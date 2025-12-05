#!/usr/bin/env python3

# SPDX-License-Identifier: AGPL-3.0-or-later
# This file is part of zk-lisp project.
# Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
#
# Additional terms under GNU AGPL v3 section 7:
#   You must preserve this notice and the zk-lisp
#   attribution in copies of this file or substantial
#   portions of it. See the NOTICE file for details.

import ast
import re
import textwrap

from math import gcd
from pathlib import Path

NR = 8
POSEIDON_ROUNDS = 27
SPONGE_IDX_BITS = 3

def find_panic_block(text: str):
    # Take the last panic about degrees
    # (in case there are multiple of them).
    panics = list(
        re.finditer(
            r"transition constraint degrees didn't match.*?expected:\s*\[(.*?)\]\s*actual:\s*\[(.*?)\]",
            text,
            re.S,
        )
    )
    if not panics:
        raise SystemExit("no `transition constraint degrees didn't match` found")

    m = panics[-1]
    exp_str = "[" + m.group(1).strip() + "]"
    act_str = "[" + m.group(2).strip() + "]"
    exp = ast.literal_eval(exp_str)
    act = ast.literal_eval(act_str)
    panic_pos = m.start()

    return exp, act, panic_pos

def find_deg_ranges_for_panic(text: str, panic_pos: int):
    # Find the last deg_ranges: [...] block before the panic
    last = None

    for m in re.finditer(r"deg_ranges:\s*(\[[^\]]*\])", text, re.S):
        if m.start() < panic_pos:
            last = m
        else:
            break

    if not last:
        return []

    ranges_str = last.group(1)
    ranges = ast.literal_eval(ranges_str)

    return ranges

def infer_base_mapping(exp):
    vals = sorted({v for v in exp if v > 0})

    if not vals:
        def base_from_eval(_: int):
            return None
        return 0, 0, base_from_eval, False

    step = 0

    for i in range(1, len(vals)):
        d = vals[i] - vals[i - 1]

        if d <= 0:
            continue

        step = d if step == 0 else gcd(step, d)

    if step == 0:
        min_val = vals[0]

        def base_from_eval(_: int):
            return None

        return min_val, 0, base_from_eval, False

    min_val = vals[0]

    def base_from_eval(v: int):
        if v < min_val:
            return None

        num = v - min_val

        if num % step != 0:
            return None

        return 1 + num // step

    ok_count = sum(1 for v in vals if base_from_eval(v) is not None)
    ok = ok_count >= int(0.95 * len(vals))

    return min_val, step, base_from_eval, ok

def analyze(path: Path):
    text = path.read_text()
    exp, act, panic_pos = find_panic_block(text)

    if len(exp) != len(act):
        raise SystemExit(f"len mismatch: expected={len(exp)} actual={len(act)}")

    deg_ranges = find_deg_ranges_for_panic(text, panic_pos)

    if not deg_ranges:
        raise SystemExit(
            "no deg_ranges found before panic; "
            "make sure vm::air::debug logging is enabled"
        )

    min_val, step, base_from_eval, base_ok = infer_base_mapping(exp)
    mismatches = [(i, exp[i], act[i]) for i in range(len(exp)) if exp[i] != act[i]]
    max_end = max(end for _, _, end in deg_ranges)

    if max_end != len(exp):
        print(
            "WARNING: deg_ranges coverage does not match expected length:",
            "max_end=", max_end,
            "len(exp)=", len(exp),
        )

    module_map = []

    for idx, ev, av in mismatches:
        mod_name = None
        local = None

        for name, start, end in deg_ranges:
            if start <= idx < end:
                mod_name = name
                local = idx - start
                break

        module_map.append((idx, ev, av, mod_name, local))

    vm_ctrl_start = None
    vm_ctrl_end = None

    for name, start, end in deg_ranges:
        if name == "vm_ctrl":
            if vm_ctrl_start is None:
                vm_ctrl_start = start
                vm_ctrl_end = end
            else:
                raise SystemExit(
                    "multiple vm_ctrl ranges in deg_ranges; "
                    "script assumes a single contiguous vm_ctrl block"
                )

    vm_ctrl_layout = None

    if vm_ctrl_start is not None and vm_ctrl_end is not None:
        len_ctrl = vm_ctrl_end - vm_ctrl_start
        len_roles = 5 * NR + 5 + NR
        len_tail = 1 + 17 + 1 + 17 + 2
        sponge_extra = len_ctrl - len_roles - len_tail

        if sponge_extra < 0:
            raise SystemExit(
                f"vm_ctrl layout mismatch: len_ctrl={len_ctrl}, "
                f"len_roles={len_roles}, len_tail={len_tail}, "
                f"sponge_extra={sponge_extra}"
            )

        if sponge_extra % (SPONGE_IDX_BITS + 1) != 0:
            raise SystemExit(
                f"vm_ctrl sponge selector region size {sponge_extra} "
                f"is not divisible by SPONGE_IDX_BITS+1={SPONGE_IDX_BITS + 1}"
            )

        num_lanes = sponge_extra // (SPONGE_IDX_BITS + 1)
        vm_ctrl_layout = {
            "len_ctrl": len_ctrl,
            "len_roles": len_roles,
            "len_tail": len_tail,
            "sponge_extra": sponge_extra,
            "num_lanes": num_lanes,
        }

    poseidon_bind = []
    ctrl_sponge = []
    ctrl_core = []
    alu_high = []
    ram_mism = []
    rom_mism = []
    other = []

    for idx, ev, av, mod, local in module_map:
        b_exp = base_from_eval(ev)
        b_act = base_from_eval(av)
        rec = {
            "idx": idx,
            "expected": ev,
            "actual": av,
            "base_expected": b_exp,
            "base_actual": b_act,
            "module": mod,
            "local": local,
        }

        if mod == "poseidon" and local is not None:
            # base poseidon len: 12*R + 12
            base_len = 12 * POSEIDON_ROUNDS + 12
            if local >= base_len:
                lane = local - base_len
                rec["lane"] = lane
                poseidon_bind.append(rec)
            else:
                other.append(rec)
            continue

        if mod == "vm_ctrl" and local is not None and vm_ctrl_layout is not None:
            len_roles = vm_ctrl_layout["len_roles"]
            sponge_extra = vm_ctrl_layout["sponge_extra"]

            if local < len_roles:
                ctrl_core.append(rec)
            elif local < len_roles + sponge_extra:
                # Here we actually have sponge selectors
                rel = local - len_roles
                lane = rel // (SPONGE_IDX_BITS + 1)
                pos = rel % (SPONGE_IDX_BITS + 1)
                kind = f"bit{pos}" if pos < SPONGE_IDX_BITS else "active"
                rec["lane"] = lane
                rec["kind"] = kind

                ctrl_sponge.append(rec)
            else:
                ctrl_core.append(rec)
            continue

        if mod == "vm_alu" and local is not None:
            alu_high.append(rec)
            continue

        if mod == "ram":
            ram_mism.append(rec)
            continue

        if mod == "rom":
            rom_mism.append(rec)
            continue

        other.append(rec)

    print(f"path={path}")
    print("len(exp)         =", len(exp))
    print("total mismatches =", len(mismatches))
    print("deg_ranges       =", deg_ranges)
    print("min_val=", min_val, "step=", step, "base_ok=", base_ok)

    if not base_ok:
        print(
            "WARNING: base degree mapping is unreliable; "
            "base_* fields may be None or misleading"
        )

    print("\nPoseidon sponge binding mismatches:")

    for r in poseidon_bind:
        print(
            f"  idx={r['idx']}, lane={r['lane']}, "
            f"exp={r['expected']} (base={r['base_expected']}), "
            f"act={r['actual']} (base={r['base_actual']})"
        )

    print("\nVmCtrl sponge-selector mismatches:")

    for r in ctrl_sponge:
        print(
            f"  idx={r['idx']}, lane={r['lane']}, {r['kind']}, "
            f"exp={r['expected']} (base={r['base_expected']}), "
            f"act={r['actual']} (base={r['base_actual']})"
        )

    print("\nVmCtrl core (roles/sums/op/rom/pc) mismatches:")

    for r in ctrl_core:
        print(
            f"  idx={r['idx']}, local={r['local']}, "
            f"exp={r['expected']} (base={r['base_expected']}), "
            f"act={r['actual']} (base={r['base_actual']})"
        )

    print("\nVmAlu high-degree mismatches:")

    for r in alu_high:
        print(
            f"  idx={r['idx']}, local={r['local']}, "
            f"exp={r['expected']} (base={r['base_expected']}), "
            f"act={r['actual']} (base={r['base_actual']})"
        )

    print("\nRAM mismatches:")

    for r in ram_mism:
        print(textwrap.shorten(str(r), width=160))

    print("\nROM mismatches:")

    for r in rom_mism:
        print(textwrap.shorten(str(r), width=160))

    print("\nOther mismatches:")

    for r in other[:80]:
        print(textwrap.shorten(str(r), width=160))

    print("\nSummary:")
    print("  poseidon_bind mismatches :", len(poseidon_bind))
    print("  vm_ctrl sponge mismatches:", len(ctrl_sponge))
    print("  vm_ctrl core mismatches  :", len(ctrl_core))
    print("  vm_alu high-degree       :", len(alu_high))
    print("  ram mismatches           :", len(ram_mism))
    print("  rom mismatches           :", len(rom_mism))
    print("  other                    :", len(other))

if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        raise SystemExit(f"Usage: {sys.argv[0]} <path-to-debug-log>")

    LOG_PATH = Path(sys.argv[1])
    analyze(LOG_PATH)
