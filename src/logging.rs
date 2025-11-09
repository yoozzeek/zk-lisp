// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::sync::Once;

static INIT: Once = Once::new();

pub fn init() {
    INIT.call_once(|| {
        if tracing::dispatcher::has_been_set() {
            return;
        }

        let env = std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string());
        let filter = tracing_subscriber::EnvFilter::new(env);

        tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_target(true)
            .with_thread_ids(false)
            .with_thread_names(false)
            .compact()
            .init();
    });
}
