// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::sync::Once;

static INIT: Once = Once::new();

pub fn init_with_level(level: Option<&str>) {
    INIT.call_once(|| {
        if tracing::dispatcher::has_been_set() {
            return;
        }

        let env = match level {
            Some(l) if !l.is_empty() => l.to_string(),
            _ => std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string()),
        };

        let filter = tracing_subscriber::EnvFilter::try_new(env.clone()).unwrap_or_else(|e| {
            eprintln!("WARN: invalid RUST_LOG/log_level '{env}': {e}; falling back to 'info'");
            tracing_subscriber::EnvFilter::new("info")
        });

        let _ = tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_target(true)
            .with_thread_ids(false)
            .with_thread_names(false)
            .compact()
            .try_init();
    });
}
