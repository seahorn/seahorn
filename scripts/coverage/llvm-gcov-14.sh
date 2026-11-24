#!/bin/bash
# SPDX-FileCopyrightText: 2026 The SeaHorn Authors
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

exec llvm-cov-14 gcov "$@"
