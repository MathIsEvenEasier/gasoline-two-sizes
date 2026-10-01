#!/bin/bash
set -euo pipefail
cd /opt/a060957-job/source
export DEBIAN_FRONTEND=noninteractive
timeout 180 apt-get update -qq
timeout 180 apt-get install -y -qq git curl zstd ca-certificates build-essential pkg-config
python3 run_full.py
