#!/usr/bin/env bash
# Validate `Paper node:` annotations for the Critch PBL formalization.
#
# Adapted from the logical-induction branch's check-paper-nodes.sh. Critch 2019 is a
# PDF source with no \label{}s, so the TeX label sweep is replaced by §-citation
# validation against the section map recorded in scripts/check_endpoint_coverage.py,
# which also carries the inventory-coverage checks in both directions:
#   1. every §-citation on a `Paper node:` line is a real section of the paper;
#   2. every declaration named in AxiomAudit.lean carries a `Paper node:` annotation;
#   3. every annotated section has an inventory endpoint (no paper material claimed
#      but off the audited trust surface).
#
# Run from repo root. Exits nonzero on any violation.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_endpoint_coverage.py
