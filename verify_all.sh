#!/usr/bin/env bash
# verify_all.sh - chained re-verification for the consolidated
# kp+1 palindrome record (11 OEIS entries, 53 Lean modules).
#
#   1. integrity: sha256sum -c MANIFEST.sha256 (must pass 100%)
#   2. source surface: scan_p0.py on every shipped .lean
#      (rejects sorry/admit/axiom/native_decide/bv_decide/unsafe)
#   3. reminder of the kernel build (requires the Lean toolchain
#      leanprover/lean4:v4.35.0 + mathlib v4.35.0)
#
# Usage: bash verify_all.sh   (from this directory)

set -u
cd "$(dirname "$0")"
rc=0

echo "== 1/3 MANIFEST integrity =="
if sha256sum -c MANIFEST.sha256; then
    echo "MANIFEST: all hashes OK"
else
    echo "MANIFEST: FAIL"
    rc=1
fi

echo
echo "== 2/3 P0 source scan (forbidden constructs) =="
if python scan_p0.py ./*.lean; then
    echo "scan_p0: OK"
else
    echo "scan_p0: FAIL"
    rc=1
fi

echo
echo "== 3/3 kernel build reminder =="
echo "With elan + toolchain leanprover/lean4:v4.35.0 installed:"
echo "  lake exe cache get && lake build"
echo "(all 53 modules are defaultTargets; axiom audits:"
echo " lake env lean AxiomsReport_<A######>.lean)"

exit $rc
