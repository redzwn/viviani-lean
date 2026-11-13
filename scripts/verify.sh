#!/usr/bin/env bash
# Re-runs every check on this project and prints a transcript. Exits non-zero if any check
# fails, including any tamper test that is wrongly accepted.
#
# Requires elan. The independent-checker steps need `leanexport` and `nanoda_bin`
# (https://github.com/ammkrn/nanoda_lib); some Lean toolchains ship both.
set -u
cd "$(dirname "$0")/.."
FAIL=0
fail() { echo "FAILED: $1"; FAIL=1; }
AXIOMS='["propext", "Classical.choice", "Quot.sound"]'
LIB=.lake/build/lib/lean

echo "== 1. Versions"
lake env lean --version
echo "mathlib $(sed -n 's/^rev = "\(.*\)"/\1/p' lakefile.toml)"

echo
echo "== 2. Build (the Lean kernel checks every proof); warnings count as failures"
lake build Viviani 2>&1 | tee /tmp/viviani-build.log | grep -E "warning|error|Build completed"
grep -q "Build completed successfully" /tmp/viviani-build.log || fail "build"
grep -qE "warning|error" /tmp/viviani-build.log && fail "build produced warnings or errors"

echo
echo "== 3. No sorry, no axiom, no native_decide in the sources"
if grep -nE "\bsorry\b|^axiom |native_decide|implemented_by|unsafe " Viviani.lean Viviani/*.lean; then
  fail "forbidden token in sources"; else echo "none"; fi

echo
echo "== 4. Axiom audit of every declaration in the project"
lake env lean scripts/Audit.lean 2>&1 | tee /tmp/viviani-audit.log
grep -q "^audit: [1-9][0-9]* declarations" /tmp/viviani-audit.log || fail "axiom audit"
grep -q "error" /tmp/viviani-audit.log && fail "axiom audit reported an error"

echo
echo "== 5. Statements are the ones on record (scripts/statements.expected)"
if lake env lean scripts/Statements.lean 2>&1 | diff - scripts/statements.expected >/dev/null; then
  echo "identical ($(grep -c '^@' scripts/statements.expected) statements)"
else fail "a statement differs from scripts/statements.expected"; fi

echo
echo "== 6. leanchecker: replay every module of the project in a fresh kernel"
if lake env which leanchecker >/dev/null 2>&1; then
  for m in Viviani.Simplex Viviani.Triangle Viviani.Regular Viviani.Tetrahedron \
           Viviani.Classical Viviani.Examples; do
    if lake env leanchecker "$m" >/dev/null 2>&1; then echo "ok  $m"; else fail "leanchecker $m"; fi
  done
else echo "skipped: leanchecker not found"; fi

NANODA=$(lake env which nanoda_bin 2>/dev/null || ls ~/.elan/toolchains/*/bin/nanoda_bin 2>/dev/null | tail -1)
if [ -n "${NANODA:-}" ] && lake env which leanexport >/dev/null 2>&1; then
  TMP=$(mktemp -d)
  # run_nanoda NAME MODULE DECL... : export the declarations with everything they depend on,
  # then type-check the export with nanoda, allowing only the three standard axioms.
  run_nanoda() {
    local name=$1 mod=$2; shift 2
    lake env leanexport "$mod" -- "$@" > "$TMP/$name.export" 2>/dev/null
    if [ ! -s "$TMP/$name.export" ]; then echo "export of $name is empty"; return 2; fi
    printf '{"export_file_path": "%s", "permitted_axioms": %s, "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "print_success_message": true, "num_threads": 2}\n' \
      "$TMP/$name.export" "$AXIOMS" > "$TMP/$name.json"
    "$NANODA" "$TMP/$name.json" 2>&1
  }

  echo
  echo "== 7. nanoda: an independent type checker (written in Rust) re-checks the main theorems"
  echo "      and everything they depend on, down to the axioms"
  OUT=$(run_nanoda viviani Viviani \
    Viviani.viviani Viviani.viviani_segment Viviani.viviani_iff \
    Viviani.sum_infDist_eq_of_affineIndependent Viviani.sum_infDist_facetSpan_const_iff_volume \
    Viviani.sum_signedInfDist_eq_of_height_eq Viviani.sum_infDist_facetSpan_mul_volume \
    Viviani.viviani_simplex Viviani.viviani_tetrahedron Viviani.viviani_disphenoid \
    Viviani.Examples.sum_eq_sqrt_three); RC=$?
  echo "$OUT"
  { [ $RC -eq 0 ] && echo "$OUT" | grep -qE "Checked [1-9][0-9]* declarations with no typechecker errors"; } \
    || fail "nanoda"

  echo
  echo "== 8. Tamper tests: each planted defect must be rejected"
  mkdir -p "$LIB/Tamper"
  tamper() {  # tamper NAME DECL EXPECTED-MESSAGE <<< source
    local name=$1 decl=$2 expect=$3
    cat > "Tamper$name.lean"
    lake env lean "Tamper$name.lean" -o "$LIB/Tamper$name.olean" >/dev/null 2>&1
    OUT=$(run_nanoda "tamper$name" "Tamper$name" "$decl"); RC=$?
    rm -f "Tamper$name.lean" "$LIB/Tamper$name.olean"
    if [ $RC -ne 0 ] && echo "$OUT" | grep -q "$expect"; then
      echo "rejected  $name: $(echo "$OUT" | grep -o "$expect.*" | head -1)"
    else echo "$OUT" | tail -3; fail "tamper test $name was not rejected as expected"; fi
  }
  tamper Sorry bad 'unpermitted axiom' <<'X'
theorem bad : 1 + 1 = 3 := by sorry
X
  tamper Axiom bad 'unpermitted axiom' <<'X'
axiom convenient : ∀ x : Nat, x = 0
theorem bad : 1 + 1 = 0 := convenient _
X
  tamper NativeDecide bad 'unpermitted axiom' <<'X'
theorem bad : 2 ^ 10 = 1024 := by native_decide
X
  # A weakened statement must be caught by the comparison in step 5.
  sed 's/#check @viviani$/#check @viviani_segment/' scripts/Statements.lean > TamperStatements.lean
  if lake env lean TamperStatements.lean 2>&1 | diff - scripts/statements.expected >/dev/null; then
    fail "tamper test Statement was not detected"
  else echo "rejected  Statement: a swapped statement no longer matches scripts/statements.expected"; fi
  rm -f TamperStatements.lean
  rm -rf "$TMP"
else
  echo; echo "== 7-8 skipped: leanexport or nanoda_bin not found"
fi

echo
echo "== 9. SHA-256 of the sources"
sha256sum Viviani.lean Viviani/*.lean lakefile.toml lake-manifest.json lean-toolchain

echo
if [ $FAIL -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAIL
