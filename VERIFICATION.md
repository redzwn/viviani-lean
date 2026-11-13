# Verification record

- Lean 4.36.0-rc2 (commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`)
- Mathlib `7bcc5e95ffc0d80d94adc6f17715f224d59d209b`
- Checkers: `leanchecker`, `leanexport` and `nanoda_bin` as shipped with that toolchain
- Date: 13 November 2026

## What each check establishes

1. **Build.** `lake build` elaborates every file; Lean’s kernel checks every proof term. The script fails on any warning.
2. **Source scan.** No `sorry`, `axiom`, `native_decide`, `implemented_by` or `unsafe` in the sources.
3. **Axiom audit** ([`scripts/Audit.lean`](scripts/Audit.lean)). Every declaration defined in a `Viviani.*` module, including compiler-generated auxiliaries, depends only on `propext`, `Classical.choice`, `Quot.sound`. The audit fails if it finds no declarations.
4. **Statement fingerprints** ([`scripts/Statements.lean`](scripts/Statements.lean)). The 22 main statements, as printed by `#check`, match [`scripts/statements.expected`](scripts/statements.expected). A weakened or altered statement fails this step.
5. **leanchecker.** Each module is replayed through the kernel from its stored proof terms.
6. **nanoda.** The main theorems and everything they depend on are exported with `leanexport` and type-checked by nanoda, a separate implementation in Rust, with only the three standard axioms permitted. The script fails if the export is empty or no declarations were checked.
7. **Tamper tests.** The same nanoda configuration must reject a proof using `sorry`, a proof using a new axiom, and a proof using `native_decide`; the fingerprint check must reject a swapped statement.

nanoda’s line “1 pretty printer errors: Unable to print axioms” concerns printing the axioms at the end of a run. It is not a type-checking error; the count of those is zero.

## What is not established

The three axioms, the correctness of Lean’s kernel and of nanoda, and the faithfulness of the formal statements to their informal readings are trusted. `leanchecker --fresh` (re-checking all of Mathlib) was not run. No human referee has reviewed the development.

## Transcript of `scripts/verify.sh`

```
== 1. Versions
Lean (version 4.36.0-rc2, x86_64-unknown-linux-gnu, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, Release)
mathlib 7bcc5e95ffc0d80d94adc6f17715f224d59d209b

== 2. Build (the Lean kernel checks every proof); warnings count as failures
Build completed successfully (18252 jobs).

== 3. No sorry, no axiom, no native_decide in the sources
none

== 4. Axiom audit of every declaration in the project
audit: 85 declarations (81 theorems) in the Viviani modules; every one depends only on axioms among [propext, Classical.choice, Quot.sound]
'Viviani.viviani' depends on axioms: [propext, Classical.choice, Quot.sound]
'Viviani.viviani_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
'Viviani.viviani_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Viviani.sum_infDist_eq_of_affineIndependent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Viviani.sum_infDist_facetSpan_const_iff_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'Viviani.viviani_simplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Viviani.viviani_disphenoid' depends on axioms: [propext, Classical.choice, Quot.sound]

== 5. Statements are the ones on record (scripts/statements.expected)
identical (22 statements)

== 6. leanchecker: replay every module of the project in a fresh kernel
ok  Viviani.Simplex
ok  Viviani.Triangle
ok  Viviani.Regular
ok  Viviani.Tetrahedron
ok  Viviani.Classical
ok  Viviani.Examples

== 7. nanoda: an independent type checker (written in Rust) re-checks the main theorems
      and everything they depend on, down to the axioms
Checked 48926 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]

== 8. Tamper tests: each planted defect must be rejected
rejected  Sorry: unpermitted axiom "sorryAx"
rejected  Axiom: unpermitted axiom "convenient"
rejected  NativeDecide: unpermitted axiom "bad._native.native_decide.ax_1_1"
rejected  Statement: a swapped statement no longer matches scripts/statements.expected

== 9. SHA-256 of the sources
8d3c5c5c21a5d29f021eda2aeacdf5b087471cb7eb917bf4aeaca04819e3ca76  Viviani.lean
839274d92ecaef5603f923718e0067361ba8bafd8093e86432596044f541dcc0  Viviani/Classical.lean
fd801abdcd57b22cc5d62c47796c31c8f3175b089b7ccf1b23a6240677d2a0db  Viviani/Examples.lean
7ec0b75d97d13054389128f7a31e2fbaf85cfb24aa4cf2b8945c5019dfefda79  Viviani/Regular.lean
e65fa22f838b02ff3ead1916f89d476c423ea23da79abc460fa11d90e779ab10  Viviani/Simplex.lean
af88584e6020ca5d64c454466737e8d62fd009cb6776dc8b1949d150bf7940a9  Viviani/Tetrahedron.lean
54b32367cd9efa717de663ad71c6da9f9c364bc8d57498528489fbfa72136a88  Viviani/Triangle.lean
1b0e320aacfb6e4d7c3364280fe758f7e3a49d3506735cfd57f883fac1576701  lakefile.toml
fbc69eb9d6e8aa76067e87309793e962e664e83650bd65a26f0880e0cb073dc9  lake-manifest.json
11c697aebe5b539d74f5069e497a588e7dfab1c4eeb74313f28357e351c55ca3  lean-toolchain

ALL CHECKS PASSED
```
