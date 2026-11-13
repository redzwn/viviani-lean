import Viviani
open Lean Elab Command

/-- `#audit_axioms` walks over every declaration defined in a module of this project and fails
unless each one depends on no axioms other than `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut theorems := 0
  let mut bad : Array (Name × Name) := #[]
  for (c, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `Viviani do continue
    let axs ← liftCoreM (collectAxioms c)
    checked := checked + 1
    if info matches .thmInfo _ then theorems := theorems + 1
    for a in axs do
      unless allowed.contains a do bad := bad.push (c, a)
  if checked == 0 then throwError "audit: no declarations found (nothing was checked)"
  unless bad.isEmpty do
    throwError "audit: non-standard axioms used: {bad}"
  logInfo m!"audit: {checked} declarations ({theorems} theorems) in the Viviani modules; every one depends only on axioms among [propext, Classical.choice, Quot.sound]"

#audit_axioms
#print axioms Viviani.viviani
#print axioms Viviani.viviani_segment
#print axioms Viviani.viviani_iff
#print axioms Viviani.sum_infDist_eq_of_affineIndependent
#print axioms Viviani.sum_infDist_facetSpan_const_iff_volume
#print axioms Viviani.viviani_simplex
#print axioms Viviani.viviani_disphenoid
