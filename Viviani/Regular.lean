/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Viviani.Simplex

/-!
# Equilateral simplices in every dimension

In a simplex of dimension `n ≥ 1` all of whose edges have length `r`, every height equals
`√((n + 1) / (2 n)) * r`: `√3 / 2 * r` for a triangle, `√(2 / 3) * r` for a tetrahedron.

* `height_sq_of_dist_eq`, `height_of_dist_eq`: the height.
* `viviani_simplex`: the distances from a point of the closed simplex to the `n + 1` facets add
  up to `√((n + 1) / (2 n)) * r`.
* `viviani_simplex_signed`: the same for signed distances, at every point of the affine span.

The proof of the height formula does not locate the foot of the altitude. It writes the foot
as an affine combination of the other vertices with unknown weights, and Mathlib's identity
`⟪pᵢ - pⱼ, pᵢ - foot⟫ = height²` then forces all the weights to be equal.
-/

public section

open EuclideanGeometry Metric Affine Finset
open scoped RealInnerProductSpace

namespace Viviani

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ}

/-- Inner products of edge vectors at a vertex of a simplex whose edges all have length `r`. -/
theorem inner_vsub_vsub_of_dist_eq {s : Simplex ℝ P n} {r : ℝ}
    (hr : ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r) {i j k : Fin (n + 1)}
    (hij : i ≠ j) (hik : i ≠ k) :
    ⟪s.points i -ᵥ s.points j, s.points i -ᵥ s.points k⟫ =
      if k = j then r ^ 2 else r ^ 2 / 2 := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    vsub_sub_vsub_cancel_left, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub,
    hr _ _ hij, hr _ _ hik]
  split_ifs with h
  · subst h
    simp
    ring
  · rw [hr _ _ h]
    ring

variable [NeZero n]

/-- In a simplex of dimension `n` whose edges all have length `r`, each height squared is
`(n + 1) / (2 n) * r ^ 2`. -/
theorem height_sq_of_dist_eq {s : Simplex ℝ P n} {r : ℝ}
    (hr : ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r) (i : Fin (n + 1)) :
    s.height i ^ 2 = (n + 1) / (2 * n) * r ^ 2 := by
  have hmem : s.altitudeFoot i ∈ affineSpan ℝ (Set.range s.points) :=
    s.altitudeFoot_mem_affineSpan i
  obtain ⟨w, hw, hwf⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hmem
  have hwi : w i = 0 :=
    (Simplex.affineCombination_mem_affineSpan_faceOpposite_iff (s := s) hw).1
      (hwf ▸ s.altitudeFoot_mem_affineSpan_faceOpposite i)
  have key : ∀ j, j ≠ i → s.height i ^ 2 = r ^ 2 / 2 * (1 + w j) := by
    intro j hj
    rw [← s.inner_vsub_vsub_altitudeFoot_eq_height_sq (Ne.symm hj), hwf,
      ← sum_smul_const_vsub_eq_vsub_affineCombination _ _ _ _ hw, inner_sum]
    have hk : ∀ k, ⟪s.points i -ᵥ s.points j, w k • (s.points i -ᵥ s.points k)⟫ =
        r ^ 2 / 2 * w k + if k = j then r ^ 2 / 2 * w j else 0 := by
      intro k
      rw [inner_smul_right]
      by_cases hki : k = i
      · subst hki
        simp [hwi, Ne.symm hj]
      · rw [inner_vsub_vsub_of_dist_eq hr (Ne.symm hj) (Ne.symm hki)]
        split_ifs with h
        · subst h; ring
        · ring
    simp_rw [hk, sum_add_distrib, ← mul_sum, hw, sum_ite_eq', mem_univ, ite_true]
    ring
  have hsum : ∑ j ∈ univ.erase i, w j = 1 := by
    rw [← hw, ← add_sum_erase _ _ (mem_univ i), hwi, zero_add]
  have h2 : ∑ j ∈ univ.erase i, s.height i ^ 2 = ∑ j ∈ univ.erase i, r ^ 2 / 2 * (1 + w j) :=
    sum_congr rfl fun j hj ↦ key j (ne_of_mem_erase hj)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
    ← mul_sum, sum_add_distrib, hsum, sum_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin] at h2
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at h2
  field_simp
  linarith

/-- In a simplex of dimension `n` whose edges all have length `r`, each height is
`√((n + 1) / (2 n)) * r`. -/
theorem height_of_dist_eq {s : Simplex ℝ P n} {r : ℝ}
    (hr : ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r) (i : Fin (n + 1)) :
    s.height i = Real.sqrt ((n + 1) / (2 * n)) * r := by
  have hr0 : 0 ≤ r := by
    have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by have := NeZero.pos n; omega)
    obtain ⟨j, hj⟩ := exists_ne i
    rw [← hr j i hj]
    exact dist_nonneg
  rw [← Real.sqrt_sq (s.height_pos i).le, height_sq_of_dist_eq hr i,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hr0]

/-- **Viviani's theorem in every dimension.** In a simplex of dimension `n` whose edges all
have length `r`, the distances from any point of the closed simplex to the `n + 1` facets add up
to `√((n + 1) / (2 n)) * r`. -/
theorem viviani_simplex {s : Simplex ℝ P n} {r : ℝ}
    (hr : ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r) {p : P}
    (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) = Real.sqrt ((n + 1) / (2 * n)) * r :=
  sum_infDist_facetSpan_eq_of_height_eq (height_of_dist_eq hr) hp

/-- The signed form of `viviani_simplex`, valid at every point of the affine span. -/
theorem viviani_simplex_signed {s : Simplex ℝ P n} {r : ℝ}
    (hr : ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    ∑ i, s.signedInfDist i p = Real.sqrt ((n + 1) / (2 * n)) * r :=
  sum_signedInfDist_eq_of_height_eq (height_of_dist_eq hr) hp

end Viviani
