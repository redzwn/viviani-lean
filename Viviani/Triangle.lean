/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Viviani.Simplex

/-!
# Triangles: Viviani's theorem and its converse

For a triangle `t` in a Euclidean affine space:

* `equilateral_iff_height_eq`: `t` is equilateral if and only if its three heights are equal
  (because height times opposite side is twice the area).
* `viviani_triangle`: in an equilateral triangle the distances from a point of the closed
  triangle to the three side lines add up to `√3 / 2` times the side.
* `sum_infDist_const_iff_equilateral`: the distance sum is constant on the closed triangle
  **if and only if** the triangle is equilateral.

Readers who prefer plain points `A B C` to `Affine.Triangle` should look at
`Viviani/Classical.lean`.
-/

public section

open EuclideanGeometry Metric Affine Finset

namespace Viviani

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Height times the opposite side is twice the area. -/
theorem height_mul_dist (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) : t.height i₁ * dist (t.points i₂) (t.points i₃) = 2 * t.volume := by
  rw [t.volume_eq_height_mul h₁₂ h₁₃ h₂₃]
  ring

/-- A triangle is equilateral if and only if its three heights are equal. -/
theorem equilateral_iff_height_eq (t : Triangle ℝ P) :
    t.Equilateral ↔ ∀ i j, t.height i = t.height j := by
  have h0 := height_mul_dist t (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
  have h1 := height_mul_dist t (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have h2 := height_mul_dist t (i₁ := 2) (i₂ := 0) (i₃ := 1) (by decide) (by decide) (by decide)
  have p0 := t.height_pos 0
  rw [Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12]
  constructor
  · rintro ⟨e1, e2⟩
    rw [← e2] at h0
    rw [← e1] at h1
    have d : 0 < dist (t.points 0) (t.points 1) :=
      dist_pos.2 (t.independent.injective.ne (by decide))
    have a : t.height 0 = t.height 1 := mul_right_cancel₀ d.ne' (h0.trans h1.symm)
    have b : t.height 0 = t.height 2 := mul_right_cancel₀ d.ne' (h0.trans h2.symm)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [← a, ← b]
  · intro h
    rw [h 1 0] at h1
    rw [h 2 0] at h2
    exact ⟨mul_left_cancel₀ p0.ne' (h2.trans h1.symm), mul_left_cancel₀ p0.ne' (h2.trans h0.symm)⟩

/-- Every height of an equilateral triangle is `√3 / 2` times the side. -/
theorem height_eq_of_equilateral {t : Triangle ℝ P} (ht : t.Equilateral) (i : Fin 3) :
    t.height i = Real.sqrt 3 / 2 * dist (t.points 0) (t.points 1) := by
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases i <;> decide
  rw [t.height_eq_sin_mul_dist hij hik hjk, ht.angle_eq_pi_div_three hij hik hjk,
    Real.sin_pi_div_three, ht.dist_eq hij (show (0 : Fin 3) ≠ 1 by decide)]

/-- **Viviani's theorem** for an `Affine.Triangle`: in an equilateral triangle, the distances
from any point of the closed triangle to the three side lines add up to `√3 / 2` times the side. -/
theorem viviani_triangle {t : Triangle ℝ P} (ht : t.Equilateral) {p : P}
    (hp : p ∈ t.closedInterior) :
    ∑ i, infDist p (facetSpan t i) = Real.sqrt 3 / 2 * dist (t.points 0) (t.points 1) :=
  sum_infDist_facetSpan_eq_of_height_eq (height_eq_of_equilateral ht) hp

/-- **Viviani's theorem with its converse.** The sum of the distances to the three side lines
is the same at every point of a closed triangle if and only if the triangle is equilateral. -/
theorem sum_infDist_const_iff_equilateral (t : Triangle ℝ P) :
    (∃ c : ℝ, ∀ p ∈ t.closedInterior, ∑ i, infDist p (facetSpan t i) = c) ↔ t.Equilateral := by
  rw [sum_infDist_facetSpan_const_iff, equilateral_iff_height_eq]

end Viviani
