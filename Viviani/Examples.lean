/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Viviani.Classical

/-!
# Sanity checks

The hypotheses of the theorems are satisfied by a genuine triangle, and the theorems say what
they should on it. In the plane `EuclideanSpace ℝ (Fin 2)` take

  `A₀ = (0, 0)`, `B₀ = (2, 0)`, `C₀ = (1, √3)`,

an equilateral triangle of side `2`. Viviani's theorem then says that the three distances from
any point of the triangle add up to `√3`.
-/

public section

open Metric

namespace Viviani.Examples

/-- The point `(0, 0)`. -/
noncomputable def A₀ : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]

/-- The point `(2, 0)`. -/
noncomputable def B₀ : EuclideanSpace ℝ (Fin 2) := !₂[2, 0]

/-- The point `(1, √3)`. -/
noncomputable def C₀ : EuclideanSpace ℝ (Fin 2) := !₂[1, Real.sqrt 3]

private lemma sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_A₀_B₀ : dist A₀ B₀ = 2 := by
  rw [EuclideanSpace.dist_eq]
  simp [A₀, B₀, Fin.sum_univ_two, Real.dist_eq]

theorem dist_B₀_C₀ : dist B₀ C₀ = 2 := by
  rw [EuclideanSpace.dist_eq]
  simp [B₀, C₀, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num [sqrt_four]

theorem dist_C₀_A₀ : dist C₀ A₀ = 2 := by
  rw [EuclideanSpace.dist_eq]
  simp [C₀, A₀, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num [sqrt_four]

/-- The three points form a genuine triangle. -/
theorem affineIndependent : AffineIndependent ℝ ![A₀, B₀, C₀] :=
  affineIndependent_of_dist_eq (dist_A₀_B₀.trans dist_B₀_C₀.symm)
    (dist_C₀_A₀.trans dist_B₀_C₀.symm) (by rw [← dist_pos, dist_A₀_B₀]; norm_num)

/-- Viviani's theorem on the concrete triangle: the three distances add up to `√3`. -/
theorem sum_eq_sqrt_three {P : EuclideanSpace ℝ (Fin 2)} (hP : P ∈ convexHull ℝ {A₀, B₀, C₀}) :
    infDist P (segment ℝ B₀ C₀) + infDist P (segment ℝ C₀ A₀) + infDist P (segment ℝ A₀ B₀) =
      Real.sqrt 3 := by
  rw [viviani_segment (dist_A₀_B₀.trans dist_B₀_C₀.symm) (dist_C₀_A₀.trans dist_B₀_C₀.symm) hP,
    dist_B₀_C₀]
  ring

end Viviani.Examples
