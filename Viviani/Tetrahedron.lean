/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Viviani.Regular

/-!
# Tetrahedra

* `viviani_tetrahedron`: in a regular tetrahedron of edge `r`, the distances from a point of the
  closed tetrahedron to the four face planes add up to `√(2 / 3) * r`.
* `viviani_disphenoid`: regularity is not needed. If opposite edges are equal in pairs (a
  *disphenoid*; its four faces are congruent triangles) the distance sum is still constant.
  The proof is Heron's formula: the four faces have the same side lengths, hence the same area,
  hence (by `height_eq_iff_volume_faceOpposite_eq`) the four heights are equal.

So in three dimensions the converse of Viviani's theorem does not single out the regular
tetrahedron: by `sum_infDist_facetSpan_const_iff_volume` the distance sum is constant exactly
when the four faces have equal area.
-/

public section

open EuclideanGeometry Metric Affine Finset

namespace Viviani

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

set_option linter.unusedSimpArgs false in -- each of the four cases uses a different subset
/-- All four faces of a disphenoid have the same area (by Heron's formula). -/
theorem volume_faceOpposite_sq_of_disphenoid (s : Simplex ℝ P 3)
    (h₁ : dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3))
    (h₂ : dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3))
    (h₃ : dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2)) (i : Fin 4) :
    (s.faceOpposite i).volume ^ 2 = (s.faceOpposite 3).volume ^ 2 := by
  have H : ∀ t : Triangle ℝ P, t.volume ^ 2 = _ :=
    fun t ↦ t.volume_sq_eq_mul_sub_mul_sub_mul_sub (i₁ := 0) (i₂ := 1) (i₃ := 2)
      (by decide) (by decide) (by decide)
  rw [H (s.faceOpposite i), H (s.faceOpposite 3)]
  simp only [Simplex.faceOpposite_point_eq_point_succAbove]
  have c₁ : dist (s.points 1) (s.points 0) = dist (s.points 2) (s.points 3) := by
    rw [dist_comm, h₁]
  have c₂ : dist (s.points 2) (s.points 0) = dist (s.points 1) (s.points 3) := by
    rw [dist_comm, h₂]
  have c₃ : dist (s.points 3) (s.points 0) = dist (s.points 1) (s.points 2) := by
    rw [dist_comm, h₃]
  have c₄ : dist (s.points 2) (s.points 1) = dist (s.points 1) (s.points 2) := dist_comm _ _
  have c₅ : dist (s.points 3) (s.points 1) = dist (s.points 1) (s.points 3) := dist_comm _ _
  have c₆ : dist (s.points 3) (s.points 2) = dist (s.points 2) (s.points 3) := dist_comm _ _
  fin_cases i <;> simp [Fin.succAbove, h₁, h₂, h₃, c₁, c₂, c₃, c₄, c₅, c₆] <;> ring


/-- The four heights of a disphenoid are equal. -/
theorem height_eq_of_disphenoid (s : Simplex ℝ P 3)
    (h₁ : dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3))
    (h₂ : dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3))
    (h₃ : dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2)) (i j : Fin 4) :
    s.height i = s.height j := by
  rw [height_eq_iff_volume_faceOpposite_eq]
  have hi := volume_faceOpposite_sq_of_disphenoid s h₁ h₂ h₃ i
  have hj := volume_faceOpposite_sq_of_disphenoid s h₁ h₂ h₃ j
  exact (pow_left_inj₀ (s.faceOpposite i).volume_pos.le (s.faceOpposite j).volume_pos.le
    two_ne_zero).1 (hi.trans hj.symm)

/-- **Viviani's theorem for a disphenoid.** If the opposite edges of a tetrahedron are equal in
pairs, the distances from any point of the closed tetrahedron to the four face planes add up to
the height. -/
theorem viviani_disphenoid (s : Simplex ℝ P 3)
    (h₁ : dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3))
    (h₂ : dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3))
    (h₃ : dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2)) {p : P}
    (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) = s.height 0 :=
  sum_infDist_facetSpan_eq_of_height_eq (fun i ↦ height_eq_of_disphenoid s h₁ h₂ h₃ i 0) hp

/-- **Viviani's theorem for the regular tetrahedron.** The distances from any point of a closed
regular tetrahedron of edge `r` to the four face planes add up to `√(2 / 3) * r`. -/
theorem viviani_tetrahedron {s : Simplex ℝ P 3} {r : ℝ}
    (hr : ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r) {p : P}
    (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) = Real.sqrt (2 / 3) * r := by
  rw [viviani_simplex hr hp]
  norm_num

end Viviani
