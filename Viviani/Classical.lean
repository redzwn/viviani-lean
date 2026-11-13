/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Viviani.Triangle

/-!
# Viviani's theorem, as in the textbook

Statements about three points `A B C` of a real inner product space `V` (for instance the plane
`EuclideanSpace ℝ (Fin 2)`), with

* the closed triangle written `convexHull ℝ {A, B, C}`,
* the side lines written `line[ℝ, B, C]`, the sides themselves `segment ℝ B C`,
* distance from a point to a set written `Metric.infDist`.

## Main results

* `viviani`: if `dist A B = dist B C = dist C A` and `P` lies in the closed triangle, the
  distances from `P` to the three side lines add up to `√3 / 2 * dist B C`. There is no
  non-degeneracy hypothesis: if the three points coincide both sides are `0`.
* `viviani_segment`: the same with distances to the three sides (segments), which is the
  literal textbook wording.
* `viviani_iff`: for a genuine (affinely independent) triangle, the distance sum is constant on
  the closed triangle if and only if the triangle is equilateral.
* `sum_infDist_eq_of_affineIndependent`: in any triangle the distance sum at
  `a • A + b • B + c • C` is `a * h_A + b * h_B + c * h_C`.
* `infDist_eq_mul_of_affineIndependent`: the distance to side line `BC` is `a * h_A`.
* `infDist_segment_eq_infDist_line`: when the foot of the altitude from `A` lies on the side
  `BC`, distance to the side and distance to its line agree on the closed triangle.
-/

public section

open EuclideanGeometry Metric Affine Finset

namespace Viviani

section image

variable {α : Type*} (A B C : α)

/-- The vertices other than the first. -/
theorem image_compl_zero : (![A, B, C] : Fin 3 → α) '' {0}ᶜ = {B, C} := by
  ext x; simp [Fin.exists_fin_succ, eq_comm]

/-- The vertices other than the second. -/
theorem image_compl_one : (![A, B, C] : Fin 3 → α) '' {1}ᶜ = {C, A} := by
  ext x; simp [Fin.exists_fin_succ, eq_comm, or_comm]

/-- The vertices other than the third. -/
theorem image_compl_two : (![A, B, C] : Fin 3 → α) '' {2}ᶜ = {A, B} := by
  ext x; simp [Fin.exists_fin_succ, eq_comm]

/-- The set of vertices. -/
theorem range_eq : Set.range (![A, B, C] : Fin 3 → α) = {A, B, C} := by
  ext x; simp [eq_comm]; tauto

end image

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {A B C P : V}

section bridge

variable (h : AffineIndependent ℝ ![A, B, C])

/-- The facet opposite `A` spans the line `BC`. -/
theorem facetSpan_zero : facetSpan (⟨![A, B, C], h⟩ : Triangle ℝ V) 0 = line[ℝ, B, C] := by
  rw [facetSpan, image_compl_zero]

/-- The facet opposite `B` spans the line `CA`. -/
theorem facetSpan_one : facetSpan (⟨![A, B, C], h⟩ : Triangle ℝ V) 1 = line[ℝ, C, A] := by
  rw [facetSpan, image_compl_one]

/-- The facet opposite `C` spans the line `AB`. -/
theorem facetSpan_two : facetSpan (⟨![A, B, C], h⟩ : Triangle ℝ V) 2 = line[ℝ, A, B] := by
  rw [facetSpan, image_compl_two]

/-- The closed triangle is the convex hull of the three vertices. -/
theorem closedInterior_eq_convexHull :
    (⟨![A, B, C], h⟩ : Triangle ℝ V).closedInterior = convexHull ℝ {A, B, C} := by
  rw [← Simplex.convexHull_eq_closedInterior, range_eq]

/-- The sum over the three facets, written out. -/
theorem sum_facetSpan_eq (P : V) :
    ∑ i, infDist P (facetSpan (⟨![A, B, C], h⟩ : Triangle ℝ V) i) =
      infDist P line[ℝ, B, C] + infDist P line[ℝ, C, A] + infDist P line[ℝ, A, B] := by
  rw [Fin.sum_univ_three, facetSpan_zero, facetSpan_one, facetSpan_two]

end bridge

/-- Three points at equal positive distances from each other form a genuine triangle. -/
theorem affineIndependent_of_dist_eq (hAB : dist A B = dist B C) (hCA : dist C A = dist B C)
    (hne : A ≠ B) : AffineIndependent ℝ ![A, B, C] := by
  have hpos : 0 < dist A B := dist_pos.2 hne
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h <;>
  · have := h.dist_add_dist
    simp only [dist_comm] at *
    linarith


/-! ### Every triangle -/

/-- **Key lemma, for three points.** The distance from `a • A + b • B + c • C` to the line `BC`
is `a` times the distance from `A` to that line. -/
theorem infDist_eq_mul_of_affineIndependent (h : AffineIndependent ℝ ![A, B, C]) {a b c : ℝ}
    (ha : 0 ≤ a) (habc : a + b + c = 1) :
    infDist (a • A + b • B + c • C) line[ℝ, B, C] = a * infDist A line[ℝ, B, C] := by
  have hw : ∑ i, ![a, b, c] i = 1 := by simpa [Fin.sum_univ_three] using habc
  have key := infDist_facetSpan_affineCombination (⟨![A, B, C], h⟩ : Triangle ℝ V) 0 hw
  have hcomb : univ.affineCombination ℝ ![A, B, C] ![a, b, c] = a • A + b • B + c • C := by
    rw [affineCombination_eq_linear_combination _ _ _ hw]
    simp [Fin.sum_univ_three]
  rw [height_eq_infDist, facetSpan_zero] at key
  rw [← hcomb]
  simpa [abs_of_nonneg ha] using key

/-- **Viviani for every triangle.** At the point `a • A + b • B + c • C` of a closed triangle,
the distances to the three side lines add up to `a * h_A + b * h_B + c * h_C`, where `h_A` is
the distance from `A` to the line `BC` and so on: a weighted average of the three altitudes. -/
theorem sum_infDist_eq_of_affineIndependent (h : AffineIndependent ℝ ![A, B, C]) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    infDist (a • A + b • B + c • C) line[ℝ, B, C] +
      infDist (a • A + b • B + c • C) line[ℝ, C, A] +
      infDist (a • A + b • B + c • C) line[ℝ, A, B] =
    a * infDist A line[ℝ, B, C] + b * infDist B line[ℝ, C, A] + c * infDist C line[ℝ, A, B] := by
  set t : Triangle ℝ V := ⟨![A, B, C], h⟩
  have hw : ∑ i, ![a, b, c] i = 1 := by simpa [Fin.sum_univ_three] using habc
  have h0 : ∀ i, 0 ≤ ![a, b, c] i := by
    intro i; fin_cases i <;> simpa
  have key := sum_infDist_facetSpan_affineCombination t hw h0
  have hcomb : univ.affineCombination ℝ t.points ![a, b, c] = a • A + b • B + c • C := by
    rw [affineCombination_eq_linear_combination _ _ _ hw]
    simp [t, Fin.sum_univ_three]
  rw [hcomb, sum_facetSpan_eq h] at key
  rw [key, Fin.sum_univ_three, height_eq_infDist, height_eq_infDist, height_eq_infDist,
    facetSpan_zero, facetSpan_one, facetSpan_two]
  rfl

/-! ### The classical theorem -/

/-- **Viviani's theorem.** For an equilateral triangle `ABC` and any point `P` of the closed
triangle, the distances from `P` to the three side lines add up to `√3 / 2` times the side,
which is the altitude of the triangle. -/
theorem viviani (hAB : dist A B = dist B C) (hCA : dist C A = dist B C)
    (hP : P ∈ convexHull ℝ {A, B, C}) :
    infDist P line[ℝ, B, C] + infDist P line[ℝ, C, A] + infDist P line[ℝ, A, B] =
      Real.sqrt 3 / 2 * dist B C := by
  by_cases hne : A = B
  · subst hne
    have hBC : A = C := by
      rw [dist_self] at hAB
      exact dist_eq_zero.1 hAB.symm
    subst hBC
    simp only [Set.insert_eq_of_mem, Set.mem_singleton_iff, convexHull_singleton] at hP
    subst hP
    simp
  · have h := affineIndependent_of_dist_eq hAB hCA hne
    set t : Triangle ℝ V := ⟨![A, B, C], h⟩
    have ht : t.Equilateral := by
      rw [Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12]
      refine ⟨?_, hAB⟩
      change dist A B = dist A C
      rw [hAB, ← hCA, dist_comm]
    rw [← closedInterior_eq_convexHull h] at hP
    have key := viviani_triangle ht hP
    rw [sum_facetSpan_eq h] at key
    rw [key, ← hAB]
    rfl

/-- **Viviani's theorem with its converse.** For a genuine triangle `ABC`, the sum of the
distances to the three side lines is the same at every point of the closed triangle if and only
if the triangle is equilateral. -/
theorem viviani_iff (h : AffineIndependent ℝ ![A, B, C]) :
    (∃ c : ℝ, ∀ P ∈ convexHull ℝ {A, B, C},
      infDist P line[ℝ, B, C] + infDist P line[ℝ, C, A] + infDist P line[ℝ, A, B] = c) ↔
      dist A B = dist B C ∧ dist C A = dist B C := by
  have key := sum_infDist_const_iff_equilateral (⟨![A, B, C], h⟩ : Triangle ℝ V)
  simp_rw [sum_facetSpan_eq h, closedInterior_eq_convexHull h] at key
  rw [key, Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12]
  change dist A B = dist A C ∧ dist A B = dist B C ↔ _
  rw [dist_comm A C]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1 ▸ h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h2.symm, h1⟩


/-! ### Distances to the sides themselves -/

/-- A side is contained in its line. -/
theorem segment_subset_line (B C : V) : segment ℝ B C ⊆ line[ℝ, B, C] := by
  rw [← convexHull_pair]
  exact convexHull_subset_affineSpan _

/-- If the foot of the altitude from `A` lies on the side `BC`, then so does the foot of the
perpendicular from any point of the closed triangle. -/
theorem orthogonalProjection_mem_segment
    (hA : (orthogonalProjection line[ℝ, B, C] A : V) ∈ segment ℝ B C)
    (hP : P ∈ convexHull ℝ {A, B, C}) :
    (orthogonalProjection line[ℝ, B, C] P : V) ∈ segment ℝ B C := by
  let π : V →ᵃ[ℝ] V :=
    (line[ℝ, B, C]).subtype.comp (orthogonalProjection line[ℝ, B, C]).toAffineMap
  have hπ : π '' convexHull ℝ {A, B, C} ⊆ segment ℝ B C := by
    rw [AffineMap.image_convexHull]
    refine convexHull_min ?_ (convex_segment B C)
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl
    · exact hA
    · have : π x = x :=
        orthogonalProjection_eq_self_iff.2 (left_mem_affineSpan_pair ℝ x C)
      rw [this]
      exact left_mem_segment ℝ x C
    · have : π x = x :=
        orthogonalProjection_eq_self_iff.2 (right_mem_affineSpan_pair ℝ B x)
      rw [this]
      exact right_mem_segment ℝ B x
  exact hπ ⟨P, hP, rfl⟩

/-- If the foot of the altitude from `A` lies on the side `BC`, then for points of the closed
triangle the distance to the side `BC` equals the distance to the line `BC`. -/
theorem infDist_segment_eq_infDist_line
    (hA : (orthogonalProjection line[ℝ, B, C] A : V) ∈ segment ℝ B C)
    (hP : P ∈ convexHull ℝ {A, B, C}) :
    infDist P (segment ℝ B C) = infDist P line[ℝ, B, C] := by
  refine le_antisymm ?_
    (infDist_le_infDist_of_subset (segment_subset_line B C) ⟨B, left_mem_segment ℝ B C⟩)
  rw [← dist_orthogonalProjection_eq_infDist]
  exact infDist_le_dist_of_mem (orthogonalProjection_mem_segment hA hP)

/-- In an isosceles triangle the foot of the altitude from the apex is the midpoint of the base. -/
theorem orthogonalProjection_eq_midpoint (h : dist A B = dist A C) :
    (orthogonalProjection line[ℝ, B, C] A : V) = midpoint ℝ B C := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
  rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← neg_vsub_eq_vsub_rev, inner_neg_left, neg_eq_zero]
  exact AffineSubspace.mem_perpBisector_iff_inner_eq_zero'.1
    (AffineSubspace.mem_perpBisector_iff_dist_eq.2 h)

/-- In an isosceles triangle with apex `A`, distance to the base and distance to its line agree
on the closed triangle. -/
theorem infDist_segment_eq_of_dist_eq (h : dist A B = dist A C)
    (hP : P ∈ convexHull ℝ {A, B, C}) :
    infDist P (segment ℝ B C) = infDist P line[ℝ, B, C] :=
  infDist_segment_eq_infDist_line
    (by rw [orthogonalProjection_eq_midpoint h]; exact midpoint_mem_segment B C) hP

/-- **Viviani's theorem, literally.** For an equilateral triangle `ABC` and any point `P` of
the closed triangle, the distances from `P` to the three sides (as segments) add up to `√3 / 2`
times the side. -/
theorem viviani_segment (hAB : dist A B = dist B C) (hCA : dist C A = dist B C)
    (hP : P ∈ convexHull ℝ {A, B, C}) :
    infDist P (segment ℝ B C) + infDist P (segment ℝ C A) + infDist P (segment ℝ A B) =
      Real.sqrt 3 / 2 * dist B C := by
  have hP₁ : P ∈ convexHull ℝ {B, C, A} := by
    convert hP using 2; ext x; simp; tauto
  have hP₂ : P ∈ convexHull ℝ {C, A, B} := by
    convert hP using 2; ext x; simp; tauto
  rw [infDist_segment_eq_of_dist_eq (by rw [hAB, ← hCA, dist_comm]) hP,
    infDist_segment_eq_of_dist_eq (by rw [← hAB, dist_comm]) hP₁,
    infDist_segment_eq_of_dist_eq (by rw [hCA, dist_comm]) hP₂]
  exact viviani hAB hCA hP

end Viviani
