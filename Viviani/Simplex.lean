/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Mathlib

/-!
# Distances from a point to the facets of a simplex

Everything in this project rests on one observation: the distance from a point to a facet of a
simplex is an affine function of the point, which vanishes on that facet. Hence, if `p` has
barycentric coordinates `w` with respect to a simplex `s`,

  `dist(p, facet opposite i) = |w i| * (height of s from vertex i)`.

Mathlib records the signed form of this as `Affine.Simplex.signedInfDist_affineCombination`;
here we draw the consequences for ordinary (unsigned) distances.

## Main results

For a simplex `s` in a Euclidean affine space, of any dimension `n ≥ 1`:

* `infDist_facetSpan_affineCombination`: the displayed formula.
* `sum_infDist_facetSpan_affineCombination`: on the closed simplex the distances to the `n + 1`
  facets add up to the weighted average `∑ i, w i * s.height i` of the heights.
* `le_sum_infDist_facetSpan`, `sum_infDist_facetSpan_le`: so the sum lies between the smallest
  and the largest height.
* `sum_infDist_facetSpan_const_iff`: the sum is the same at every point of the closed simplex
  if and only if all heights are equal,
* `sum_infDist_facetSpan_const_iff_volume`: if and only if all facets have the same volume.
* `sum_signedInfDist_div_height`, `sum_signedInfDist_eq_of_height_eq`: with signed distances
  the identities hold on the whole affine span, not only inside the simplex.
* `sum_infDist_facetSpan_mul_volume`: `∑ i, dist(p, facet i) * vol(facet i) = n * vol(s)`, the
  identity behind the classical proof by areas.

The distance to a facet always means `Metric.infDist p (facetSpan s i)`: the least distance from
`p` to the affine subspace spanned by the facet (a line for a triangle, a plane for a
tetrahedron).
-/

public section

open EuclideanGeometry Metric Affine Finset

namespace Viviani

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} [NeZero n]

/-- The affine span of the facet of `s` opposite vertex `i`: for a triangle, the line through the
side opposite `i`; for a tetrahedron, the plane through the face opposite `i`. -/
abbrev facetSpan (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  affineSpan ℝ (s.points '' {i}ᶜ)

/-- The height of a simplex from vertex `i` is the distance from that vertex to the affine
span of the opposite facet. -/
theorem height_eq_infDist (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.height i = infDist (s.points i) (facetSpan s i) := by
  rw [← dist_orthogonalProjection_eq_infDist, Simplex.height, Simplex.altitudeFoot,
    Simplex.orthogonalProjectionSpan]
  simp_rw [Simplex.range_faceOpposite_points]

/-- For a point of the affine span of the simplex, the absolute value of Mathlib's signed
distance to a facet is the ordinary distance to the affine span of that facet. -/
theorem abs_signedInfDist_eq_infDist (s : Simplex ℝ P n) (i : Fin (n + 1)) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    |s.signedInfDist i p| = infDist p (facetSpan s i) := by
  rw [← dist_orthogonalProjection_eq_infDist]
  refine AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert ?_
  rwa [affineSpan_insert_affineSpan, Set.insert_image_compl_eq_range]

/-- The signed distance to the facet opposite `i` is the barycentric weight of `i` times the
height from `i`. (A restatement of `Affine.Simplex.signedInfDist_affineCombination` in terms of
`Affine.Simplex.height`.) -/
theorem signedInfDist_affineCombination (s : Simplex ℝ P n) (i : Fin (n + 1))
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    s.signedInfDist i (univ.affineCombination ℝ s.points w) = w i * s.height i := by
  rw [s.signedInfDist_affineCombination i hw, Simplex.height, Simplex.altitudeFoot,
    dist_eq_norm_vsub]

/-- **Key lemma.** The distance from a point to the facet opposite vertex `i` is the absolute
value of its barycentric weight at `i`, times the height from `i`. -/
theorem infDist_facetSpan_affineCombination (s : Simplex ℝ P n) (i : Fin (n + 1))
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    infDist (univ.affineCombination ℝ s.points w) (facetSpan s i) = |w i| * s.height i := by
  rw [← abs_signedInfDist_eq_infDist s i (affineCombination_mem_affineSpan hw _),
    signedInfDist_affineCombination s i hw, abs_mul, abs_of_pos (s.height_pos i)]

/-- **Viviani for every simplex.** For a point of the closed simplex, with barycentric weights
`w`, the distances to the facets add up to the weighted average `∑ i, w i * s.height i` of the
heights. -/
theorem sum_infDist_facetSpan_affineCombination (s : Simplex ℝ P n)
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) (h0 : ∀ j, 0 ≤ w j) :
    ∑ i, infDist (univ.affineCombination ℝ s.points w) (facetSpan s i) =
      ∑ i, w i * s.height i := by
  refine sum_congr rfl fun i _ ↦ ?_
  rw [infDist_facetSpan_affineCombination s i hw, abs_of_nonneg (h0 i)]

omit [NeZero n] in
/-- A point of the closed simplex is an affine combination of the vertices with nonnegative
weights. -/
theorem exists_weights_of_mem_closedInterior {s : Simplex ℝ P n} {p : P}
    (hp : p ∈ s.closedInterior) :
    ∃ w : Fin (n + 1) → ℝ, ∑ j, w j = 1 ∧ (∀ j, 0 ≤ w j) ∧
      p = univ.affineCombination ℝ s.points w := by
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  exact ⟨w, hw, fun j ↦ (hw01 j).1, rfl⟩


/-! ### The distance sum on the closed simplex -/

/-- At a vertex, the distance sum is the height from that vertex. -/
theorem sum_infDist_facetSpan_point (s : Simplex ℝ P n) (j : Fin (n + 1)) :
    ∑ i, infDist (s.points j) (facetSpan s i) = s.height j := by
  have h := sum_infDist_facetSpan_affineCombination s (w := Pi.single j 1)
    (Fintype.sum_pi_single' _ _) (fun k ↦ by by_cases hk : k = j <;> simp [hk])
  rw [univ.affineCombination_piSingle ℝ s.points (mem_univ j)] at h
  simpa [Pi.single_apply] using h

/-- On the closed simplex the distance sum is at least the smallest height. -/
theorem le_sum_infDist_facetSpan {s : Simplex ℝ P n} {p : P} (hp : p ∈ s.closedInterior)
    {m : ℝ} (hm : ∀ i, m ≤ s.height i) : m ≤ ∑ i, infDist p (facetSpan s i) := by
  obtain ⟨w, hw, h0, rfl⟩ := exists_weights_of_mem_closedInterior hp
  rw [sum_infDist_facetSpan_affineCombination s hw h0]
  calc m = ∑ i, w i * m := by rw [← sum_mul, hw, one_mul]
    _ ≤ ∑ i, w i * s.height i := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hm i) (h0 i)

/-- On the closed simplex the distance sum is at most the largest height. -/
theorem sum_infDist_facetSpan_le {s : Simplex ℝ P n} {p : P} (hp : p ∈ s.closedInterior)
    {M : ℝ} (hM : ∀ i, s.height i ≤ M) : ∑ i, infDist p (facetSpan s i) ≤ M := by
  obtain ⟨w, hw, h0, rfl⟩ := exists_weights_of_mem_closedInterior hp
  rw [sum_infDist_facetSpan_affineCombination s hw h0]
  calc ∑ i, w i * s.height i ≤ ∑ i, w i * M :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hM i) (h0 i)
    _ = M := by rw [← sum_mul, hw, one_mul]

/-- If all heights of a simplex equal `h`, the distances from any point of the closed simplex to
the facets add up to `h`. -/
theorem sum_infDist_facetSpan_eq_of_height_eq {s : Simplex ℝ P n} {h : ℝ}
    (hh : ∀ i, s.height i = h) {p : P} (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) = h :=
  le_antisymm (sum_infDist_facetSpan_le hp fun i ↦ (hh i).le)
    (le_sum_infDist_facetSpan hp fun i ↦ (hh i).ge)

/-- **Viviani and its converse, in every dimension.** The distance sum is constant on the closed
simplex if and only if all heights of the simplex are equal. -/
theorem sum_infDist_facetSpan_const_iff (s : Simplex ℝ P n) :
    (∃ c : ℝ, ∀ p ∈ s.closedInterior, ∑ i, infDist p (facetSpan s i) = c) ↔
      ∀ i j, s.height i = s.height j := by
  constructor
  · rintro ⟨c, hc⟩ i j
    rw [← sum_infDist_facetSpan_point s i, ← sum_infDist_facetSpan_point s j,
      hc _ (s.point_mem_closedInterior i), hc _ (s.point_mem_closedInterior j)]
  · intro h
    exact ⟨s.height 0, fun p hp ↦ sum_infDist_facetSpan_eq_of_height_eq (fun i ↦ h i 0) hp⟩

/-! ### Signed distances: the identity on the whole affine span -/

/-- **Ternary-plot reading.** Signed distance to a facet, measured in units of the corresponding
height, is the barycentric coordinate. -/
theorem signedInfDist_div_height (s : Simplex ℝ P n) (i : Fin (n + 1))
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    s.signedInfDist i (univ.affineCombination ℝ s.points w) / s.height i = w i := by
  rw [signedInfDist_affineCombination s i hw, mul_div_assoc, div_self (s.height_pos i).ne',
    mul_one]

/-- For every point of the affine span of a simplex, the signed distances to the facets, each
measured in units of the corresponding height, add up to `1`. -/
theorem sum_signedInfDist_div_height (s : Simplex ℝ P n) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    ∑ i, s.signedInfDist i p / s.height i = 1 := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  simp_rw [signedInfDist_div_height s _ hw, hw]

/-- **Signed Viviani on the whole plane.** If all heights equal `h`, the signed distances to the
facets add up to `h` at every point of the affine span of the simplex, inside or outside. -/
theorem sum_signedInfDist_eq_of_height_eq {s : Simplex ℝ P n} {h : ℝ}
    (hh : ∀ i, s.height i = h) {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    ∑ i, s.signedInfDist i p = h := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  simp_rw [signedInfDist_affineCombination s _ hw, hh, ← sum_mul, hw, one_mul]

/-! ### Volumes: the content of the classical area proof -/

/-- Height times the volume of the opposite facet is `n` times the volume of the simplex. -/
theorem height_mul_volume_faceOpposite (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.height i * (s.faceOpposite i).volume = n * s.volume := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [s.volume_eq i]
  field_simp

/-- **The area identity.** For a point `p` of the closed simplex,
`∑ i, dist(p, facet i) * vol(facet i) = n * vol(s)`. For a triangle this says that the three
triangles with apex `p` over the three sides have total area equal to the area of the triangle,
which is the heart of the classical proof of Viviani's theorem. -/
theorem sum_infDist_facetSpan_mul_volume {s : Simplex ℝ P n} {p : P}
    (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) * (s.faceOpposite i).volume = n * s.volume := by
  obtain ⟨w, hw, h0, rfl⟩ := exists_weights_of_mem_closedInterior hp
  have : ∀ i, infDist (univ.affineCombination ℝ s.points w) (facetSpan s i) *
      (s.faceOpposite i).volume = w i * (n * s.volume) := fun i ↦ by
    rw [infDist_facetSpan_affineCombination s i hw, abs_of_nonneg (h0 i), mul_assoc,
      height_mul_volume_faceOpposite]
  simp_rw [this, ← sum_mul, hw, one_mul]

/-- Two heights of a simplex are equal exactly when the opposite facets have equal volume. -/
theorem height_eq_iff_volume_faceOpposite_eq (s : Simplex ℝ P n) (i j : Fin (n + 1)) :
    s.height i = s.height j ↔ (s.faceOpposite i).volume = (s.faceOpposite j).volume := by
  have h := (height_mul_volume_faceOpposite s i).trans (height_mul_volume_faceOpposite s j).symm
  have hi := s.height_pos i
  have hj := s.height_pos j
  have vi := (s.faceOpposite i).volume_pos
  have vj := (s.faceOpposite j).volume_pos
  constructor
  · intro e
    rw [e] at h
    exact mul_left_cancel₀ hj.ne' h
  · intro e
    rw [e] at h
    exact mul_right_cancel₀ vj.ne' h

/-- The distance sum is constant on the closed simplex if and only if all facets have the same
volume. -/
theorem sum_infDist_facetSpan_const_iff_volume (s : Simplex ℝ P n) :
    (∃ c : ℝ, ∀ p ∈ s.closedInterior, ∑ i, infDist p (facetSpan s i) = c) ↔
      ∀ i j, (s.faceOpposite i).volume = (s.faceOpposite j).volume := by
  simp_rw [sum_infDist_facetSpan_const_iff, height_eq_iff_volume_faceOpposite_eq]

/-! ### Regular simplices -/

/-- All heights of a regular simplex (in the sense of `Affine.Simplex.Regular`) are equal. -/
theorem height_eq_of_regular {s : Simplex ℝ P n} (hs : s.Regular) (i j : Fin (n + 1)) :
    s.height i = s.height j := by
  obtain ⟨x, hx⟩ := hs (Equiv.swap i j)
  let f : P →ᵃⁱ[ℝ] P := x.toRealAffineIsometryEquiv.toAffineIsometry
  have e : s.map f.toAffineMap f.injective = s.reindex (Equiv.swap i j).symm := by
    ext k
    change x (s.points k) = s.points ((Equiv.swap i j).symm k)
    simpa using (congrFun hx k).symm
  have h := s.height_map f i
  rw [e, Simplex.height_reindex] at h
  simpa using h.symm

end Viviani
