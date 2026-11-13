# Claims and evidence

Every claim we make in public about this project, with what supports it and how to check it. If a sentence about the project is not covered here, we should not be saying it.

| Claim | Evidence | Reproduce |
| --- | --- | --- |
| Viviani’s theorem for every point of a closed equilateral triangle, with distances to the three sides as segments, value √3/2 × side | `Viviani.viviani_segment` | `lake build` |
| The same with distances to the side lines; no non-degeneracy hypothesis | `Viviani.viviani` | `lake build` |
| Converse: for an affinely independent triangle, constant distance sum ⇔ equilateral | `Viviani.viviani_iff`, `Viviani.sum_infDist_const_iff_equilateral` | `lake build` |
| In every triangle the sum is the weighted average of the heights, hence between the least and greatest height | `sum_infDist_eq_of_affineIndependent`, `le_sum_infDist_facetSpan`, `sum_infDist_facetSpan_le` | `lake build` |
| Signed identity on the whole affine span | `sum_signedInfDist_div_height`, `sum_signedInfDist_eq_of_height_eq` | `lake build` |
| Simplices of every dimension n ≥ 1 with equal edges r: sum = √((n+1)/(2n))·r | `height_of_dist_eq`, `viviani_simplex`, `viviani_tetrahedron` | `lake build` |
| In any simplex: constant sum ⇔ equal heights ⇔ equal facet volumes; constant in every disphenoid | `sum_infDist_facetSpan_const_iff`, `sum_infDist_facetSpan_const_iff_volume`, `viviani_disphenoid` | `lake build` |
| Area identity Σ dᵢ·vol(Fᵢ) = n·vol(S) on the closed simplex | `sum_infDist_facetSpan_mul_volume` | `lake build` |
| The hypotheses are satisfiable and the theorem gives √3 on (0,0), (2,0), (1,√3) | `Viviani.Examples.sum_eq_sqrt_three` | `lake build` |
| No `sorry`; only `propext`, `Classical.choice`, `Quot.sound`, for all 85 declarations | `scripts/Audit.lean` | `lake env lean scripts/Audit.lean` |
| Builds without warnings on Lean 4.36.0-rc2, Mathlib `7bcc5e95` | step 2 of the transcript | `scripts/verify.sh` |
| Re-checked by `leanchecker` (6 modules) and by nanoda (48,926 declarations) | steps 6–7 of the transcript | `scripts/verify.sh` |
| Four planted defects are rejected | step 8 of the transcript | `scripts/verify.sh` |
| Each website figure reports numbers consistent with the theorems | `site/build/interact.py` (private site source) | run it against the built page |
| The current development was written without consulting the earlier Lean formalizations’ code | working record of the project | not machine-checkable; stated as our account |

## Things we do not claim

- That this is the first, second or only Lean formalization of Viviani’s theorem or of any result above. Earlier formalizations exist (see the README).
- That any of the mathematics is new. Sources are cited in the README.
- That the key lemma is ours: its signed form is Mathlib’s `Affine.Simplex.signedInfDist_affineCombination`, and the height–volume relation is Mathlib’s `Affine.Simplex.volume_eq`.
- That Bang’s theorem (equal face areas imply a disphenoid) is formalized here. It is not.
- That the classical area proof is formalized *as a proof*. The area identity is proved, but from the weights, not by cutting and adding measures.
- That anything was reviewed by a person other than the authors, or that “nothing is taken on trust”.
- Any ranking against other projects.

## Search record for novelty

No novelty search was carried out in this phase, because no novelty is claimed. Before making any “we found no earlier formalization of X” statement, run and record the search described in the project’s claims policy (Mathlib, GitHub repositories and code, Zenodo, arXiv, Google Scholar, Lean Zulip, large proof collections, Isabelle AFP, HOL Light, Rocq/GeoCoq, Mizar).
