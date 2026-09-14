# Lane ms-core-3: simple_kazhdan_sofic_group.tex, "Finite models" tail (tex 146–153 at bf961c128)

Target: origin/main `simple_kazhdan_sofic_group.tex` at bf961c128 (340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99). Rows keyed
`LINE:<l>@bf961c128` in `metadata/sk-census-rows/ms-core-3.tsv`.

CLAIM tex 146–153 (entrywise finite models of G, the injective partial homomorphism into GL_{3N}(F₂), "Thus G is LEF", sofic and hyperlinear models) — split proposed to ms-units 2026-09-13 ~19:05 (ms-units keeps tex 118–145); new modules under GroupApproximation/Manuscript/SimpleKazhdanSofic/ once the ledger lands

## Ledger (tex 146–153 at bf961c128; provisional, ownership split pending ms-units' reply)

| key | sentence | carriers on origin (root-reachable) | status (planned) | gap |
|---|---|---|---|---|
| `LINE:146@bf961c128` | "For a finite subset of $G$, include the entries of its elements, their inverses, their differences, and all intermediate sums and products needed for matrix multiplication." | `Pestov91.IsLEFRing.matrix`, `Pestov91.IsLEFRing.isLEF_units` (Pestov91/LEF) | partial | These give entrywise finite ring models into an abstract finite ring. The printed target is the ring model `R → M_N(F₂)` of tex 131–145 (ms-units), applied entrywise. |
| `LINE:148@bf961c128` | "The resulting model is an injective partial homomorphism into $\GL_{3N}(\F_2)$." | none at the printed target | open | Build: an entrywise extension of an injective partial ring model `R → M_N(F₂)` is an injective partial group homomorphism `GL_3(R) ⊇ F → GL_{3N}(F₂)`, through `M_3(M_N(F₂)) ≅ M_{3N}(F₂)`. |
| `LINE:149@bf961c128` | "Thus $G$ is LEF." | `Pestov91.isLEF_elementaryGroup (hR : IsLEFRing R)`; Palomar witness `Pestov91.isLEF_elementaryGroup_witnessRing` (Toeplitz ring only) | partial | For a general infinite minimal subshift X (thm:main), `IsLEFRing (LC(X,F₂) ⋊_T ℤ)` is ms-units' half (tex 123–145). |
| `LINE:150@bf961c128` | "The regular permutation actions of these finite groups give sofic models; their permutation matrices give hyperlinear models~\cite{Pestov}." | `isSofic_of_isLEF` (Sofic/LEFSofic), `Pestov91.isHyperlinear_of_isLEF` via `isHyperlinear_of_isSofic` (Sofic/Hyperlinear) | partial | Closed and proved, so no literature binder for [Pestov]. Conditional only on "G is LEF"; route check of the regular action and permutation matrices pending. |
