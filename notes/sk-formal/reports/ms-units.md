# Lane ms-units: simple_kazhdan_sofic_group.tex, "Finite models", tex 118–145 at bf961c128

Lead: session nonsofic-existence-49 (ROSTER-sk, re-scoped 18:58).  Target text: origin/main `simple_kazhdan_sofic_group.tex` at
bf961c128, md5 7b3dc4ec92b4581553bc0dc2b0edcb99 (re-checked 19:1x).  Rows keyed `LINE:<l>@bf961c128`.
Split by agreement: ms-units 118–145 (the ring models); ms-core-3 146–153 (entrywise models of G, LEF, sofic, hyperlinear).

## Ledger

| line(s) | sentence (abridged) | carrier on main | status now | plan |
|---|---|---|---|---|
| 118 | `\subsection*{Finite models}` | — | structural | row only |
| 119–120 | "A group is LEF if every finite subset embeds injectively into a finite group, preserving all products that stay in that subset." | `Sofic.IsLEF` (permutation models); `Sofic.FiniteGroupModel` | definition, verifying | check the finite-group form equals the permutation form |
| 121 | "We construct such models for R, and then apply them entrywise." | — | structural | roadmap; the ring endpoint below and ms-core-3's entrywise half carry it |
| 123–124 | "For each k, there is a periodic sequence y = w^∞ with exactly the same words of length 2k+1 as X." | none (Pestov91 `exists_periodic_model` is Toeplitz-only) | open | build `exists_periodic_sameWords` |
| 124–125 | "Indeed, minimality implies uniform recurrence." | none for general subshifts | open | build `uniformlyRecurrent_of_minimal` |
| 125–127 | "In a point of X, choose two occurrences of the same word of length 2k, separated by a segment w long enough to contain every word of length 2k+1." | none | open | build (occurrences at 0 and N, N ≥ ℓ) |
| 127–128 | "Repeating this segment introduces no new word of that length at the join." | none | open | build: every window of y is a word of the point, read straight through the join |
| 128–129 | "Its length N can be chosen arbitrarily large." | none | open | build (N ≥ any prescribed N0) |
| 131 | "Let Pδ_n = δ_{n+1} on F_2^{Z/NZ}." | `Pestov91.shiftMatrix` | definition, verifying | direction check against `shiftMatrix_apply` |
| 131–133 | "If f depends on a window [−ρ,ρ], evaluate its local table along y to obtain a diagonal matrix D_y(f)." | `WordGraph.exists_radius`, `WordGraph.evalFamily` | partial | D_y as evaluation at points realizing the windows of y |
| 133–136 | "Send Σ f_j u^j ↦ Σ D_y(f_j) P^j." | `Pestov91.periodicModel` | definition, verifying | instantiate with D_y |
| 137–141 | "For any fixed finite list … choose k larger than all windows … The relation P^iD_y(f)P^{-i} = D_y(f∘T^{-i}) then preserves every listed operation." | `Pestov91.periodicModel_mul` (covariance hypothesis) | partial | prove the covariance of D_y for k ≥ radius + degree |
| 141–142 | "Nonzero coefficients remain nonzero, since every allowed window occurs in y." | none for y | open | build from the same-words clause |
| 142–144 | "Taking N larger than twice the largest absolute exponent makes the corresponding cyclic diagonals distinct; hence nonzero differences also remain nonzero." | `Pestov91.eq_of_periodicModel_eq`, `intCast_zmod_inj` | formalized once instantiated | instantiate |
| (endpoint) | R = LC(X, F₂) ⋊_T ℤ is an LEF ring over these models | `Pestov91.isLEFRing_skewMonoidAlgebra_of_periodic` | partial | build `isLEFRing_clopenCrossedProduct_of_minimal` |

Existing carrier on a DIFFERENT route: ms-traces-3's `WordGraph.isLEFRing_clopenCrossedProduct_of_cycleCondition` (178808d0a), one
cyclic periodic word per nonzero coefficient.  The note's route uses one periodic y carrying every (2k+1)-word, so it is built
separately and the cycle-condition route is recorded as a cross-check only.

Spelling (shared with ms-core-3): `A : Type` finite discrete, `X : Set (ℤ → A)` closed, `hX : ∀ n, Set.MapsTo (shift n) X X`,
infinite, minimal (dense orbits in X); `R = ClopenCrossedProduct (WordGraph.shiftHomeomorph hX) (ZMod 2)`.

## CLAIMS

- CLAIM tex 123–129: `GroupApproximation/Manuscript/SimpleKazhdanSofic/MinimalSubshiftPeriodicWord.lean`, which proves uniform
  recurrence from minimality and the periodic word y with the same (2k+1)-words and arbitrarily large N.
- CLAIM tex 131–144 and the ring endpoint: `GroupApproximation/Manuscript/SimpleKazhdanSofic/FiniteModelsRing.lean`, which proves
  D_y, covariance, nonzero coefficients, distinct diagonals and `IsLEFRing R`.

## Re-scope 19:45 (PROTOCOL: current tip, ranges by section, rows by 12-hex hash)

The note is at e80dcf20a (386 lines, md5 4ad49212…). "Finite models" is ≈116–177.  Split agreed with ms-core-3:
- ms-units: 117–145;
- ms-core-3: 147–177 (marked limits, SL_{3N_ℓ}(F₂), expanders, sofic, hyperlinear, operator-algebra consequences).
Rows wait for skf-census to regenerate `metadata/SK_SENTENCE_CENSUS.tsv` at the tip; the census on origin is still at bf961c128.

Route changes at the tip, with carriers:
- 121–124: "Fix x ∈ X … every word of X occurs in x, and x_{[0,2ℓ)} recurs at arbitrarily large positions.  Choose such a position m …".  Carriers: `exists_nat_word_eq_of_minimal`, `exists_recurrence_of_minimal`, `exists_occurrences_of_mem`.
- 124–129: the m-periodic y_ℓ agrees with x on [0, m+2ℓ); windows are translates of windows starting in [0,m); same words.  Carriers: `periodicWord_natCast_eq`, `periodicWord_window_eq`, `periodicWord_exists_window_eq`.
- CLAIM 129–132: least period N_ℓ ≥ #words, and "a subshift with boundedly many words of each length is finite", so N_ℓ → ∞.  Module `GroupApproximation/Manuscript/SimpleKazhdanSofic/FiniteModelsLeastPeriod.lean`.
- CLAIM 134–145: D_ℓ(f)δ_t = f(T^t y_ℓ)δ_t on F₂^{Z/N_ℓ}, φ_ℓ = Σ D_ℓ(f_j)P^j, covariance, identities for large ℓ, φ_ℓ(r) ≠ 0 for large ℓ.  Module `GroupApproximation/Manuscript/SimpleKazhdanSofic/FiniteModelsAsymptotic.lean`, exposing the named Prop ms-core-3 consumes.
- Kept: `FiniteModelsRing` (`exists_matrixModel_clopenCrossedProduct`), which carries the injective finite ring models that ms-core-3's landed `FiniteModelsGroup` (3d1ce154d) consumes.
