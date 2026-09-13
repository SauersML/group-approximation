# UN review, part 10: descent and constant-shape inflation of torus tiling modules

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-labbe-torus-decider`, landing `b89e7992df`, artifact
`research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md`. Inputs:
`torus-quantum-tilings-decide-matriciality-of-sft-rings`, reviewed PASS by un-verify-measure
(`un-review-measure-2026-09-13-part3.md` §L1).

| item | node | verdict |
|---|---|---|
| (1) | `torus-tiling-modules-restrict-to-smaller-scales` (Theorem A) | PASS |
| (2) | `constant-shape-substitutions-inflate-torus-tiling-modules` (Theorem B) | PASS |
| (3) | `self-similar-sft-matricial-iff-one-torus-module` (Corollary C) | PASS |
| (4) | Attempts on `labbe-wang-shift-crossed-product-is-exactly-matricial` | PASS with one wording repair |

Row 7 of the UN table stays undecided. Nothing here is framed as deciding it.

## 1. Descent

- (T1) is the same relation at both scales. (T2) at scale `D′` is required only for representatives in
  `B_(2D′) ⊆ B_(2D)`.
- (T3) at `D′`. Insert `Σ_a e_a(t+h) = 1` for `h ∈ B_D ∖ B_(D′)`. All factors in play sit at sites within
  sup-distance `2D`, so they commute and the product is order independent.
  - If two lifts `h ≠ h′` give the same torus site, the product contains `e_(π̃(h))(s) e_(π̃(h′))(s)`, which is zero
    unless the letters agree. So the expansion is an algebraic identity with no embedding hypothesis.
  - Every extension `π̃` restricts to the illegal `π`, so it is illegal (languages are closed under restriction), and
    (T3) at scale `D` kills it.

## 2. Inflation (constant shape `S = diag(s_1, s_2)`, `s_min ≥ 2`)

- **Well defined.** A class of `Z²/SΛ` has representatives `Sp + j`, `j ∈ Q_S`, unique up to `p ↦ p + λ`. `f_b(t′)`
  depends only on `(p̄, j)`.
- **(T1).** `Σ_b f_b = Σ_a e_a(p̄) = 1`, and `f_b f_(b′) = Σ_(a : σ(a)_j = b = b′) e_a(p̄)`.
- **(T2).**
  - Given a representative `w′` of `t′_2 − t′_1` with `|w′|_∞ ≤ 2D′`, choose the lift `t′_2 = t′_1 + w′`.
  - For integers, `⌊(x+w)/s⌋ − ⌊x/s⌋ ≤ ⌈|w|/s⌉`, and `|w′_i| ≤ 2 s_min(D−1) ≤ 2 s_i(D−1)`. So the parents differ by
    at most `2(D−1)` coordinatewise.
  - Their classes have a representative in `B_(2D)`, and (T2) at scale `D` applies. Same-parent generators commute
    trivially.
- **(T3).**
  - **Parents.** The lifted ball `t′_0 + B_(D′)` spans `2D′+1` integers per coordinate, hence at most
    `⌈(2 s_i(D−1)+1)/s_i⌉ = 2D−1` parent values. So `P ⊆ c + B_(D−1)`.
  - **Grouping.** For one parent `p`, the product over its children is `Σ_(a∈A_p) e_a(p̄)` by orthogonality.
  - **Expansion.** Expanding over `P` and inserting (T1) on `c + B_D ∖ P` gives a sum over `ρ̃ : c + B_D → A` with
    `ρ̃(p) ∈ A_p`. This is again an algebraic identity when lifts coincide on the torus.
  - **Illegal `ρ̃`:** the term dies by (T3) at scale `D`.
  - **Legal `ρ̃`:** `x ∈ Ω` with `x|_(c+B_D) = ρ̃` (shift invariance) gives `σ(x) ∈ Ω`. Then
    `σ(x)(t′_0 + h) = σ(ρ̃(p_h))_(j_h) = π(h)`, so `π` would be legal, a contradiction.
- **Scale.** `D′ = s_min(D−1) ≥ 2D−2 ≥ D+1` for `D ≥ 3`, and `D′ ≥ r` once `D ≥ r`.

## 3. Corollary C

- **(⇒)** Theorem 1(d) of the torus criterion gives modules at every `D ≥ r`. Take `D = max(r, 3)` and descend to 3.
- **(⇐)** From a base module at scale 3, `D_(m+1) = s_min(D_m − 1) ≥ D_m + 1` is unbounded. Theorem B gives modules at
  every `D_m` on `Z²/S^mΛ`, descent gives every scale, and the torus criterion (⇐) gives the unital embedding.
- **Hypotheses.** Free minimal is used only through the torus criterion. `k` finite is required by it.
- **Scale 3.** The algebra at scale 3 is defined through the global language `L_(B_3)(Ω)`, so the base relations do
  not depend on `r`.

## 4. Attempts on `labbe-wang-shift-crossed-product-is-exactly-matricial`

- **"What holds"** matches the reviewed nodes above.
- **No recognizable constant-shape self-similarity.** Marked recalled; not imported.
  - The argument is sound in outline. A recognizable constant-shape substitution gives a continuous `S`-adic odometer
    factor, hence rational eigenvalues. `Ω_U` is measure-isomorphic to a golden rotation coding
    (`labbe-shift-is-a-toral-rotation-coding`), whose point spectrum has no nontrivial rational eigenvalues.
  - The claim is correctly limited to recognizable substitutions (the artifact says non-recognizable ones are not
    excluded).
- **Skeleton argument.** Marked heuristic. One sentence asserted as fact that the width and height projections are
  constant along columns and rows in a module. That is established only for legal words, and (T3) constrains only
  local products. Repaired: the sentence now says "should be … (not proved for modules; (T3) constrains only local
  products)".
- **Searches.** Recorded as not run, with the reasons. Consistent.
