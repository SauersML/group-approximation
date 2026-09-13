# SL_3(Z) on SL_3(R)/Λ, part 2: uniform distance from finite actions (2026-09-13)

Lane `ex-sl3z-cocompact-quotient`. Continues `sl3z-cocompact-quotient-holonomy-drift-2026-09-13.md`,
Sections 1--2, and uses the same notation.

## 3. Theorem E

**Hypothesis (R).** `Λ <= SL_3(R)` is a cocompact lattice with a faithful homomorphism
`ι : Λ → GL_m(Q)` whose image contains no nontrivial unipotent matrix.

*Examples.* Let `D` be a central division algebra of degree `3` over `Q` with `D ⊗ R ≅ M_3(R)`. Any
discrete subgroup of `SL_1(D)(Q) <= SL_3(R)` satisfies (R) through `ι(x) = (left multiplication on
D ≅ Q^9)`. Indeed, `ι(x)` unipotent means `(x − 1)^9 = 0` in `D`, so `x = 1`. Conjugating `Λ` inside
`SL_3(R)` changes `X` only by the `SL_3(Z)`-equivariant bi-Lipschitz map `xΛ ↦ xg^(−1)(gΛg^(−1))`, and
(R) is intrinsic to the abstract group, so the theorem is conjugation invariant.

**Theorem E.** Under (R) there is `ε_E > 0` such that for every finite `SL_3(Z)`-set `V` and every
`y : V → X`, some `v ∈ V` and `s ∈ S` have `d̄(y(sv), s·y(v)) >= ε_E`.

*Proof.* Choose `ε_E < ε_0` with `η(ε_E) < κ/12` (Sections 1 and 2). Suppose every pair is good at scale
`ε_E`. By Definition 1.3(3), `SL_3(Z)` acts on `Ω = V × Λ`, and the stabilizer of `(v,μ)` is `ker ρ_v`.

*Rigidity.* `Γ_v` is an arithmetic subgroup of `SL_3(Q)`. Bass--Milnor--Serre (Publ. IHÉS 33, 1967)
Theorem 16.2 applies, with (16.1) verified in `bms-sln-z-representations-agree-with-algebraic-ones-citation`.
It gives an algebraic `F : SL_3 → GL_m` over `Q` with `F = ι∘ρ_v` on some finite-index `Γ' <= Γ_v`.
Algebraic homomorphisms preserve unipotency, so for unipotent `u ∈ Γ'`, `ι(ρ_v(u))` is unipotent, hence
trivial, hence `ρ_v(u) = 1`. `Γ'` contains `e_ij^N` for some `N`. These generate `E_3(Z, N)`, which has
finite index in `SL_3(Z)` (BMS, Introduction (i)). So `ker ρ_v` has finite index.

*Drift.* Every `SL_3(Z)`-orbit on `Ω` is finite. The union `O` of the orbits through `V × {1}` is finite,
invariant under all `σ̃_s`, and has no bad pairs. Corollary 2.3 requires a proportion
`θ_* = (κ/12 − η(ε_E))/B(D_X) > 0` of bad pairs. Contradiction. ∎

**Calibrations.**
* *`Λ = SL_3(Z)`.* (R) fails because of unipotents, and so does cocompactness. The Hecke sets
  `V_k ⊆ SL_3(R)/SL_3(Z)` are finite `SL_3(Z)`-sets with `y` = inclusion, every pair exactly good. The
  holonomy is `x ↦ axa^(−1)`, with infinite image. Unbounded lifts in the cusp defeat Corollary 2.3.
* *Irrational rotation `Z ↷ R/Z` by `α`.* The finite actions `Z/q` with marks `kp/q`, `|p/q − α| < ε`, are
  good everywhere. Their holonomy `q ↦ p` has infinite image in `Z`, which is allowed because no
  rigidity theorem forces it to be finite.
* *Model test of (R).* A trivial model fails it: `SL_3(Z)` itself, where unipotents exist. Real objects
  satisfy it: the norm-one groups of maximal orders in cubic division algebras.

## 4. Where this stops, and what a nonsoficity proof would need

Theorem E needs every pair good on an honest action. Microstates relax both conditions:

1. **Almost-actions.** `σ` may violate the relators on a proportion `ε` of vertices. The labelled
   system is then an action of the free group `F_S` on `Ω`, with no holonomy homomorphism.
2. **Defects.** A proportion `ε` of pairs may be bad. Labels on bad pairs are unconstrained, and
   holonomy along loops through them is arbitrary.

By Corollary 2.3, a sofic model must have infinite holonomy along every finite labelled region, and
defects are what can supply it. A proof of `sl3z-cocompact-quotient-admits-no-topological-microstates`
along these lines needs a defect-tolerant superrigidity: an almost-cocycle of `SL_3(Z)` with values in
`Λ` and a vanishing proportion of defects is close in Hamming distance to one with finite holonomy.
This is a cosystolic-expansion statement with nonabelian coefficients `Λ` for the Cayley complexes of
the almost-actions, not a property (T) statement. Becker--Lubotzky instability (recalled, not verified
here) suggests that for general almost-actions the Hamming rounding fails. So the negative direction
would need to use the continuous marks as well, not only the combinatorics.

Conversely, a positive construction must realize infinite `Λ`-holonomy through a vanishing proportion
of seams, while keeping the marks almost equivariant everywhere else. A natural test object: glue exact
congruence-quotient models along sparse seams whose labels generate a Zariski-dense subgroup of `Λ`.
