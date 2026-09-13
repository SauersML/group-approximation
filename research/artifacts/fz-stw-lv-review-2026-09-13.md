# STW Problem LV: review of the repository answer (2026-09-13)

**Verdict: FAIL.** The mathematics is correct: for irrational `λ, μ > 0` the flows `α^(λ)` and `α^(μ)` on `O_2` are
cocycle conjugate iff `λ = μ`. But this is not a first-time solution of Problem LV.

- Under the literal reading, the answer is an immediate corollary of a standard invariant, the KMS inverse temperature,
  which the literature already uses.
- The one published paper that addresses LV reads it as a completeness question: is `β` a complete invariant once the
  frequencies are not normalized? That question has only a generic partial answer (Neagu, arXiv:2509.00829).
- One scope note in the repository is contradicted by that paper, generically.

Reviewed on main 43019778646a:
- the research nodes `stw99-problem-lv-quasifree-flows-o2`, `o2-quasifree-flows-cocycle-conjugacy-classified`,
  `o2-quasifree-flows-kms-separation-proof`, `stw99-lv-answered-by-kms-separation`, `stw99-lv-via-dual-trace-scaling-spectrum`,
  `stw99-lv-dual-trace-scaling-spectrum-cocycle-invariant` and `stw99-lv-dual-trace-scaling-spectrum-proof`;
- research/artifacts/stw99-lv-quasifree-flow-solution-2026-08-30.md;
- the LV section of research/artifacts/stw99-late-band-audit-2026-08-31.md.

## 1. The printed problem
**Source.** Schafhauser–Tikuisis–White, "Nuclear C*-algebras: 99 problems", arXiv:2506.10902v2 (8 May 2026). Problem
LV is in the classification section, immediately after Problem LIV.

**The family.** `α^(λ) : R ↷ O_2` for `λ ∈ R`, with `α_t(s_1) = e^{it} s_1` and `α_t(s_2) = e^{iλt} s_2`.

**What STW recall:**
- For irrational `λ < 0` the flow is Rokhlin, so it is unique up to cocycle conjugacy (Kishimoto).
- For irrational `λ > 0` the crossed product is simple and stably projectionless, with a unique tracial ray
  (Kishimoto–Kumjian).
- Dean showed that the crossed product is `W ⊗ K` for generically many `λ`.

**The problem:**

> "Determine when the quasifree flows α(λ) on the Cuntz algebra O2 described above are cocycle conjugate for irrational λ > 0."

**The equivalence (footnote 78):**

> "Two actions α : G ↷ A and β : G ↷ B are cocycle conjugate if there is an isomorphism σ : A → B and a function w : G → U(B) (or U(M(B)) when B is non-unital) such that σα_gσ^{-1} = Ad(w_g)β_g and w_{gh} = w_g β_g(w_h) for all g, h ∈ G."

So cocycle conjugacy is a conjugacy followed by an exterior equivalence, and time is not rescaled. `O_2` is unital, so
`w` takes values in `U(O_2)`; it is continuous, as usual. The v2 addenda (17.1, 25.1, 26.1) do not mention LV.

## 2. Re-derivation of the claim
**(a) KMS equation.** Let `ω = (1, λ)`.
1. Each `s_j` is entire analytic, with `α_z(s_j) = e^{iω_j z} s_j`.
2. For a β-KMS state `φ`, the condition `φ(s_j^* α_{iβ}(s_j)) = φ(s_j s_j^*)` gives `φ(s_j s_j^*) = e^{-ω_j β}`.
3. Since `s_1 s_1^* + s_2 s_2^* = 1`, this forces `e^{-β} + e^{-λβ} = 1`.
4. For `β ≤ 0` the left side is at least 2. On `(0, ∞)` it decreases strictly from 2 to 0. So `β(λ) > 0` is unique.

A `β(λ)`-KMS state exists: take the product state with density `diag(e^{-β}, e^{-λβ})` on the gauge-invariant UHF core
and compose it with the conditional expectation onto the core.

**(b) Injectivity.** If `λ < μ`, then `e^{-β(λ)} + e^{-μβ(λ)} < 1`, so `β(μ) < β(λ)`.

**(c) Invariance.** A conjugacy transports KMS states. Now suppose `γ_t = Ad(w_t) α_t` (exterior equivalence).
1. The maps `π_γ(a) ↦ π_α(a)` and `λ_γ(t) ↦ π_α(w_t) λ_α(t)` define an isomorphism `A ⋊_γ R → A ⋊_α R`. It intertwines
   the dual flows exactly, because both fix the coefficients and multiply the unitary at `t` by the same scalar.
2. The dual weight of a β-KMS weight is a densely defined, lower semicontinuous trace, scaled by `e^{-βs}` under the dual
   flow. Conversely, every such trace comes from a densely defined β-KMS weight.
3. On a unital algebra, a densely defined KMS weight is finite: its left ideal is dense, so it contains an invertible
   element and hence 1. A finite nonzero weight is a positive multiple of a state.

So the set `{β : γ has a β-KMS state}` is a cocycle conjugacy invariant, and the unique tracial ray is not needed. The
repository's route is also valid. It reads the scaling exponent on the unique ray and identifies it with `β` through the
dual weight, so it needs only the forward half of step 2, plus Kishimoto–Kumjian.

**(d) Node displays.**
- `o2-quasifree-flows-cocycle-conjugacy-classified` states exactly (a)–(c).
- In `stw99-lv-dual-trace-scaling-spectrum-proof`, the transport `τ_α∘Φ = r τ_β` uses the unique ray on both sides.
  Deducing that the positive character `c_α` is continuous from lower semicontinuity is correct.
- Steps 1–4 of `o2-quasifree-flows-kms-separation-proof` are sound.
- Model check: swapping `s_1 ↔ s_2` and reparametrizing `t ↦ t/λ` conjugates `α^(λ)` to `α^(1/λ)`. This is consistent
  with `β(1/λ) = λ β(λ)`.

## 3. Novelty and fidelity (search to 2026-09-13)
- **Kishimoto–Kumjian**, Canad. J. Math. 48 (1996), Theorem 4.1. For rationally independent positive frequencies, the
  crossed product is simple and stably projectionless, with a unique trace up to scalar.
- **Kishimoto**, "Rohlin flows on the Cuntz algebra O2", Internat. J. Math. 13 (2002).
  - Quasi-free flows on `O_2` either are Rokhlin or have a unique KMS state, and all the Rokhlin ones are cocycle
    conjugate.
  - After his Theorem 1.2 he asks whether the cocycle conjugacy class of the non-Rokhlin ones is determined by the
    inverse temperature of the unique KMS state. This is as reported by Neagu; I did not read Kishimoto's paper. The
    question already assumes that `β` is an invariant.
- **Neagu**, arXiv:2509.00829v1 (31 Aug 2025), "Generic classification of the quasi-free flows on the Cuntz algebra O2".
  - Theorem 3.12 covers flows with frequencies `L = (L_1, L_2)`. Take the ratios `L_2/L_1 ∈ R_+ \ Q` for which `α^L` is
    classified up to cocycle conjugacy by `β`, where `e^{-βL_1} + e^{-βL_2} = 1`. This set is dense and of second
    category.
  - (3.8) records the scaling `τ∘α̂^L_t = e^{-βt} τ`.
  - The proof combines three inputs: his Theorems 3.6 and 3.10 (generic equivariant Z-stability, generic Rokhlin dual
    flow); Szabó's classification of Rokhlin flows (Comm. Math. Phys. 382 (2021), Theorem C); and his Proposition 1.2.
    Part (i) of that proposition is the crossed-product intertwining of §2(c).
  - He writes: "Our main result provides a partial answer to Kishimoto's question and to [37, Problem LV]".
  - arXiv lists no journal reference.
- **STW v2** (8 May 2026) still lists LV with no addendum, and its acknowledgements thank Neagu.
- **Search.** The searches covered arXiv and the web: Problem LV, quasi-free flows on Cuntz algebras and their
  classification, Kishimoto's question, and the names Evans, Izumi and Bratteli–Kishimoto. No other work on this question
  or citing Problem LV turned up.

**Reading of LV.** In STW's normalization (first frequency 1), distinct values of `λ` have distinct `β`. `β` is an
invariant by facts STW cite ([262] and KMS theory). So the literal question is settled by a standard invariant, and "iff
`λ = μ`" is a one-line corollary, not the solution of an open problem.

Neagu reads LV as Kishimoto's completeness question for general `L`, which is the same as classification up to time
rescaling, and he calls a generic result a partial answer. The repository does not address that question. The late-band
audit calls the argument "repository-original", but it misses 2509.00829.

**Error in a scope note.**
- **Claim.** Lines 44–47 of research/artifacts/stw99-lv-quasifree-flow-solution-2026-08-30.md say the classification "up
  to rescaled cocycle conjugacy" is `{λ, 1/λ}`. The parenthetical in `o2-quasifree-flows-cocycle-conjugacy-classified`
  says the invariant classifies after rescaling.
- **Gap.** Rescaling time by `c` divides `β` by `c`. After rescaling, `β` carries no information, and no other invariant
  is given.
- **Contradiction.** As stated, Neagu's Theorem 3.12 contradicts the note generically. Take `λ, μ` in his generic set and
  `c = β(μ)/β(λ)`. Then `α^(1,λ)` and `α^(c,cμ)` have the same `β`, so they are cocycle conjugate, and
  `α^(c,cμ)_t = α^(μ)_{ct}`. The generic set is uncountable, so these rescaled classes are not `{λ, 1/λ}`.

## 4. Lean-cheapest faithful proof of the literal theorem
The Challenge needs only footnote 78 and the flows; KMS states stay inside the proof. This route avoids crossed products
by `R`, traces, von Neumann algebras and the Kishimoto–Kumjian uniqueness theorem.
1. **KMS equation** and strict monotonicity of `β`, as in §2(a),(b). Elementary.
2. **Existence** of a `β(λ)`-KMS state for `α^(λ)`: the product state on the UHF core composed with the gauge expectation.
3. **Smoothing the cocycle.** This step is elementary and I checked it for this review.
   - Let `w` be a norm-continuous `α`-cocycle. Take `f ≥ 0` smooth with `∫ f = 1` and support close to 0, and set
     `y = ∫ f(s) w_s ds`, with `‖y − 1‖ < 1/3`.
   - The cocycle identity gives `α_t(y) = w_t^* G(t)`, where `G(t) = ∫ f(s − t) w_s ds` is smooth. Hence
     `α_t(y^* y) = G(t)^* G(t)` is smooth too.
   - Put `v = y |y|^{-1}`. The cohomologous cocycle `w'_t = v^* w_t α_t(v) = v^* G(t) (G(t)^* G(t))^{-1/2}` is smooth.
     Since `‖G^* G − 1‖ < 1`, the inverse square root is a norm-convergent power series.
   - `Ad(w') α = Ad(v^*) ∘ Ad(w) α ∘ Ad(v)`.
   - Differentiating the cocycle identity gives `dw'_t/dt = w'_t α_t(ih)` with `h = h^* ∈ A`. So, up to an inner
     conjugacy, the exterior equivalence is the bounded perturbation `α^h`.
4. **Araki perturbation.** The β-KMS states of `α` and of `α^h` correspond (Bratteli–Robinson, vol. II, §5.4.1). In Lean
   this needs the Dyson series for α-entire `h`, Gaussian smoothing for general `h`, and a weak* limit of states.
5. **Assembly.**
   - The flow `γ = σ α^(λ) σ^{-1} = Ad(w) α^(μ)` has a `β(λ)`-KMS state.
   - By steps 3 and 4, so does `α^(μ)`.
   - By step 1, `β(λ) = β(μ)`, so `λ = μ`.

**Cost.** Step 1 is cheap; step 3 is cheap to medium; step 2 is medium; step 4 is the main cost. The repository's route
(crossed products by `R`, dual weights, Kishimoto–Kumjian) is heavier.

**Fidelity guards.** `O_2` must be the Cuntz algebra, and the flows must exist: a vacuous family proves anything. The
cocycle `w` is continuous and takes values in `U(O_2)`.

## 5. Consequences
- LV must not be packaged as a Palomar "Solution to STW Problem LV". The literal theorem may be formalized, but it is a
  corollary of the standard KMS invariant, not a new answer.
- Owners should correct four items: the root node's "ANSWERED" status, the claim "This answers STW Problem LV", the
  `{λ, 1/λ}` scope note, and the audit's originality note. This review edits no research node.
- What remains open is whether `β` classifies these flows for every irrational ratio. Neagu covers a dense set of second
  category.
