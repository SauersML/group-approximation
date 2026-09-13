# The reduced C*-algebra face of the paradox/measure dichotomy

Lane `un-reduced-cstar`, 2026-09-13. Part 1 of 1. Status: my own derivations, unreviewed. Load-bearing
inputs are nodes already on main, each named where it is used.

## 0. Summary

- **(a) Paradox side, decided.** Let `𝒢` be an ample Hausdorff second countable groupoid with compact unit space
  `X` and no invariant probability measure, `k` a countable field, `R = A_k(𝒢)`. For `N ≥ 2n` (the rank threshold
  of `no-invariant-measure-steinberg-elementary-no-mf-quotient`) and every nontrivial quotient `Q` of `EL_N(R)`,
  `C*_r(Q)` is separable, stably finite and not MF, and `C*_max(Q)` is not MF. This covers the boundary-action group
  `S_∂`, whose reduced algebra also has a unique trace. Node `measure-free-steinberg-el-n-reduced-cstar-not-mf`.
- **(b) Measure side, not decided. Three firewalls, established:**
  1. Infinite simple groups such as Pestov's `S` have no nontrivial finite-dimensional unitary representations, so
     they are not purely matricial field (PMF). Any MF embedding of `C*_r(S)` must use genuinely non-exact
     asymptotic representations. Node `minimally-almost-periodic-groups-are-not-pmf`.
  2. Every representation of the ring-induced LEF models that contains a permutation module on unimodular columns
     has an exactly invariant vector for the images of a non-amenable stabilizer subgroup. This includes the regular
     representation and its part orthogonal to the constants. So those models never converge strongly.
     Node `ring-model-permutation-vectors-block-strong-convergence`.
  3. Weak convergence gives the lower bound for free, and with a unique trace, any MF embedding is tracially
     faithful. What is missing is exactly an upper bound, "no outliers" (§2.4).
- **(c) Operator-algebra form.** Necessity holds: reduced MF in infinitely many ranks forces an invariant measure.
  Sufficiency implies the famous open root `infinite-kazhdan-group-with-mf-reduced-cstar`. Open claim
  `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure`, with a live route into that root.

## 1. Paradox side

**Theorem 1.** Let `𝒢`, `X`, `k` and `R` be as in §0, and assume `X` carries no `𝒢`-invariant Borel probability
measure. Choose `n ≥ 1` with `2n[1] ≤ n[1]` in `V(R)`. For every `N ≥ 2n` and every nontrivial quotient `Q` of
`EL_N(R)` (for instance `EL_N(R)` itself, or `EL_N(R)/Z(EL_N(R))`):
1. every homomorphism from `Q` to an MF group is trivial, so `Q` is not MF;
2. `C*_r(Q)` is separable, stably finite and not MF;
3. `C*_max(Q)` is not MF.

*Proof.*
- **Step 1.** By `no-invariant-measure-steinberg-elementary-no-mf-quotient` (item 2), every homomorphism
  `EL_N(R) → M` with `M` MF is trivial. A homomorphism `Q → M` composed with `EL_N(R) → Q` is therefore trivial, so
  `Q → M` is trivial. Since `Q ≠ 1`, `Q` is not MF.
- **Step 2.** Manuscript Lemma `prop:mf-residual-calculus` (`non_mf_groups_exist.tex` l.361), quoted: "Let $A$ be a
  unital $C^*$-algebra and let $\pi\colon G\to\U(A)$ be an injective group homomorphism. If $A$ embeds in a norm
  matrix corona, then $G$ is MF. In particular, this applies to the canonical group homomorphisms into
  $\U(C^*_{\max}(G))$ and $\U(C^*_{\mathrm r}(G))$." Apply it with `G = Q`. By Step 1, neither `C*_r(Q)` nor
  `C*_max(Q)` embeds in a norm matrix corona.
- **Step 3.** `k` is countable and `𝒢` second countable, so `A_k(𝒢)` and hence `Q` are countable, and `C*_r(Q)` is
  separable. The canonical trace is faithful on `C*_r(Q)`, so `C*_r(Q)` is stably finite. This is the argument of
  manuscript Cor l.1038. ∎

**Corollary 2 (the paradoxical mirror of Pestov's group).** Let `S_∂ = EL_N(LC(∂F_d,k)⋊F_d)/Z` with `N ≥ 3`.
- By `boundary-action-elementary-simple-kazhdan-not-mf`, `S_∂` is infinite, finitely generated, simple and Kazhdan.
- `C*_r(S_∂)` is separable, stably finite, not MF, and has a unique tracial state.
- Unique trace: `S_∂` is simple, infinite and non-amenable (it is infinite with (T)), so its amenable radical is
  trivial. By `bkko-reduced-traces-concentrate-on-amenable-radical` (BKKO Thm 4.1), every tracial state `τ` on
  `C*_r(S_∂)` has `τ(λ_s) = 0` for `s ≠ e`. So `τ` is the canonical trace.

**Corollary 3 (necessity in (c)).** With `𝒢`, `k` and `R` as above but with no measure hypothesis: if `C*_r(EL_N(R))`
is MF for infinitely many `N`, then `X` carries a `𝒢`-invariant probability measure. This is the contrapositive of
Theorem 1, applied to `Q = EL_N(R)` with `N ≥ 2n`.

**Model tests.**
- Cuntz groupoid (`R = L_k(1,2)`): `n = 1`, and Theorem 1 recovers manuscript Cor l.1038 for `EL_N`, `N ≥ 2`.
- Minimal ℤ-subshift (Pestov ring): there is an invariant measure, so Theorem 1 says nothing. That is consistent
  with §2, where the question stays open.

## 2. Measure side: what can and cannot give MF of `C*_r(S)`

Here `S = EL_3(LC(X,F_q)⋊ℤ)/Z` for an infinite minimal subshift, or more generally `EL_N(A_k(𝒢))/Z` for `k`
finite and `A_k(𝒢)` finitely generated and matricial. MF of `C*_r(S)` means an injective *-homomorphism into
`∏_i M_{d_i}/⊕_i M_{d_i}`. Lifting the unitaries `λ_g` gives operator-norm asymptotic representations `V_i` with
`‖V_i(z)‖ → ‖λ_S(z)‖` for every `z ∈ ℂ[S]`.

### 2.1 No genuine representations (PMF is impossible)

**Proposition 4.** Let `Γ` be a nontrivial group such that every homomorphism `Γ → U(d)`, for every `d`, is
trivial. Then no sequence of finite-dimensional unitary representations converges strongly to `λ_Γ`.
- In the language of Magee–de la Salle (arXiv:2312.03220v2, Def. 1.2, quoted in
  `research/artifacts/mf-kazhdan-cstar-literature-status-2026-09-12.md`), `Γ` is not PMF.
- Every infinite finitely generated group with no nontrivial finite quotient has this property.
- *Proof.* Take `g ≠ e` and `z = 1 − g`. Every `ρ_i` is trivial, so `‖ρ_i(z)‖ = 0`. But `λ_g ≠ 1`, so
  `‖λ_Γ(z)‖ > 0`. For the second sentence: the image `ρ(Γ) ≤ U(d) ⊆ GL_d(ℂ)` is a finitely generated linear group,
  hence residually finite (Malcev, recalled). A nontrivial image would give `Γ` a nontrivial finite quotient. ∎
- **Application.** Take `G = EL_N(A_k(𝒢))` with `k` finite, `A_k(𝒢)` finitely generated, and 𝒢 as in
  `steinberg-elementary-groups-are-simple-mod-centre` (reviewed PASS, 171f0f7525).
  - `G` is infinite with finite centre `Z ⊆ k^× I`, and every normal subgroup is central or all of `G`.
  - A finite quotient `G/M ≠ 1` forces `M` central, and then `G/M` would be infinite, which is absurd.
  - So `G` and `G/Z` are not PMF. This includes Pestov's `S`, its ambient `G`, and `S_∂`.
- **Consequence.** Every MF approximation of `C*_r(S)` is an asymptotic representation that is far from every
  genuine one. So `S` fails operator-norm Ulam stability in the strongest sense.

### 2.2 The lower bound is automatic

**Proposition 5 (standard).** Let `V_i: Γ → U(d_i)` be operator-norm asymptotic representations with
`tr_{d_i}(V_i(g)) → τ_Γ(g)` for every `g`. Then `liminf_i ‖V_i(z)‖ ≥ ‖λ_Γ(z)‖` for every `z ∈ ℂ[Γ]`.
- *Proof.* Put `a = z*z`. Operator-norm asymptotic multiplicativity gives `‖V_i(z)*V_i(z) − V_i(a)‖ → 0` and
  `tr(V_i(a)^m) → τ(a^m)` for each `m`. So `‖V_i(z)‖^{2m} ≥ tr(V_i(z)*V_i(z))^m`, and the right side tends to
  `τ(a^m)`, for each fixed `m`.
- Since `τ` is faithful on `C*_r(Γ)`, `τ(a^m)^{1/m} → ‖λ(a)‖ = ‖λ(z)‖²`. ∎
- LEF models `σ_i` composed with the regular representations `λ_{F_i}` satisfy the trace hypothesis, since
  `σ_i` is injective on the window. The whole difficulty of strong convergence is the upper bound.

**Remark 6 (MF embeddings are tracially faithful).**
- Let `Φ` be an MF embedding of `C*_r(Γ)` with `Γ` of trivial amenable radical. After cutting down by the lifted
  projection `Φ(1)`, assume `Φ` is unital.
- Then `tr_ω∘Φ` is a tracial state on `C*_r(Γ)`, hence `τ_Γ` by BKKO Thm 4.1.
- So the lifted `V_i` satisfy `tr(V_i(g)) → δ_{g,e}` along `ω`: every MF model of `C*_r(S)` is also a
  hyperlinear model.

### 2.3 Stabilizer vectors block ring-induced models

**Proposition 7.** Let `P_0 ≤ Γ` be generated by a finite symmetric set `K` and non-amenable, and put
`h_K = |K|^{-1} Σ_{s∈K} s`. Let `V_i` be operator-norm asymptotic representations of `Γ` that have unit vectors `ξ_i`
with `‖V_i(s)ξ_i − ξ_i‖ → 0` for every `s ∈ K`. Then `(V_i)` does not converge strongly to `λ_Γ`.
- *Proof.* `‖V_i(h_K)‖ ≥ ⟨V_i(h_K)ξ_i, ξ_i⟩ → 1`.
- `λ_Γ` restricted to `P_0` is a multiple of `λ_{P_0}`, so `‖λ_Γ(h_K)‖ = ‖λ_{P_0}(h_K)‖ < 1` (Kesten). ∎

**Application to ring-induced models.**
- **Setting.** `R` is exactly matricial: unital maps `σ_i: R → M_{N_i}(F_i)` over finite fields that are injective
  and multiplicative on windows exhausting `R` (`exactly-matricial-rings-have-lef-general-linear-groups`).
  `G = EL_n(R)` with `n ≥ 3`, and `F_i` is the finite group generated by `σ_i(window) ⊆ GL_n(M_{N_i}(F_i))`.
- **Invariant vector.** Let `c_i = (1,0,…,0)^T ∈ M_{N_i}(F_i)^n`. If `p ∈ G` fixes `e_1 ∈ R^n`, its first column is
  `e_1`, so `σ_i(p)c_i = c_i` exactly once `p` is in the window.
- **Non-trivial vector.** The permutation module `ℓ²(F_i c_i) ≅ ℓ²(F_i/H_i)` sits inside `λ_{F_i}`, and its
  constants are the constants of `ℓ²(F_i)`. So `ξ_i = δ_{c_i} − mean`, normalized, lies in `ℓ²_0(F_i)`.
  - `ξ_i` is exactly `σ_i(p)`-invariant.
  - `|F_i c_i| ≥ |σ_i(window)| → ∞`, so the normalization is harmless.
- **Non-amenable stabilizer.** `Stab_G(e_1) ⊇ EL_{n−1}(R)` on coordinates `2,…,n`.
  - For `n ≥ 4` and `R` finitely generated it is infinite and Kazhdan (EJZ), hence non-amenable.
  - For Pestov's ring and `n = 3`: the shift `u` generates `F_q[u] ≅ F_q[t]` (crossed-product normal form), and
    `E_2(F_q[t]) = SL_2(F_q[t])` contains a free subgroup of rank 2 (Nagao amalgam, recalled). Take `K` generating
    that free subgroup.
- **Conclusion.** For every representation `π_i` of `F_i` containing the nontrivial part of the permutation module on
  unimodular columns (in particular `λ_{F_i}` and `λ^0_{F_i}`), `π_i∘σ_i` never converges strongly to `λ_G`.
- **For `S = G/Z`.** `P_0 ∩ Z = 1`, and the same argument works with columns taken modulo `F_i^×`.

This is the Magee–de la Salle mechanism (their Thm 1.1 and Cor 1.3 for `SL_4(ℤ)`, invariant vectors for a
non-amenable subgroup), transplanted from genuine representations to ring-induced asymptotic ones.

### 2.4 What remains for MF of `C*_r(S)`

Any MF model must satisfy all three conditions at once:
- it is not a representation (Prop. 4);
- its normalized traces tend to `δ_e` (Rem. 6);
- it has no almost invariant vectors for any non-amenable subgroup `P_0` beyond those `λ_S` has (Prop. 7).

A natural candidate (heuristic, unverified) is to take, inside `F_i ⊆ SL_{nN_i}(F_i)`, irreducible representations
with no vectors invariant under the images of the ring stabilizers ("cuspidal type", compare Deligne's example for
`SL_3(F_q)` in Magee–de la Salle Ex. 2.2). Their normalized characters on `σ_i(g)`, `g ≠ e`, should tend to 0 by
character bounds for groups of Lie type (Bezrukavnikov–Liebeck–Shalev–Tiep, recalled).

The missing step is a deterministic no-outlier theorem. The random-permutation method applies only to free
groups. Bordenave–Collins, arXiv:1801.00876, abstract (fetched on MSI 2026-09-13): "Consider a finite sequence of
independent random permutations, chosen uniformly either among all permutations or among all matchings on n points.
We show that, in probability, as n goes to infinity, these permutations viewed as operators on the (n-1) dimensional
vector space orthogonal to the vector with all coordinates equal to 1, are asymptotically strongly free." A Kazhdan
group has no randomness to exploit. van Handel's survey (arXiv:2510.12520 §2.2, quoted in the literature-status
artifact) records deterministic strong convergence as "very much open".

## 3. The operator-algebra form (c)

Take `F_r ↷ X` minimal and topologically free, with `R = LC(X,F_q)⋊F_r` finitely generated.
- **(⇒, established):** Corollary 3.
- **(⇐, open):** if `X` has an invariant measure, is `C*_r(EL_N(R)/Z)` MF for all large `N`? For `r = 1` and `X` a
  minimal subshift this would give an infinite Kazhdan group with MF reduced algebra, the open root
  `infinite-kazhdan-group-with-mf-reduced-cstar`. So (⇐) is at least as hard as that root.
- **The C*-level picture.**
  - Both `C*_r(S)` and `C*_r(S_∂)` are separable, stably finite, with unique trace (the invariants computed here).
  - The paradoxical one is not MF; the measured one is undecided.
  - Tracial and stable-finiteness invariants cannot see the dichotomy at the reduced level. Only MF, or corona
    traces on `C*_max` (un-traces), separate the two sides.

## 4. Credits and bounds

- **Credits.** Theorem 1 is manuscript Cor l.1038's argument applied to un-paradox's groupoid theorem, crediting
  un-paradox and un-middle. The PMF definition and the invariant-vector obstruction are Magee–de la Salle's.
  BKKO for unique trace. Kesten; Malcev and Nagao recalled.
- **Not re-read.** Magee–de la Salle and van Handel were not re-read by this lane; I used the quotes in
  `mf-kazhdan-cstar-literature-status-2026-09-12.md`, read from the PDFs by lane ex-mf-kazhdan-cstar. Bordenave–Collins
  abstract only.
- **Not done.** No web search. No computation.
