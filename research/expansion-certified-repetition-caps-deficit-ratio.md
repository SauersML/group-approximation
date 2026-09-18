---
rg: 2
id: expansion-certified-repetition-caps-deficit-ratio
kind: claim
title: Unless P = NP, a parallel-repetition amplifier whose per-round soundness rate is at most K gamma^2 + kappa lambda gamma on NO hosts of spectral gap lambda certifies deficit ratio at most 2K gamma^2/eta + 3184 kappa, and one certified through any polynomial-time multiplicative value bound certifies an empty gap; so expansion-certified repetition (AKKSTV Theorem 4.3 included) cannot reach sqrt-scale UG hardness or UGC from any source short of sqrt-scale
distinct_from:
  black-box-repetition-needs-sqrt-scale-soundness-gap: that kills repetition amplifiers certified by a universal bound, through the odd cycle and with no complexity assumption; this kills the expansion-certified survivor it names, through the spectral-gap rounding and P != NP. Its universal quadratic rates reappear here only as the K gamma^2 term.
  spectral-gap-no-outputs-cannot-prove-ugc: that kills reductions whose NO outputs have few near-1 constraint eigenvalues, at the output; this uses its r = 1 rounding on the NO sources of a repetition step, to cap the soundness rate the amplifier can certify.
  unique-games-on-expanding-constraint-graphs-are-easy: that is the AKKSTV rounding algorithm; this is a class kill on amplification arguments, and uses the linear (log-free) rounding of the spectral node instead.
  akkstv-expansion-parallel-repetition-bound: that is the expansion-dependent repetition bound itself; this proves that on NP-hard NO sources that bound, and every bound of its rate shape, yields only bounded deficit ratio.
  ug-hardness-deficit-ratio-padding-line: that defines the deficit ratio R and caps padded proper splits at R <= 2; this caps a different class, repetition with expansion-certified soundness, at R <= 3184 kappa (pure expansion rates) and at R <= 1 (computable multiplicative certificates).
  sqrt-scale-unique-games-hardness: that is the open hole; this kills one class of routes to it and names the rate condition any surviving repetition route must meet.
  sqrt-scale-unique-games-hardness-is-equivalent-to-ugc: that proves sqrt-scale sources suffice for UGC through a universal bound; this proves expansion does not replace the sqrt-scale source.
  parallel-repetition-collapses-threshold-rank-to-spectral-gap: that tracks the output spectrum of a repetition; this bounds the certified output value from the source spectrum.
artifacts:
  - experiments/ugc-expansion-repetition-2026-09-17/check_rate_class_bounds.py
  - experiments/ugc-expansion-repetition-2026-09-17/output.txt
---

**ESTABLISHED (class kill, conditional on P != NP only through its conclusion).**
The proof is `expansion-certified-repetition-caps-deficit-ratio-proof`.

**Setting.** Unique games are as in `spectral-gap-no-outputs-cannot-prove-ugc`.
They are weighted, have no isolated vertices, and have constraint walk `A`, which
is self-adjoint in `L2(π)`. For `λ in (0, 2]`, a game is **λ-gapped** if `A`
has at most one eigenvalue `> 1 − λ`. For bipartite games this is the condition
"`λ_2` of the normalized Laplacian of the question graph is `>= λ`".

A **λ-gapped source** `S = (η, γ, λ)` is the promise problem
`Gap-UG[1 − η, 1 − γ]` in which every NO instance is λ-gapped. YES instances
are unrestricted, and alphabets may grow with the input. `S` is **hard** if it
is NP-hard under polynomial-time many-one reductions.

A **repetition amplifier** on `S` with `n` rounds maps `G ↦ G^(⊗n)`. It
certifies completeness by product strategies, so the output completeness is
`1 − ε'` with `ε' := 1 − (1 − η)^n`, and it is required that `ε' <= 1/2`. Its
**certified soundness** `δ'` is a number with `val(G^(⊗n)) <= δ'` for every NO
instance `G` of `S`. The certified deficit ratio is
`R = (1 − δ')/ε'`, as in `ug-hardness-deficit-ratio-padding-line`.

* **Rate class `Rate(K, κ)`.** Soundness is certified by a rate function
  `ψ : (0,2] × (0,1] → [0,1]`, through `val(G^(⊗n)) <= (1 − ψ(λ, γ))^n`, with
  `δ' = (1 − ψ(λ, γ))^n`, where

  ```text
  ψ(λ, γ)  <=  K γ^2 + κ λ γ        for all λ, γ    (K, κ >= 0 constants).
  ```

* **Certificate class `Cert`.** There is a map `β` from games to `[0,1]` such
  that:
  - `val(G^(⊗m)) <= β(G)^m` for all `m >= 1`, and in particular `β >= val`;
  - for every rational `τ > 0`, `β(G)` can be computed to additive error `τ`
    in time polynomial in `|G|`.

  Soundness is certified as `δ' = (sup_(G NO in S) β(G))^n`.

**Theorem.**

1. *(Source gate.)* If `S = (η, γ, λ)` is hard and `γ > 1536 η/λ + 28 η`,
   then `P = NP`. Since `λ <= 2`, a hard λ-gapped source with `P != NP`
   satisfies `λ γ <= 1592 η`.
2. *(Rate class.)* Assume `P != NP`. Let `S` be hard, and take a `Rate(K, κ)`
   amplifier on `S` with `ε' <= 1/2`. Then

   ```text
   1 − δ'  <=  2 ε' ( K γ^2/η + 1592 κ ),    so    R  <=  2 K γ^2/η + 3184 κ .
   ```

3. *(Pure expansion rates.)* For `K = 0`, `R <= 3184 κ`. This holds for every
   `η`, `λ`, `n` and alphabet. Such amplifiers therefore never certify
   `Gap-UG[1 − ε', 1 − C'·sqrt(ε')]` with `C' > 3184 κ sqrt(ε')`, and never
   `Gap-UG[1 − ε', ε']` with `ε' < 1/(3184 κ + 1)`. For every fixed `κ` they
   reach neither `sqrt-scale-unique-games-hardness` nor
   `unique-games-conjecture`. For `κ < 1/1592` they do not even cross the
   padding line `R = 2`.
4. *(Mixed rates are circular.)* Suppose a `Rate(K, κ)` amplifier certifies
   `R >= R* > 3184 κ`, with `K > 0`. Then the source satisfies
   `γ >= C sqrt(η)`, where `C = sqrt((R* − 3184 κ)/(2K))`, and its NO hosts
   have `λ <= 1592 sqrt(η)/C`. So the source is already a sqrt-scale hard
   point, with the constant `C` growing like `sqrt(R*)`. It is also restricted
   to NO hosts of gap `O(sqrt(η))`, so it implies the hardness asked for in
   `sqrt-scale-unique-games-hardness` at that `C`. Such an amplifier cannot
   derive sqrt-scale hardness from anything weaker than sqrt-scale hardness.
5. *(Certificate class.)* Assume `P != NP`. Let `S` be hard. Then
   `sup_(NO) β >= 1 − η`, so every `Cert` amplifier has
   `δ' >= (1 − η)^n = 1 − ε'`. The certified gap is empty, whatever the host
   expansion and whatever `n`.
6. *(Members.)*
   - **AKKSTV Theorem 4.3.** `akkstv-expansion-parallel-repetition-bound` is
     read as the rate `ψ_A(λ, γ) = c_R λ γ0/ln(1/γ0)` with
     `γ0 = min(γ, 1/e)`. This rate is certified on every NO instance, since
     `val <= 1 − γ` implies `val <= 1 − γ0`. It satisfies `ψ_A <= c_R λ γ`.
     So it lies in `Rate(0, c_R)`, and item 3 caps it at `R <= 3184 c_R`.
   - **Its own proof route.** That proof goes through the Feige--Lovász `σ`.
     So it also lies in `Cert` whenever `σ` is computable to fixed additive
     precision in polynomial time. That solvability is standard, but it is not
     imported here. The kill of this member rests on item 3, not on item 5.
   - **Linear-rate bounds.** Every "strong repetition on expanders" bound with
     per-round rate `O(poly(λ)·γ)` and polynomial degree at least 1 lies in
     `Rate(0, κ)`. Every universal quadratic rate `O(γ^2)` lies in
     `Rate(K, 0)`; these are Rao and Dinur--Steurer type rates, and item 4
     reduces them to the existing black-box kill.

**Invariant and death step.** The invariant is the **normalized certified
rate** `ψ/η`. The certified output ratio is at most `2ψ/η`, because `n` rounds
cost `nη <= 2ε'` in completeness. On the NO side of a hard source, the
spectral-gap rounding forces `λγ <= 1592 η`. So any rate linear in `λγ` has
`ψ/η = O(1)`. Every member dies at the **soundness-certification step**: on
NP-hard NO sources, the expansion that the certificate uses is exactly as
strong as the source's own deficit allows. The certificate class dies earlier.
Its certificate would itself decide the source.

**Survivors, which form the new decomposition.** A repetition route to
`sqrt-scale-unique-games-hardness` from a sub-sqrt source must certify a rate
`ψ(λ, γ)` that satisfies `ψ/η → ∞` on hard λ-gapped sources with
`λγ <= 1592 η` and `γ = o(sqrt(η))`. This means one of the following:

* **(P1)** hardness of some λ-gapped source `(η, γ, λ)`; and
* **(P2)** a parallel-repetition rate for unique games on λ-gapped NO hosts
  that is **superlinear in `λγ` and superquadratic in `γ` at once**. An example
  is `ψ >= ω(λγ + γ^2)` in the regime `γ^2 << λ`, such as `ψ ~ sqrt(λ)·γ`.

The two can fail independently. (P2) is a purely combinatorial statement about
repeated values, with no complexity content. The odd cycle
(`raz-odd-cycle-repetition-lower-bound`) does not refute (P2): its `λ ~ γ^2` sits
at the boundary of the regime. Other routes also escape this kill:

* soundness analyses that use more structure than `(λ, γ)`, such as
  small-set expansion or threshold-rank profiles;
* amplifiers whose completeness is not the product bound;
* non-repetition amplifiers.
