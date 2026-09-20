---
rg: 2
id: lambda-gapped-xor-sources-cannot-feed-sqrt-rate-repetition
kind: claim
title: Expanding XOR games repeat at rate sqrt(lambda) gamma / 54, but unless P = NP every hard lambda-gapped alphabet-2 source has sqrt(lambda) gamma <= 40.5 eta, so any repetition rate up to K gamma^2 + kappa sqrt(lambda) gamma certifies deficit ratio at most 2K gamma^2/eta + 81 kappa -- the sqrt-gap rate class is dead at alphabet 2
distinct_from:
  expansion-certified-repetition-caps-deficit-ratio: that kills rates up to K gamma^2 + kappa lambda gamma, for every alphabet, via the linear spectral gate lambda gamma <= 1592 eta; this kills the strictly larger class kappa sqrt(lambda) gamma, which the linear gate cannot touch (it only gives sqrt(lambda) gamma <= sqrt(1592 eta gamma)), but only for alphabet-2 sources, via the XOR Cheeger gate.
  xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration: that is the SDP inequality; this is its repetition and complexity consequence.
  akkstv-expansion-parallel-repetition-bound: that gives the rate lambda eps / log(1/eps) for every alphabet; item 1 here is the rate sqrt(lambda) gamma / 54 at alphabet 2, through the same Feige--Lovasz route.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that kills universal (expansion-free) repetition bounds via the odd cycle; this kills expansion-certified sqrt-gap bounds from alphabet-2 sources.
  sqrt-scale-unique-games-hardness: that is the open hole; this closes the alphabet-2 lambda-gapped repetition route to it and names the alphabet >= 3 survivor.
---

**ESTABLISHED (class kill, conditional on P != NP only through its
conclusion).** The proof is `lambda-gapped-xor-sources-sqrt-rate-proof`.

**Setting.** This is the setting of `expansion-certified-repetition-caps-deficit-ratio`:
λ-gapped sources `S = (η, γ, λ)`, repetition amplifiers with `ε' <= 1/2`, and
the certified deficit ratio `R = (1 − δ')/ε'`. The one restriction here is
that every instance of `S` has **alphabet 2**. Such instances are signed graphs
or Max-2LIN instances, and XOR games in the bipartite case. Only the source is
restricted; the repeated game `G^(⊗n)` has alphabet `2^n`.

* **Rate class `SqRate(K, κ)`.** Soundness is certified by
  `val(G^(⊗n)) <= (1 − ψ(λ, γ))^n` on NO instances, with
  `ψ(λ, γ) <= K γ² + κ sqrt(λ) γ`. Since `λ <= 2`, this contains `Rate(K, κ/sqrt 2)`
  and hence every rate killed in `expansion-certified-repetition-caps-deficit-ratio`.

**Theorem.**

1. *(The sqrt rate is real.)* Let `U` be a bipartite XOR game whose question
   graph has normalized spectral gap `λ > 0`, and let `opt(U) <= 1 − γ`. Then,
   for every `r >= 1`,
   `opt(U^(⊗r)) <= σ(U)^r <= (1 − sqrt(λ) γ/54)^r`. So `SqRate(0, 1/54)` is a
   valid certificate on alphabet-2 bipartite NO hosts. It improves the AKKSTV
   rate `λγ/log(1/γ)` at alphabet 2. The exponent `1/2` is the best that the
   Figure 1 route can give, by the odd-cycle tightness in
   `xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration`.
2. *(XOR source gate.)* Let `S` be a hard λ-gapped alphabet-2 source with
   `γ > 40.5 η/sqrt(λ)`. Then `P = NP`. Hence, under `P != NP`, every hard
   such source has `sqrt(λ) γ <= 40.5 η`.
3. *(Rate class.)* Assume `P != NP`, let `S` be a hard λ-gapped alphabet-2
   source, and take an `SqRate(K, κ)` amplifier on it. Then

   ```text
   1 − δ'  <=  2 ε' (K γ²/η + 40.5 κ),     so     R  <=  2K γ²/η + 81 κ .
   ```

   With `K = 0`, `R <= 81 κ`, uniformly in `η`, `λ` and `n`. In particular, the
   genuine rate of item 1 certifies `R <= 1.5` at the gate. Neither
   `sqrt-scale-unique-games-hardness`, which needs `R` unbounded, nor
   `unique-games-conjecture` is reachable this way.
4. *(Survivor.)* A repetition route to `sqrt-scale-unique-games-hardness` from
   a λ-gapped source with a pure expansion rate `κ sqrt(λ) γ` must use a source
   of **alphabet `k >= 3`**. The rate bound gives `R <= n κ sqrt(λ) γ/ε' <= 2κ sqrt(λ)γ/η`,
   so unbounded `R` needs `sqrt(λ) γ / η -> ∞`. Under `P != NP`, the gate `T_η`
   must still fail, so some NO hosts must have basic-SDP deficit at most `1.5 η`.
   The source must therefore contain λ-gapped integrality gaps with
   `δ_sdp / (sqrt(λ) γ) -> 0`. The first open question is whether a fixed-`k`
   XOR Cheeger inequality `δ_sdp >= c_k sqrt(λ) γ` holds for `k >= 3`. If it
   holds, the survivor dies at every fixed alphabet. Otherwise a λ-gapped
   integrality gap at fixed `k` with `δ_sdp = o(sqrt(λ) γ)` is the object to
   build.

**Remark (not used).** Khot–Vishnoi-type instances have `δ_sdp ≈ λ` and
`γ` near 1. This suggests `c_k -> 0`, at best of order `1/sqrt(log k)`, so the
survivor is alive for alphabets growing with the input. That regime is still
constrained by the linear gate of `expansion-certified-repetition-caps-deficit-ratio`.

**How this fits.** The linear gate `λγ <= 1592 η` killed rates `κλγ`. It left
the sqrt-gap rates `κ sqrt(λ) γ` alive. Spark `4ee60ca4` reports that
(λ,γ)-certified rates are capped at order `sqrt(λ) γ`; that cap is not used
here. Item
1 shows that such rates really occur at alphabet 2. Items 2–3 show that they are
still useless there, because the XOR Cheeger inequality turns the same `sqrt(λ)`
into a polynomial-time gate. The invariant is again `ψ/η` on hard sources. It
is bounded as soon as the soundness certificate is dominated by a
polynomial-time SDP deficit.
