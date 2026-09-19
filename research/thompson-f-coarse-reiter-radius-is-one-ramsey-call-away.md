---
rg: 2
id: thompson-f-coarse-reiter-radius-is-one-ramsey-call-away
kind: claim
title: In Thompson's F one 1/2-Ramsey call at an exponential window yields a coarsely invariant measure, so the coarse Reiter radius is elementary in the Ramsey radius, AMP holds, and ¬AMP, RGAP₁ and RGAP₂ are all false
distinct_from:
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that proves the sandwich RGAP₂ ⇒ ¬AMP ⇒ RGAP₁ and leaves all three open; this proves CR(M) ≤ A·R(A·6^{556M²}) + A·M², which refutes all three.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, open until now; this refutes it by proving AMP(D) for some fixed D.
  thompson-f-ramsey-radius-double-gap-below-reiter-radius: that is RGAP₂; this refutes it.
  thompson-f-ramsey-function-iterates-reach-towers: that proves the fork AMP(D) ⇒ R not elementary; this supplies AMP(D), so R_F is not elementary without any hypothesis.
  coarse-ball-invariance-gives-fine-reiter-measures: that is spectral smoothing of one given measure; this produces the coarse measure from Ramsey sets, which is the quantifier swap that the smoothing lemma cannot do.
---

**ESTABLISHED** by `thompson-f-coarse-reiter-radius-is-one-ramsey-call-away-proof`. It is a direct proof from
`moore-ramsey-criterion-for-amenability` (definitions), `coarse-ball-invariance-gives-fine-reiter-measures`
(rerun at threshold 3/2), `thompson-f-word-length-is-comparable-to-caret-count`, the sandwich
`thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap` and Proposition D of
`thompson-f-ramsey-function-iterates-reach-towers`. It has not been independently reviewed.

**Setting.** `S = {x_0, x_1}`, balls `B_r` are taken in the word metric of `S ∪ S⁻¹`, `R = R_{F,S}` is Moore's
Ramsey function (`R(m)` is the least `n` with `B_n` 1/2-Ramsey with respect to `B_m`), and
`CR(M) = min{ r : some ν ∈ P(B_r) has ‖gν − ν‖₁ ≤ 1 for all g ∈ B_M }`. Values lie in `[0, ∞]`.

**Theorem (one Ramsey call gives one coarse measure).** There is a constant `A ≥ 2`, depending only on `(F, S)`,
such that for every `M ≥ 1`

`CR(M) ≤ A·R(A·6^{556M²}) + A·M²`.

**Corollaries.**
1. *CRE holds.* There is an `E` with `CR(N) ≤ exp_E(R(exp_E(N)))` for all `N ≥ 1`.
2. *AMP holds, so ¬AMP is false.* By Corollary 1 of the sandwich, AMP(E+3) holds:
   `R̃(m, 1/u) ≤ exp_{E+3}(R(exp_{E+3}(m+u)) + u)` for all `m, u ≥ 1`. So
   `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead` is **false**.
3. *Both gaps are false.* RGAP₁ is the negation of "CRE(E) for some E", so it is false. RGAP₂ implies ¬AMP, so it is
   false too. The routes `thompson-f-amenable-via-costly-ramsey-amplification` and
   `thompson-f-costly-amplification-via-double-ramsey-reiter-gap` are **dead**. Their open prerequisite is refuted, not
   just unproved.
4. *Moore's moderate-rate hope fails.* By Proposition D, for every `q` there is an `m` with `R(m) > exp_q(m)`. This
   holds with no hypothesis: if `F` is not amenable then `R` is infinite from some point on. So 1/2-Ramsey balls of
   `F` do not have elementary radii, and they are exactly as expensive as coarse Reiter measures up to a bounded
   tower.

**The mechanism (why the known kills do not apply).**
- *Minimax first, Ramsey second.* By the finite minimax theorem, `CR_{3/2}(M) > n'` has a certificate: weights
  `p_g` on `B_M` and functions `f_g : F → [0,1]` with `Σ_g p_g (f_g(gx) − f_g(x)) > 3/4` on `B_{n'}`. The
  certificate uses only `K = |B_M| − 1` functions, one per group element, however large `n'` is. So it is enough to
  defeat each fixed certificate with some measure, and that measure may depend on the certificate.
- *One set codes the certificate.* In `V = (F ≀ Z) × Z ≤ F`, the wreath coordinates `y_k` live on the disjoint
  dyadic intervals `x_0^k([1/8, 1/4])`, the shift is `x_0` rescaled to `[0, 1/2]`, and the extra `Z` is `x_1`. The
  set is `{w·x_1^t : Σ_i p_i f_i(y_i(w)) > (t mod 8 + 1/2)/8}`. The test measures are the uniform averages of
  `x_1^r σ^j a_j` and of `x_1^r σ^j` over `r < 8` and `j < 16K`, where `a_j` puts `g_i` on coordinate `i − j`.
- *The shift kills the selector death.* The w9 kill on `thompson-f-ramsey-radius-double-gap-below-reiter-radius`
  says that a coded coloring only controls a family of conditional marginals `ν_i`, one per coloring. Here each
  test function `f_i` is read on every coordinate `i − j`, `j < 16K`. So balancing the one set controls
  `Σ_i p_i (gν̄(f_i) − ν̄(f_i))` for the single averaged marginal `ν̄ = (1/16K) Σ_{j<16K} (y_{−j})_*ν`, up to
  an error `1/8`. The threshold coordinate costs another `1/8`.
- *Coordinates are undistorted.* A coordinate `y_k` of an element of `V` of length `r` has length `O(r)`. The shift
  exponents are read off the slopes at `0` and `1/2`, and restricting to a dyadic interval that is mapped to itself adds
  no carets. So `ν̄` lives in a ball of radius `O(R(m))`, where `m = O(|B_M|·M)`.
- *Distinct from the killed classes.* The w9 window-preserving class kill (`F_2` has `R(1) = 3` and `CR(1) = ∞`) is
  respected. The argument is `F`-specific, because it needs `(F ≀ Z) × Z ≤ F` with linear coordinate distortion, and it
  moves the window from `M` to about `5^M·M`. The earlier translation and product codings died because the witness
  could treat colorings or trials separately. Here the minimax removes the need to treat them separately, and the shift
  forces a common marginal.

**What changes in the graph.** The last non-root-equivalent analytic route through Moore's Ramsey functions is
closed. `R_F`, `R̃_F`, `F_{F,S}` and `CR_F` are all equivalent up to bounded towers. Each of them is elementary iff the
Følner function is, and the Følner function is not (Moore). So every Ramsey-type route to `thompson-f-is-amenable` is
now quantitatively the Følner problem, as the inverted-orbit route already was
(`f-dyadic-confinement-witness-times-match-folner-function`).

**Remark (general form).** The proof uses only this about `F`. `F` contains `(F ≀ Z) × Z`, the wreath coordinates and
the two `Z` exponents of an element of length `r` have length `O(r + 1)`, and the test elements have length
`O(K(M+1))`. Any finitely generated group with such a self-wreath embedding satisfies the same theorem, with
constants depending on the embedding.
