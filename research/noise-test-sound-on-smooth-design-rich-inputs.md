---
rg: 2
id: noise-test-sound-on-smooth-design-rich-inputs
kind: claim
title: The Braverman--Khot--Minzer reduction stays sound when richness is weakened to a smooth low-degree pairing design
distinct_from:
  rich-2to1-conjecture-is-equivalent-to-ugc: that is the published equivalence for fully rich instances; this identifies the two properties of the pairing distribution the soundness proof uses and shows any family with both suffices.
  separated-small-pairing-families-defeat-the-noise-test: that is the obstruction for small separated families; this is the positive transfer for families that are designs of strength 8d+1 with the pull-back density comparison, which by pullback-smoothness-needs-exponentially-many-pairings are always exponentially large.
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

**ESTABLISHED (transfer of a published proof).** Call a family `F` of perfect
pairings of `[2n]` **`t`-wise uniform** when every partial matching with at most
`t` pairs lies in a random member of `F` with the same probability as in a
uniform perfect matching. Call it **`(K,m,C_0)`-smooth** when the pull-back
distribution `nu_(F,m)` has density at most `C_0 m^(-2n)` at every `K`-roughly
balanced point.

Fix the parameters `m, delta, zeta, d` of BKM's main analytic lemma (ECCC
TR19-141, Lemma 3.1) and `C_0 >= 1`. For `n` large, the lemma's conclusion holds
for `pi` drawn from any `(8d+1)`-wise uniform, `(K,m,C_0)`-smooth family, with
uniformly random right labels. Its high-degree threshold `gamma` also depends
on `C_0`. Consequently their Section 5 soundness argument applies verbatim to
2-to-1 instances whose pairing family at every left vertex has these two
properties.

The proof audits every use of uniformity: degree-`2d` and degree-`8d`
expectations in Lemmas 4.6, 4.9 and 4.10, which a design matches exactly, and
the density comparison in Lemma 4.12, which smoothness supplies. All other
lemmas concern `f` alone or the uniform measure alone. Richness is not used in
completeness or folding.

This is a transfer: BKM's lemmas are imported, not reproved.

## Attempts

* **Belief-breaking audit against the verbatim text (2026-09-19, calibration;
  no gap found).** The aim was a use of uniform pairings in ECCC TR19-141 (full
  version, pypdf extraction) that neither design moments nor smoothness
  covers. Each passage was reread with that question in mind:
  - **Appendix C.** For "any 2-to-1 map pi", folding of `G = T_(1-eps) F`
    passes to `H = G|_pi`, so `E[h_r] = 1/m`. The same holds for every
    member of any family. This is the "subtle point" behind
    `E[g_(u,v)] = 1/m` in 5.2. It is needed because the pull-back measure is
    not uniform, and it uses no richness.
  - **Section 5.2.** Lemma 3.1 is used once. The bad event is "`I_j[g_(u,v)] > delta/2`
    for some `j` but no `i in pi^(-1)(j)` has `I_i[g_u] > tau`". It is a
    property of the single edge `(u,v)` and is invariant under right
    relabelling. So a per-left-vertex family bound, averaged over edges,
    gives the stated `zeta`. Theorem 2.6 applies to `h_v` alone.
  - **Lemma 4.12.** `q = f 1_(E^c)` is bounded by `f <= 1`, so its mass is
    `Pr_x[imbalanced]`, which does not depend on the family. The only
    pointwise-density step is "one can 'switch' to uniform distribution over
    input thanks to Lemma 4.2" for `h = f^(>d) 1_E`. This is exactly
    `(K,m,C_0)`-smoothness.
  - **Lemmas 4.8, 4.9 and Theorem 2.13.** Pseudo-randomness under
    `pi(A)=B` and the fourth-moment bound
    `E_pi[G^4] <= C(d,m) E_pi[G]^4` are proved for the uniform conditioned
    measure only. The design inherits the final inequality through
    `E[G^4]` and `E[G]`. It never needs pseudo-randomness of its own, so the
    conditionings on `|A| = 4d*` coordinates are not a design-strength cost.
  - **Lemma 4.10.** The step "for any `j` and any `i != i'`,
    `Pr_(pi:pi(i)=pi(i')=j)`" conditions `F` on containing `{i,i'}`. A
    `t`-wise uniform family stays `(t-1)`-wise uniform under that
    conditioning.
* **Bookkeeping correction, harmless.** The artifact says that averaging a
  monomial `1_(pi(S)=T)` over `tau` gives "`1[the k specified pairs lie in pi] / (n)_k`".
  - The correct value is `Pr_F[pi restricted to S induces exactly the pattern of T] / (n)_b`,
    where `b` is the number of distinct values in `T`. Singletons must stay
    unpaired inside `S`.
  - Inclusion-exclusion over partial matchings of `S` expresses this through
    `Pr[M <= pairs(pi)]` with `|M| <= |S|/2`.
  - So a monomial of coordinate-degree `k` needs pair strength `floor(k/2)`.
    `G^4` together with the degree-2 conditioning has coordinate-degree
    `8d+2`, so strength `4d+1` already suffices. The stated `8d+1` is correct
    but conservative.
* **Verdict.** Every use of uniformity is one of three kinds: a low-degree
  moment (Lemmas 4.6, 4.9 and 4.10), the balanced-point density (Lemma 4.12),
  or none (Appendix C, 5.1, 5.2). The transfer stands, and both
  `ugc-from-smooth-design-rich-2to1` and `ugc-from-finite-moment-pairing-hardness`
  rest only on their hardness hypotheses. This also confirms the finite-moment
  route's claim that Lemma 4.12's high-degree term is the only pointwise use
  of the pairing law.
