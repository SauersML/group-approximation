---
rg: 2
id: fpbs-uniform-l2-gap-short-relator-cylinders
kind: claim
title: Each one-relation cylinder of uniformly nonamenable marked groups has uniform l2 gap constants
distinct_from:
  fpbs-uniform-l2-gap-marked-groups: that asks for one uniform pair (M,delta) on all of X_(k,eta); this splits it into one independently falsifiable statement per relation w, and with the high-girth patch only the finitely many w shorter than L(eta) matter.
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
---

**OPEN.** Fix `k >= 2`, `eta in (0,1)` and a nontrivial freely reduced word
`w` in `F_k`. Let `Z_{k,eta,w}` be the set of `k`-marked groups
`(Gamma; s_1,...,s_k)` with `w = e` in `Gamma`, whose simple Cayley graph has
spectral radius at most `1 - eta`. The claim is that for every such
`(k,eta,w)` there are `M_w < infinity` and `delta_w > 0` with

```text
||T^G_{p_c(G) + delta_w}||_{2->2} <= M_w   for every G in Z_{k,eta,w}.
```

Section 4 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.

* Each `Z_{k,eta,w}` is a compact clopen piece of `X_{k,eta}`.
* Only the words with `|w| < L(eta)` are needed to recover the uniform
  conjecture, because `fpbs-high-girth-uniform-l2-patch` covers the rest.
* The pieces can be attacked or refuted separately. Representative pieces:
  - `w = s_1^2`: involutive generators;
  - `w = [s_1,s_2]`: commuting generators, as in `Gamma x Z` with mixed
    markings;
  - `w = s_1^n`: a torsion generator of small order.
* A counterexample on a single piece refutes the uniform conjecture for that
  `(k,eta)`. It does not refute the pointwise l2 conjecture: by
  `fpbs-l2-gap-baire-dichotomy` it gives a failure of uniformity, and a
  pointwise failure needs a nonempty kernel.

## Attempts

* **Transplant the known qualitative classes by compactness (2026-09-17).**
  Cover a cylinder by open neighbourhoods of groups already known to be in
  `C_2`, such as free products, hyperbolic groups and acylindrically
  hyperbolic groups, and take a finite subcover.

  **Where it dies:**
  - A finite subcover needs each point to have a neighbourhood inside *one*
    `U_{M,delta}`, not merely to lie in `C_2`.
  - The known gap theorems give constants that are not locally determined: for
    example, hyperbolicity constants are unbounded along convergent sequences.
    Section 4 of `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`
    records that their constants degenerate.
  - On the cylinder `w = [s_1,s_2]` the pieces contain markings of `Gamma x Z`.
    The factor-of-iid construction of Theorem 6 of
    `research/artifacts/fpbs/exploration.md` shows that nonamenability together
    with finite-cluster averaging does not control the operator there.
  - No piece is decided.
