---
rg: 2
id: kt-coset-bernoulli-essentially-free
kind: claim
title: The Kun--Thom coset Bernoulli action is essentially free modulo its scalar center, and free for q=2
distinct_from:
  coset-bernoulli-action-is-essentially-free: that proves essential freeness for the ARITHMETIC pair (SL_3(Z[1/p]), SL_3(Z)) through the Bruhat--Tits building of SL_3(Q_p); this proves it for the Kun--Thom Theorem E pair by the semidirect-product grading and monomial supports, with no building, and finds a finite central kernel the arithmetic case does not have.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**ESTABLISHED.**  Fix the Kun--Thom Theorem E pair
`Gamma = EL_r(R_+) < G = E rtimes S`, with `E = EL_r(R)`, `S = SL_d(Z)`,
`R_+ = F_q[x_1,...,x_d]`, `R = F_q[x_1^(±1),...,x_d^(±1)]`, `r,d >= 3`, and
put `I = G/Gamma`, `X = {-1,1}^I` with Bernoulli(1/2) measure `mu`.  Let

```text
Z_q = { lambda I : lambda in F_q, lambda^r = 1 },     |Z_q| = gcd(r, q-1).
```

1. Every `g in G \ E` fixes **no** coset.
2. Every `g in E \ Z_q` moves infinitely many cosets.
3. Every `g in Z_q` fixes **every** coset; `Z_q` is central in `G` and
   `core_G(Gamma) = Z_q` is the kernel of `G action I`.
4. Hence `G/Z_q action (X,mu)` is essentially free, and the generalized
   Bernoulli action is ergodic.  For `q = 2` (and whenever `gcd(r,q-1)=1`),
   `Z_q = 1`: the coset action is faithful and `G action (X,mu)` itself is
   essentially free.

The correction relative to the first posing of this node (2026-09-11,
`d9764c064`): unrestricted essential freeness is **false** when
`gcd(r,q-1) > 1`, because the nontrivial central scalars act trivially on `I`.
The pinned `q = 2` pair of the double lane
(`kt-q2-double-hyperlinear-iff-relative-embeddable`) is unaffected.

DERIVATION
kt-coset-bernoulli-essentially-free-proof
