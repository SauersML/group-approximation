---
rg: 2
id: spherical-hs-average-bypasses-global-character-resolution
kind: claim
title: One word-visible spherical Hilbert--Schmidt average collapses the marked seed without resolving the global character PVM
distinct_from:
  infinite-character-actor-word-energy-interface: that asks finite word defects to recover the full character transport energy after global PVM exactification; this is an alternative endpoint which never names the individual character projections.
  finite-covariance-energy-sees-only-character-restrictions: that computes the blindness of finitely many diagonal module tests; this must authenticate a non-diagonal actor orbit frame in Hilbert--Schmidt space.
  finite-covariance-mixed-words-remain-character-blind: that refutes mixed words built only from a transporter and a finite tested diagonal algebra; this requires independent actor relations to authenticate the exchanged domains.
  one-seed-infinite-character-expansion-collapses-mark: that applies a Schreier gap to an already exact spectral PVM; this seeks the analogous contraction directly on a word-generated non-diagonal Hilbert--Schmidt sector.
---

OPEN.  Choose one finitely presented actor/module packet, a finitely
supported probability measure `mu` on fixed actor words, and `q<1`.  For every
sufficiently accurate matrix microstate `U`, define

```text
A_(mu,U)(X)=sum_g mu(g) C_g X C_g^*.                    (SHA1)
```

The target is a word-authenticated Hilbert--Schmidt sector `W_U` and a seed
vector `X_U in W_U` for which the presentation defects imply, with a
dimension-independent modulus,

```text
||A_(mu,U) X||_2 <= q ||X||_2+omega(delta)              (SHA2)
```

on the seed-generated orbit frame, while the mark/Pauli relations imply

```text
||A_(mu,U)X_U-X_U||_2 <= omega(delta),
||X_U||_2 >= c sqrt(mu_mark)-omega(delta)               (SHA3)
```

for one fixed `c>0`.  Then

```text
(1-q)c sqrt(mu_mark) <= O(omega(delta)),                (SHA4)
```

so the marked carrier vanishes without global abelian rounding or recovery
of every `P_chi`.

The analytic model is the quasi-regular contraction behind Skenderi--Yehuda,
*Growth gaps and generating sets* ([arXiv:2608.19101](https://arxiv.org/abs/2608.19101)):
under a uniform stabilizer growth-gap hypothesis, one finite spherical
measure can contract all relevant quasi-regular sectors.  That paper supplies
the design of `mu`, not `(SHA2)--(SHA3)`.  The project must still prove that
the selected actor has the required uniform family of stabilizers and that
its finite relators make the corresponding non-diagonal orbit frame visible
inside normalized Hilbert--Schmidt space.

## Attempts

**Orbit-frame attack and decisive red-team test.**  Start with the cyclic
Hilbert--Schmidt span of one off-diagonal Pauli coefficient and transport it
by the finitely many words in `supp(mu)`.  The unresolved step is proving a
dimension-independent lower frame bound from the presentation relations;
without it, contraction of an abstract quasi-regular model says nothing
about the microstate sector.

Apply the two-character invisible-fiber swap from
`finite-covariance-mixed-words-remain-character-blind`.  If the swap extends
to the actor relations and leaves `(SHA1)` unchanged on the proposed sector,
then no estimate `(SHA2)` can distinguish the fine transport and this route
is refuted.  A surviving construction must exhibit the exact actor word which
moves or separates the exchanged domains.  Merely replacing a finite family
of diagonal probes by their average is not new information.

## Why this is a bypass, not a hidden PVM theorem

This claim does not establish `(ISC2)` in
`infinite-character-actor-word-energy-interface`, and it does not make
finite character restrictions globally separating.  It replaces that lane
by one contraction-versus-invariance inequality on a non-diagonal cyclic
sector.  Failure of this claim therefore leaves the existing whole-module
PVM route unchanged.

