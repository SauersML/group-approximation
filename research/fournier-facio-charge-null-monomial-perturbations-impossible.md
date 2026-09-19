---
rg: 2
id: fournier-facio-charge-null-monomial-perturbations-impossible
kind: claim
title: A Fournier--Facio witness cannot be monomial modulo the singular charge null ideal
invalidates:
  - fournier-facio-asymptotically-one-sparse-near-witness
distinct_from:
  fournier-facio-compact-monomial-near-witness-impossible: That removes compact perturbations using pure singularity; this removes arbitrary, possibly noncompact perturbations which vanish only in the charged column seminorm.
  fournier-facio-monomial-near-witness-impossible: That requires exact basis normalization; this permits every actor to mix basis vectors on a large ordinary Hilbert subspace, provided that mixing is invisible to the invariant charge.
  fournier-facio-compression-coset-charge-impossible: That requires an equivariant coarse map to `G/Gamma`; this uses no coarse factor and applies to an arbitrary charged basis.
---

**ESTABLISHED CHARGE-NULL FENCE.**  Let `G` be the explicit
Fournier--Facio group and let

```text
(ell^2(X),mu,pi:G->U(ell^2(X)))                       (FCN1)
```

be a Kahl--Schneider charged-basis near representation with charged diagonal
state

```text
phi_mu(T)=integral_X <T delta_x,delta_x> dmu(x).
```

There cannot exist monomial unitaries `M_g`, one for every `g`, such that

```text
phi_mu((pi(g)-M_g)^*(pi(g)-M_g))=0.                   (FCN2)
```

No compactness, finite rank, or uniform propagation hypothesis is imposed.
Condition `(FCN2)` says exactly that, for every positive `epsilon`,

```text
mu({x: ||pi(g)delta_x-M_g delta_x||>=epsilon})=0.     (FCN3)
```

Thus the perturbation may be noncompact and arbitrarily large on an
infinite charge-null set.

The reason is that the charge-null operators form the left null ideal of
`phi_mu`.  State invariance transfers from `pi(g)` to `M_g`; this makes the
permutations underlying `M_g` preserve `mu`.  Right multiplication by those
monomials then also preserves the null ideal.  Expanding each multiplication
row shows that the family `M` is itself a charged near representation, and
`(FCN3)` transfers essential freeness from `pi` to `M`.  This contradicts
`fournier-facio-monomial-near-witness-impossible`.

Consequently a positive non-Cartan witness must exhibit genuine
positive-charge delocalization: for every choice of monomial actor family,
some fixed group element has positive charge of basis vectors on which its
image stays a definite distance from the chosen phase-permutation image.
It is not enough to place all non-Cartan mixing on a charge-null reservoir.

Proof: `fournier-facio-charge-null-monomial-no-go-proof`.
