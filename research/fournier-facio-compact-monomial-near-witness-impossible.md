---
rg: 2
id: fournier-facio-compact-monomial-near-witness-impossible
kind: claim
title: A Fournier--Facio singular near witness cannot be monomial even modulo compacts
invalidates:
  - fournier-facio-compactly-blurred-monomial-witness
distinct_from:
  fournier-facio-monomial-near-witness-impossible: That excludes actors which exactly normalize one charged atomic basis; this allows every actor to differ from a basis-normalizing unitary by an arbitrary compact operator.
  fournier-facio-compression-coset-charge-impossible: That excludes charged bases with an equivariant map to the compression cosets; this needs no coarse coset factor and applies to an arbitrary atomic basis.
---

**ESTABLISHED ESSENTIAL-CARTAN FENCE.**  Let `G` be the explicit
Fournier--Facio group.  There is no Kahl--Schneider charged-basis witness

```text
(ell^2(X),mu,pi:G->U(ell^2(X)))
```

for its hyperlinearity with `mu` purely singular and, for every `g in G`,

```text
pi(g)=M_g+K_g,                                           (FCM1)
```

where `M_g` is a monomial unitary in the basis `X` and `K_g` is compact.
The monomial lifts need not form a representation, the phases are arbitrary,
and the compact perturbations need not have uniformly bounded rank.

Indeed a purely singular charged diagonal state annihilates every compact
operator.  Consequently `(FCM1)` transfers state invariance and every
near-multiplication row from `pi` to `M`.  Compact operators also converge to
zero on all but a finite set of vectors of any fixed orthonormal basis at
each positive tolerance, so essential freeness transfers as well.  The
monomial family `M` would therefore be an essentially free amenable near
representation, contradicting
`fournier-facio-monomial-near-witness-impossible`.

Thus a positive singular witness cannot be obtained by compactly blurring a
Schreier, quasi-regular, or phase-twisted permutation model.  In the Calkin
algebra its actor image cannot have coherent lifts in the image of one atomic
masa normalizer.  The surviving positive lane must be genuinely non-Cartan
even modulo compacts and, by
`fournier-facio-compression-coset-charge-impossible`, cannot carry an
equivariant coarse `G/Gamma` factor.

Proof: `fournier-facio-compact-monomial-no-go-proof`.
