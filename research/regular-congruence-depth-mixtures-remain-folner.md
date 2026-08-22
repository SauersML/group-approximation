---
rg: 2
id: regular-congruence-depth-mixtures-remain-folner
kind: claim
title: Actual SL3 regular-congruence depth mixtures remain Folner after branching
artifacts:
  - research/artifacts/sl3-regular-depth-folner-profile-2026-08-22.md
distinct_from:
  folner-multiplicity-atlases-have-vanishing-first-exit: that realizes arbitrary abstract semisimple type atlases using cyclic characters; this computes the genuine minimal-conductor bands inside regular SL3 congruence representations and retains the canonical lattice character.
  fixed-shift-invariance-does-not-force-flat-profile: that is a statement about abstract probability profiles; this proves that the p^8 arithmetic branching multiplicities merely convolve those profiles with a geometric kernel and therefore do not restore a shift gap.
  depth-shifted-regular-overlap-is-exactly-one-sixteenth: that computes the common fraction for one regular block under one parahoric depth shift; this allows arbitrarily wide direct-sum mixtures of regular blocks and shows that their one-dimensional conductor marginal stays Folner.
---

Let

```text
G_a=SL_3(Z/p^a Z),       a>=1,       q=p^(-8).
```

For any finite rational probability profile `mu=(mu_a)` on positive
conductor levels there is an exact finite-dimensional representation

```text
sigma_mu = direct_sum_a M_a Reg(G_a)                    (RDF1)
```

whose normalized dimension weight in the displayed level-`a` blocks is
exactly `mu_a`.  Indeed choose a common integer `D` such that
`M_a=D mu_a/|G_a|` is integral.

Decompose each regular block into irreducibles by MINIMAL congruence
conductor.  In `Reg(G_a)`, the total dimension of irreducibles factoring
through `G_b` is exactly `|G_b|`.  Since

```text
|G_a|/|G_(a-1)|=p^8       (a>=2),                       (RDF2)
```

the normalized exact-conductor bands in a level-`a` regular block are

```text
mass(conductor=b)=(1-q)q^(a-b)       (2<=b<=a),
mass(conductor<=1)=q^(a-1).                             (RDF3)
```

Thus, away from the bottom level, passing from the displayed top-level
profile `mu` to the genuine minimal-conductor profile is convolution with
the probability kernel

```text
kappa(r)=(1-q)q^r,       r>=0.                           (RDF4)
```

The mass collapsed into the bottom band is at most `q^(L-1)` when `mu` is
supported in levels `a>=L`.  Therefore, for every fixed depth translation
`s`,

```text
TV(nu,shift_s nu)
 <= TV(mu,shift_s mu)+2q^(L-1),                         (RDF5)
```

where `nu` is the genuine minimal-conductor distribution of `sigma_mu`.

Take the triangular profile

```text
mu_(L,N)(L+k)=2(k+1)/((N+1)(N+2)),       0<=k<=N.       (RDF6)
```

For every fixed `s`, first let `L,N->infinity`.  Then

```text
TV(nu_(L,N),shift_s nu_(L,N))->0,
max_b nu_(L,N)(b)->0.                                   (RDF7)
```

Moreover these exact representations have the canonical lattice character
locally: for every finite `F subset SL_3(Z)\{1}`, reduction modulo `p^a` is
nontrivial on every element of `F` once `a>=L(F)`, and hence every regular
block in `(RDF1)` has normalized trace zero on `F`.

Consequently the actual `p^8` congruence branching multiplicities do not
turn the one-dimensional conductor-depth shift into a non-Folner operator,
even under canonical-character normalization.  Since conjugation by
`h=diag(p,1,p^(-1))` changes the simple-root depths by one and the long-root
depth by two, every fixed depth stencil it exposes is defeated by `(RDF7)`.

This is a no-go for deriving a fixed denominator-relator payment from the
minimal-conductor MARGINAL alone.  It is not a full arithmetic microstate:
the construction does not provide the joint parahoric intertwiners required
by the denominator relations.  A successful contraction must therefore use
their branch labels, mixed-root compatibility, or the global building PVM;
the exact depth distribution and its genuine branching dimensions are
insufficient.

