---
rg: 2
id: extraspecial-fusion-filter-normalizer-proof
kind: route
title: Compute the spin Fourier PVM and factor every normalizer through its matrix multiplicity
target: extraspecial-fusion-filter-local-normalizer-globalization
requires:
  - perfect-qc-separation-yields-finite-bcs-with-no-matrix-model
---

An extraspecial group `E_n` has `2^(2n)` linear characters, all trivial
on `J`, and one nonlinear irreducible representation `rho` of dimension
`d=2^n`.  The latter sends `J` to `-I`.  The sum-of-squares identity is

```text
2^(2n) + d^2 = 2^(1+2n)=|E_n|.                         (EFP1)
```

It follows from the Wedderburn decomposition that the negative central
idempotent selects exactly the spin block:

```text
p_- C[E_n]p_-=End(C^d).                                 (EFP2)
```

Let `A` be maximal abelian containing `J`; then
`|A|=2^(n+1)`.  The spin character is `d` at the identity, `-d` at
`J`, and zero off the center.  For every character `chi` of `A` with
`chi(J)=-1`, its multiplicity in `rho|_A` is

```text
<chi,rho|_A>
 =|A|^(-1)(d+(-1)(-d))
 =2d/2^(n+1)=1.                                         (EFP3)
```

There are `|A|/2=d` such characters.  Their Fourier projections are
therefore rank one in the spin block, are mutually orthogonal, and sum to
`p_-`.  This proves the local one-hot statement.

The same uniqueness proves the fusion identity.  The tensor cube sends
`J` to `-I`, so all of its irreducible constituents lie in the negative
central sector.  The only such irreducible is `rho`; comparison of
dimensions gives multiplicity

```text
dim(rho^tensor3)/dim(rho)=d^3/d=d^2.                    (EFP4)
```

Thus fusion returns to the spin block even though the additive Fourier
projections do not obey the group-like tensor rule for literal selectors.

Now let `pi` be any representation of an ambient `Gamma` with
`pi(J)=-I`.  Restriction to `E_n` is a multiple of `rho`, so there is
a unitary identification

```text
pi(e)=rho(e) tensor I_K,              e in E_n.          (EFP5)
```

Assume `E_n normal Gamma`.  For `g in Gamma`, conjugation by `pi(g)`
normalizes `M_d tensor I`.  Every automorphism of `M_d` is inner, so
choose `u_g in U(d)` implementing that automorphism.  Then

```text
(u_g^* tensor I)pi(g) in (M_d tensor I)'
                         =I tensor B(K).                 (EFP6)
```

It is unitary, hence equals `I tensor w_g` for a unitary `w_g`.  This
proves `(EFF5)`.

Every Fourier projection, and every conjugate by such a normalizer, is now
`P tensor I_K` for a projection `P in M_d`.  Suppose these were the
decoded outcome projections for all questions of the fixed independent-set
source.  The relations

```text
sum_v (P_(i,v) tensor I)=I,
(P_(i,u) tensor I)(P_(j,v) tensor I)=0
  for every losing pair                                  (EFP7)
```

hold if and only if the corresponding relations hold among the first
factors in `M_d`.  Those first factors would be a perfect
finite-dimensional representation of the synchronous algebra, contrary to
its established no-matrix property.  Therefore some decoded row must leave
the normalized spin matrix factor.

Finally let `q` be any projection and abbreviate `pi(g)` by `g`.
Inserting `q+(1-q)=1` gives

```text
qghq=qgqhq+qg(1-q)hq,                                  (EFP8)
```

which rearranges to `(EFF7)`.  Even zero ambient word defect therefore
does not imply zero defect for the product of compressed letters.  In the
extraspecial construction, forcing all letters to normalize the spin block
makes this leakage vanish but triggers `(EFP5)--(EFP7)`.  The sole escape
is to retain and quantitatively use the nonnormal relative-position term,
which is outside a finite fusion/normalizer table.
