---
rg: 2
id: rf-hnn-telescope-retains-coefficient-residual
kind: claim
title: A residually finite base keeps every algebraic coefficient visible through an ascending-HNN telescope
distinct_from:
  one-compressor-covariance-has-free-hs-telescope: that gives a covariance telescope for an arbitrary fixed finite-dimensional base representation; this chooses a new regular finite quotient at each depth and proves that a prescribed algebraic coefficient retains its full canonical L2 norm on every telescope block.
  high-type-irreducibles-retain-finite-packet-mass: that needs a stationary quotient in order to extend one irreducible as an exact HNN representation; this needs no stationary quotient and gives vanishing-defect finite-dimensional HNN tuples for every injective endomorphism.
  residually-finite-models-refute-filtered-wandering-return: that assumes the ambient group itself is residually finite and uses its exact finite quotients; an ascending HNN extension need not be residually finite, and this constructs approximate models from residual finiteness of the base alone.
---

**ESTABLISHED BARE ASCENDING-HNN FENCE.**  Let `Lambda` be a finitely
generated residually finite group, let `alpha:Lambda->Lambda` be injective,
and fix a finite generating set `S`.  For every

```text
b in C[Lambda]                                             (RHT1)
```

and every `L>=1`, there are a finite-dimensional exact representation
`Pi_L` of `Lambda` and a unitary `T_L` such that

```text
max_(s in S)
 ||T_L Pi_L(s) T_L^(-1)-Pi_L(alpha(s))||_2 <=2/sqrt(L),  (RHT2)

||Pi_L(b)||_2=||lambda_Lambda(b)||_2.                     (RHT3)
```

The same models can be made exactly canonical on any prescribed finite
window of base-group words.  If `z in C[B]` is a projection for a finite
subgroup `B<Lambda`, the quotient can simultaneously be chosen so that

```text
tr(Pi_L(z))=tau_B(z).                                     (RHT4)
```

Thus the single ascending HNN extension

```text
H=<Lambda,t | t s t^(-1)=alpha(s), s in S>              (RHT5)
```

cannot bound any nonzero algebraic base coefficient by its ordinary HNN
relator energy.  Indeed, for the usual sum of squared normalized-HS defects,

```text
E_HNN(Pi_L,T_L)<=4|S|/L,                                 (RHT6)
```

while `(RHT3)` is independent of `L`.

## Proof

Write `b=sum_(g in F)c_g g`, with `F` finite.  For each `L`, residual
finiteness gives a finite quotient

```text
q_L:Lambda->Q_L                                           (RHT7)
```

which separates every pair of elements in each finite set

```text
alpha^j(F),                  0<=j<L.                     (RHT8)
```

If a finite canonical base window `W` and a finite packet `B` are also
prescribed, require in addition that every nonidentity element of
`alpha^j(W union B)` survive for `0<=j<L`.  These are finitely many
requirements, and injectivity of `alpha` makes every element to be separated
nontrivial.

Let `rho_L=lambda_(Q_L) o q_L` and form the length-`L` telescope

```text
K_L=direct_sum_(j=0)^(L-1) ell^2(Q_L),
Pi_L(g)|_(K_j)=rho_L(alpha^j(g)).                        (RHT9)
```

Let `T_L` be the cyclic backward block shift.  Exactly as in
`one-compressor-covariance-has-free-hs-telescope`, covariance holds on
`L-1` blocks and can fail only on the wrap block.  A difference of two
unitaries has normalized-HS norm at most `2`, so `(RHT2)` and `(RHT6)`
follow.

The separation in `(RHT8)` prevents collisions among the support terms of
`q_L(alpha^j(b))`.  The regular trace on `Q_L` therefore gives, on every
block,

```text
||rho_L(alpha^j(b))||_2^2
   =sum_(g in F)|c_g|^2
   =||lambda_Lambda(b)||_2^2.                           (RHT10)
```

Averaging `(RHT10)` over the `L` equal blocks proves `(RHT3)`.  The same
regular-trace calculation gives zero trace to every prescribed nonidentity
word in `W` on every block, hence exact canonicality on that window.  When
`z` is a projection, injectivity on every `alpha^j(B)` identifies each block
with a multiple of the regular `B`-module and gives `(RHT4)`.

## Bounded-type coefficient consequence

Let `Lambda` also have property `(T)`, let `p=p_<=K` be its bounded-type
central projection, choose `a in C[Lambda]` with

```text
||a-p||_max<=epsilon<1,
```

and let `0!=z=z*=z^2 in C[B]`, `q=tau_B(z)`.  The regular representation
kills `p`, so

```text
||lambda_Lambda(z(1-a))||_2
 >=(1-epsilon)sqrt(q).                                  (RHT11)
```

Apply `(RHT1)--(RHT3)` to `b=z(1-a)`.  Then

```text
||Pi_L(z(1-a))||_2>=(1-epsilon)sqrt(q),
E_HNN(Pi_L,T_L)<=4|S|/L.                                (RHT12)
```

Consequently the residual isolated in
`one-bounded-type-coefficient-separates-unbounded-exits` cannot be compiled
into word energy by a bare single self-copy/HNN relation, even when `alpha`
has no stationary finite quotient retaining the packet.  An ascending-HNN
candidate must add a genuinely payload-sensitive two-cell beyond covariance;
that extra cell, not the infinite-index self-copy, would carry the whole
matrix-only burden.

The first broad two-letter extension is fenced as well.
`rf-amenable-two-cell-retains-coefficient` replaces the cyclic interval by a
joint right Følner set.  It retains the same exact coefficient norm through
every amenable compression-semigroup relation, including commuting and
nilpotent/Hall--Witt tables.  Therefore adding a second stable letter helps
only when its joint holonomy is genuinely nonamenable or its
coefficient-valued cocycle escapes amenable-extension permanence.

DERIVATION
rf-hnn-coefficient-telescope-proof
