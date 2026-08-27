---
rg: 2
id: high-type-irreducibles-retain-finite-packet-mass
kind: claim
title: Residual quotient towers contain high irreducibles retaining every finite-packet projection
distinct_from:
  canonical-packet-traces-do-not-place-old-commutant-density: that uses the whole regular representation of each quotient and leaves open whether its large multiplicity algebra causes the commutant-density loss; this extracts one irreducible block, whose commutant is already scalar.
  minimal-packet-corner-overlap-has-irreducible-spectator-dilution: that tensors an independent unbounded irreducible spectator onto a packet factor; this keeps the packet literally inside one residually finite Kazhdan group and obtains the irreducibles from its own quotient tower.
  toeplitz-self-embedding-fixes-unbounded-congruence-types: that constructs stationary unbounded congruence types but does not retain positive mass for a prescribed packet projection; this proves retention whenever the packet survives an unbounded stationary quotient tower.
---

**ESTABLISHED IRREDUCIBLE EXTRACTION AND HNN FENCE.**  Let `Lambda` be an
infinite residually finite property-`(T)` group, let `B<Lambda` be finite,
and let

```text
0!=z=z*=z^2 in C[B],             q=tau_B(z)>0.          (HIR1)
```

Suppose `q_n:Lambda->Q_n` are finite quotients, injective on `B`, with
`|Q_n|->infinity`.  Then there are irreducible representations

```text
pi_j:Lambda->U(d_j),             d_j->infinity,         (HIR2)
```

factoring through members of this quotient tower and satisfying

```text
tr_(d_j)(pi_j(z))>=q/2.                                  (HIR3)
```

Since each `pi_j` is irreducible,

```text
dim End_Lambda(pi_j)/d_j^2=1/d_j^2 ->0.                 (HIR4)
```

Thus the old-commutant-density dilution is not an artifact of taking a
regular representation with a large multiplicity space.  One scalar
commutant already suffices while a prescribed nonzero finite-packet
projection keeps fixed positive Hilbert mass.

## Proof

For a finite quotient `Q=Q_n`, write its regular representation in
Plancherel form.  For `sigma in Irr(Q)` put

```text
a_sigma=dim(sigma)^2/|Q|,
r_sigma=tr_(dim sigma)(sigma(z)).                       (HIR5)
```

Because `q_n` is injective on `B`, the canonical trace of `z` is unchanged.
Since `z` is a projection, `0<=r_sigma<=1`, and the regular trace identity
is

```text
sum_(sigma in Irr(Q)) a_sigma r_sigma=q.                (HIR6)
```

Fix `K`.  Property `(T)` gives only finitely many irreducible unitary
representations of `Lambda` of dimension at most `K`.  Let

```text
C_K=sum_(rho in Irr_<=K(Lambda)) dim(rho)^2<infinity.   (HIR7)
```

Every irreducible of `Q_n` of degree at most `K`, pulled back along `q_n`,
belongs to this fixed finite menu.  Hence its total Plancherel weight is at
most

```text
sum_(dim sigma<=K) a_sigma <= C_K/|Q_n| ->0.            (HIR8)
```

Choose `n` so large that the right side is less than `q/2`.  If every
irreducible `sigma` of degree greater than `K` had `r_sigma<q/2`, then
`(HIR6)` and `(HIR8)` would give

```text
q
 =sum_(dim sigma<=K) a_sigma r_sigma
  +sum_(dim sigma>K) a_sigma r_sigma
 <q/2+q/2=q,                                            (HIR9)
```

a contradiction.  Thus some irreducible quotient representation has
`dim(sigma)>K` and `r_sigma>=q/2`.  Taking `K->infinity` proves
`(HIR2)--(HIR3)`, and Schur's lemma proves `(HIR4)`.

## Stationary-quotient consequence

Let `alpha:Lambda->Lambda` be an injective endomorphism and assume, in
addition, that the same quotient tower is stationary:

```text
q_n o alpha=q_n.                                        (HIR10)
```

Then every `pi_j` above satisfies `pi_j o alpha=pi_j`, so it extends to the
ascending HNN extension

```text
H=<Lambda,t | t g t^(-1)=alpha(g), g in Lambda>         (HIR11)
```

by `pi_j(t)=1`.  These are exact zero-relator-defect representations of
`H` with packet mass at least `q/2` and old-`Lambda` commutant density
tending to zero.  More generally the same conclusion holds when
`q_n o alpha` differs from `q_n` by an automorphism of `Q_n` implemented in
the chosen irreducible representation.

Consequently any estimate of the form `(PCD1)` for a carrier projection
`z` is false if `z` survives an unbounded stationary finite-quotient tower.
A successful coefficient-covariance cell must therefore destroy at least
one of the following three properties on every such tower:

1. survival of the finite packet `B` and the projection `z`;
2. stationarity of the quotient under the compressor endomorphism;
3. extension of the extracted irreducible across the added cell.

This is a stricter falsification test than regular-quotient dilution.  It
shows that coupling only to quotient-stationary coefficient words cannot
place packet mass in positive old-commutant density, even after all regular
multiplicity has been removed.

DERIVATION
high-type-packet-plancherel-extraction-proof

