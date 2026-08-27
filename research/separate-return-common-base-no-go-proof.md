---
rg: 2
id: separate-return-common-base-no-go-proof
kind: route
title: Audit tensor, scalar-free, and regular-orbit combinations of cyclic spatializations
target: separate-return-models-do-not-force-a-common-base
requires:
  - free-lattice-ce-is-joint-ultrapower-spatialization
---

For the tensor proposal, let `pi_i:N->Q_i` be the base embeddings obtained
from the separate cyclic crossed products.  The only pointwise formula that
uses every coordinate is

```text
Delta(x)=pi_1(x) tensor ... tensor pi_r(x).                (SCB1)
```

For `r>=2`,

```text
Delta(lambda 1)=lambda^r 1 != lambda 1                    (SCB2)
```

for a generic scalar `lambda`; `(SCB1)` is not linear.  A genuine diagonal
star homomorphism `N->N^(tensor r)` would be extra coalgebra structure and is
not supplied by embeddings.  The valid maps `x |-> pi_i(x) tensor 1` simply
choose one cyclic model and give no implementers for the other automorphisms.

For the free proposal put `A_i=N rtimes_(beta_i) Z`.  Scalar free-product
permanence can make

```text
A_1 *_C ... *_C A_r                                      (SCB3)
```

Connes embeddable, but `(SCB3)` contains distinct copies `N_i`.  Covariance
for the `i`th return holds only on `N_i`.  The algebra required by `(FJS3)` is

```text
A_1 *_N ... *_N A_r = N rtimes_beta F_r.                 (SCB4)
```

Passing from `(SCB3)` to `(SCB4)` means imposing equality of all copies of
every element of `N` and retaining the reduced amalgamated trace.  No
Connes-embeddability permanence under that operation is available for a
nonamenable `N`; it is exactly the Gao--Junge nonamenable-amalgamation gate.
Adding free labels therefore solves independence of the returns but not
equality of their base embeddings.

Finally consider the literal orbit-sum construction.  Its blocks are indexed
by `g in F_r`, with the base represented on block `g` by
`pi_0 compose beta_g`, and the unitary for `s` sends block `g` to block `sg`.
If the direct-sum trace gives block `g` weight `mu(g)`, unitary invariance of
the trace forces

```text
mu(sg)=mu(g)                    (s in S, g in F_r).        (SCB5)
```

Thus all singleton weights are equal.  No invariant probability exists on
the infinite regular orbit.  In approximate finite orbit truncations,
vanishing normalized covariance error would give a Folner sequence for
`F_r`, impossible when `r>=2`.

There is an exact quantitative form of this obstruction.  Let `(e_g)` be
the labeled block PVM and let `W_s` be any proposed unitary shift.  Projection
rank matching gives

```text
(1/2) sum_g ||W_s e_g W_s^* - e_(sg)||_2^2
  >= (1/2) ||s_*mu-mu||_1.                              (SCB6)
```

The bound is optimal: pair the two block decompositions with maximal rank
intersection in every label.  Hence vanishing aggregate HS mismatch for
every generator is literally a Reiter sequence of finitely supported
probability measures.  In the homogeneous-quotient application the acting
cocompact lattice is infinite Kazhdan and therefore nonamenable, so some
generator retains a uniform mismatch.  This quantitative statement still
only fences labeled orbit-block commonization; an arbitrary common embedding
may mix or destroy those artificial labels and remains the open
spatialization problem.

One may instead permute a finite quotient `F_r/H`.  To label a quotient block
by `pi_0 compose beta_g`, however, changing the representative from `g` to
`gh`, `h in H`, must not change that block up to the allowed matrix-unitary
identification.  This asks that the kernel automorphisms `beta_h` already be
spatial relative to the chosen seed embedding.  Residual finiteness supplies
the permutation, not this covariance.  Hence finite quotients do not derive
the common embedding from the separate cyclic data either.
