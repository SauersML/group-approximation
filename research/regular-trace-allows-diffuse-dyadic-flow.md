---
rg: 2
id: regular-trace-allows-diffuse-dyadic-flow
kind: claim
title: Regular trace forces dyadic conductor escape but does not contradict diffuse bidirectional flow
distinct_from:
  sparse-dyadic-iwahori-packets-have-a-uniform-boundary: that gives a mismatch floor when only finitely many conductor depths are occupied; this determines what canonical trace says about the escaping band masses and shows that its scalar consequence is compatible with the remaining unbounded-width flow.
  pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss: that uses the full Plancherel branching multiplicities of regular quotient representations; this uses only convergence of the vertex character to the regular character and therefore applies to arbitrary selected non-Plancherel packets.
---

Let `Pi_n` be exact finite-dimensional representations of `SL_2(Z)` which
factor through finite dyadic congruence quotients, and suppose their
normalized characters converge pointwise to the regular character.  Write
`x_(n,a)` for the normalized physical dimension of the sum of their
irreducible constituents of minimal congruence conductor `a`.  Then for
every fixed `r`,

```text
sum_(a<=r) x_(n,a) -> 0.                                (RTE1)
```

The same holds for the opposite vertex packet.  Thus canonical trace rules
out every positive shallow-conductor atom and forces the whole band measure
to escape to infinity.  This conclusion uses only fixed principal-
congruence root elements and is uniform over all selected irreducible types.

However `(RTE1)` does not contradict the bidirectional recurrence from
`sparse-dyadic-iwahori-packets-have-a-uniform-boundary`.  Indeed, for any
integers `A,K>=1`, put

```text
x_a=y_a=1/K                 (A<a<=A+K),
c_(a,a+1)=c_(a+1,a)=1/(2K)  (A<a<A+K),                 (RTE2)
```

and set every other band mass and coupling coefficient to zero.  The
unmatched mass on each side is `u=1/K`, so its normalized `L^1` restriction
mismatch is

```text
L/d=2u=2/K -> 0.                                      (RTE3)
```

At every occupied upper depth,

```text
sum_(b<=a)c_(a,b) <= x_a/2 <= 2x_a/3,
```

and symmetrically
`sum_(a<=b)c_(a,b)<=2y_b/3`.  Hence `(RTE2)` satisfies all presently proved
last-layer fixed-space and bidirectional-flow inequalities.  Taking
`A=A_n->infinity` and `K=K_n->infinity` also satisfies `(RTE1)`.

The scalar escape is not caused by fractional arithmetic.  There is also an
integral saturated nearest-neighbour profile on `L>=2` consecutive depths: take
`x_a=y_a=3`; put weight two on the bottom diagonal cell, weight one on every
other diagonal cell and every adjacent off-diagonal cell, and leave only one
unit unmatched at the top of each side.  Every two-thirds inequality is then
an equality, the common mass is `3L-1`, and

```text
L1 mismatch / physical dimension = 2/(3L).            (RTE4)
```

Thus integrality, nearest-neighbour conductor movement, and saturation of the
known root-fixed-space bound still permit a Følner window.

There is likewise no contradiction at the level of fixed trace tests.  On
each depth-`a` scalar band use the exact-conductor Plancherel shell: the
orthogonal complement of the inflated `Reg(G_(a-1))` inside `Reg(G_a)`.
For every fixed nonidentity group element (in particular every fixed
principal-congruence or root element), both regular characters vanish once
`a-1` exceeds the element's separation depth, so the shell character also
vanishes.  The weighted characters of `(RTE2)` therefore converge to the
regular character.

This last construction is an abstract scalar feasibility packet, not a
claim that the couplings `(RTE2)` are realized by genuine selected vertex
irreducibles: the displayed flow is not asserted to be the actual branching
coupling of the Plancherel shells.  Its point is exact: canonical trace,
band escape, and the current two-thirds flow inequalities alone have a
common model, so no contradiction can be derived from those data.  Closing
the diffuse `K->infinity` gate requires a label-sensitive branching or
character-ratio inequality coupling the within-band character to its
upper/opposite restriction multiplicities; scalar band masses and fixed-word
traces are insufficient.
