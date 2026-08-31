---
rg: 2
id: commuting-raw-qutrit-router-has-active-rank-ceiling
kind: claim
title: A commuting raw qutrit router cannot fill the active head, while an unconstrained rectangular row fills it only by a finite gauge
artifacts:
  - research/commuting-raw-qutrit-router-rank-ceiling-proof.md
distinct_from:
  three-carrier-hidden-line-join-crosses-target-but-has-no-range: that proves the two-character source crosses the target before routing; this computes the best possible one-character range after every commuting raw router.
  jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16: that supplies the 20, 18, and 16 head ranks; this separates the immutable active rank from the movable qutrit character.
  qutrit-complementary-jacobson-signs-minimal-router-finite: that gives one acyclic finite packet; this covers arbitrary finite parallel S/T orbit packets and also identifies the exact rectangular gauge which lies outside them.
---

Remove the central qutrit line `<h>` from the 288-dimensional sign
packet.  The remaining active finite factor has order 96.  In its regular
representation the polar support of the selected sign row has rank

```text
r_+=10,                         r_-=9,                    (CRQ1)
```

whereas the active part of the target `Ee_2` has rank 16.  The two
source qutrit characters account for the known ranks `20/288=5/72`
and `18/288=1/16`.

Let `N` be any finite packet of literal raw `S` or `T` roots on
unused, product-zero block positions.  Assume it is closed under the
qutrit orbit, commutes with the active 96-dimensional factor, and may be
moved by `h`.  Then every full-`C` Fourier row which starts on the
selected active polar and ends in one `h` character has range trace at
most

```text
10/288=5/144              in the all-plus row,
 9/288=1/32               in every other surviving row. (CRQ2)
```

This ceiling is independent of the number of parallel roots.  Both
values are below the target:

```text
1/18-5/144=1/48,          1/18-1/32=7/288.              (CRQ3)
```

The reason is not the earlier quarter kernel.  Even a perfect Fourier
router can move the `h` character but, because it commutes with the
active factor, it cannot enlarge active rank 10 or 9 to rank 16.

The local raw packet is finite.  Product-zero root positions make
`N` an elementary abelian 2-group; the complete local group has order

```text
288 |N|.
```

For `N isomorphic to F_2^(2m)` this is `288*4^m`.  Thus literal
uncollected raw labels do not by themselves escape the finite absorber.

There is an exact complementary optimizer, but it exposes the missing
relation rather than closing it.  In the 288-dimensional regular head,
choose rank-eight subspaces in each of the two source-character blocks
and a unitary sending their direct sum onto the rank-sixteen target.
The compression is a partial isometry with

```text
T^*T=P_0,             TT^*=Ee_2,             s_min(T|P_0)=1, (CRQ4)
```

and `rank(P_0)=16`.  It discards exactly 4 dimensions in the all-plus
row and 2 in the other row, namely normalized traces `1/72` and
`1/144`.  Its two rank-eight branches have exact full-`C` source and
target typing.

Consequently full target, trace `1/18`, and a uniform singular floor
are analytically compatible.  They become nontrivial only if a mixed
raw return relation selects those two rank-eight source subspaces from
the already named Lin occurrence.  A commuting raw packet cannot do so,
while an unconstrained rectangular unitary chooses them by gauge.  When
tensored with a Lin projection, the optimizer has source
`P_0 tensor p` and target `Ee_2 tensor p`; it preserves the entire
occurrence multiplicity and is Morita-neutral.  The nonhyperlinear-group
root therefore remains open.

DERIVATION
commuting-raw-qutrit-router-rank-ceiling-proof
