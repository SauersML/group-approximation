---
rg: 2
id: gauge-pair-holonomy-needs-one-source-moment
kind: claim
title: Gauge-pair free-phase holonomy makes the common Gram automatic and leaves one mixed moment
distinct_from:
  one-binary-marginal-block-escape: that moves two same-sign coordinate atoms outside one finite root block; this applies that construction to the two-share gauge orbit and computes the resulting common-source Fanizza decoder.
  isotypic-finite-edge-forces-full-commuting-selector-support: that excludes a logical-invariant finite edge type; this uses a multi-piece algebraic corner unitary which acts nontrivially on the two shares while fixing their logical product.
  capacity-gated-common-source-gram-word-cell: that asks for ordinary group-word control of all common-source context rows; this makes the common Gram exact algebraically and isolates the single finite mixed Hecke moment which the word cell must pay.
---

Fix one gauge-doubled logical selector

```text
X=A B,                 [A,B]=1,                         (GFM1)
```

and a selected finite packet corner

```text
q C[K]q = M_D(C)
```

whose coordinate atoms occur in gauge pairs

```text
(a,b) <-> (-a,-b).                                     (GFM2)
```

The two coordinates in `(GFM2)` have the same logical sign `x=ab`.  After
the standard gauge-orbit covariantization they also have the same
multiplicity.

On every such two-coordinate fiber take a Hadamard rotation `H`, and put
`H=1` on any unpaired complement.  Let `(e_j)` be the coordinate minimal
projections, adjoin independent free letters `(h_j)`, and set

```text
W=sum_j h_j e_j,                 V=W H.                 (GFM3)
```

Exactly as in `one-binary-marginal-block-escape`, `W` and `V` are finite
support algebraic unitaries in the corner.  If `x` is the diagonal packet
involution carrying the logical products, then

```text
[V,x]=0,                 V^*V=VV^*=q.                  (GFM4)
```

But `V` does not preserve the individual share diagonals `a,b`; the
Hadamard block mixes their two opposite sign vectors.  The conjugated share
and assignment projections contain nonzero coefficients at free reduced
words `h_r h_s^(-1)` and leave `qC[K]q`.

Thus a nontrivial Hecke holonomy **can** evade logical-selector
centralization while preserving exact completeness.  It evades
`isotypic-finite-edge-forces-full-commuting-selector-support` for the precise
reason required there: `V` is a multi-piece algebraic corner unitary carrying
the individual gauge-share direction, not one finite HNN edge type invisible
to the logical product.

## Common-source computation

Let `Q<=q` be any projection; in the Fanizza application it is the
capacity-gated leakage projection `(1-C)E`.  For a context `c`, choose a
gauge-pair holonomy `V_c` as above and define

```text
S_c=V_c^* Q.                                             (GFM5)
```

Thus the packet design must place the capacity and exit projections in the
common selected corner `q`; this containment is an explicit hypothesis, not
an automatic consequence of gauge doubling.

Then the source Gram is literal and independent of `c`:

```text
S_c^*S_c=Q.                                             (GFM6)
```

Let `a_(c,u)` denote either one target share involution or the target logical
product in the selected allowed packet, and let `Z_u` be the corresponding
original shared Fanizza word.  The entire covariance row is the scalar

```text
mu_(c,u)(Q)
 =||a_(c,u)V_c^*Q-V_c^*QZ_u||_2^2.                     (GFM7)
```

Because all factors have fixed finite Hecke support, `(GFM7)` is a fixed
finite linear combination of ordinary mixed trace moments.  Summing one
share and the logical product for each gauge pair is enough: covariance of
the second share follows from `B=XA`, fixed-word telescoping, and the lifted
context commutation relations.

The target allowed-context residuals vanish on the selected root packet.
Consequently

```text
M_Q=sum_(c,u) mu_(c,u)(Q)                               (GFM8)
```

is the only remaining analytic input to
`capacity-gated-common-corner-bcs-two-cell`.  Namely, an ordinary word cell
proving

```text
M_Q <= K E_rel+o(1)                                    (GFM9)
```

immediately supplies `(CSG2)--(CSG3)` with the same source `Q` for all four
contexts and hence proves `NCL13`.

## The one-word/full-corner specialization

For `Q=q`, write

```text
d_(c,u)=V_c a_(c,u)V_c^*.
```

Then `(GFM7)` becomes the single mixed Hecke-word moment

```text
mu_(c,u)(q)
 =||d_(c,u)-Z_u q||_2^2
 =2 tau(q)-2 Re tau(d_(c,u) Z_u q).                    (GFM10)
```

Thus full overlap of the prescribed word with the escaped packet selector is
one scalar, not a family of block equations.  Vanishing of `(GFM10)` gives

```text
Z_u q=d_(c,u),          Z_u q Z_u^*=q,                 (GFM11)
```

so the prescribed word reduces the corner and agrees there with the escaped
selector.  Approximate vanishing gives exactly the square-root HS covariance
error, with no dependence on ambient dimension.

## Exact HALT firewall

The cell does not require a tracial extension.  Gauge-orbit
covariantization gives equal multiplicity to the two share assignments in
`(GFM2)`, and countable amplification makes every retained multiplicity
infinite.  Hence the Hadamard and context transports exist exactly without
changing `X=AB` or the native Fanizza mark.  On a HALT branch where the
forbidden capacity-gated `Q` vanishes, `(GFM5)--(GFM9)` are vacuous.

This audit is deliberately about completeness of the Hecke geometry, not a
claim that `(GFM9)` already follows from ordinary relators.

## Remaining ordinary-word issue

The block-escaping `V_c` is a finite **sum** of group translates.  It is not
one group generator.  Replacing it by a single compressed word loses the
coordinate-dependent free phases: full source support of `qgq` forces `g`
to normalize `q`, and for a primitive finite root packet an honest packet
normalizer keeps the root matrix algebra invariant (up to an external
multiplicity unitary).

Therefore the smallest surviving construction target is exactly `(GFM9)`:
linearize the finite Hecke sum by a root/Steinberg or another non-Bass--Serre
two-cell and make its capacity-gated mixed moment pay defining word energy.
No further source-Gram alignment theorem is required once `(GFM3)` is
available.
