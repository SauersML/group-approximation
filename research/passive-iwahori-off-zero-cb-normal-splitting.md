---
rg: 2
id: passive-iwahori-off-zero-cb-normal-splitting
kind: claim
title: The passive Iwahori Jacobian has a uniform off-zero completely bounded normal splitting
distinct_from:
  gauge-optimized-target-has-uniform-congruence-tangent-gap: that gives a level-independent normalized-HS inverse only at exact congruence endpoints; this asks for a mixed L2/operator-norm splitting at the approximate passive tuple itself.
  bs14-thresholded-newton-needs-coordinate-basin: that assumes an operator-norm coordinate tube around a previously selected endpoint; this splitting would construct the endpoint by Newton without selecting it first.
  authenticated-core-union-basin-is-relative-liftability: that is the qualitative global lifting statement; this is a concrete local analytic sufficient condition on the passive operator-small region.
  normalized-hs-taylor-remainder-is-not-dimension-free: that proves an L2-only Newton argument is invalid; the operator-norm half of the splitting below is exactly what pays its mixed-norm remainder.
---

**OPEN; STRONG SUFFICIENT PASSIVE CONDITION.**  Work on the smooth constraint
manifold `M_(R,S)` of involutions satisfying `XRX=R^(-1)` over one supplied
exact `BS(1,4)` core `(R,S)`, modulo the genuine gauge.  (There is no
corresponding fixed-core relation forcing `X` to invert `S`; its interaction
with `S` is carried by the cubic rows.)  Let `F` be the pair of remaining
cubic Iwahori rows, expressed in a fixed local unitary chart.  There should
be constants

```text
theta_0>0,       C_2<infinity,       C_infinity<infinity,          (PCB1)
```

independent of matrix dimension, congruence level, multiplicity, and the
exact regular core, with the following property.  At every passive tuple
`x in M_(R,S)` satisfying

```text
||F(x)||_op <= theta_0,                                      (PCB2)
```

there is a gauge-normal linear correction operator `G_x` on the two-row
residual space such that, for `p=2,infinity`,

```text
||G_x y||_p <= C_p ||y||_p,                                 (PCB3)
||DF_x G_x y-y||_p <= C_0 ||F(x)||_op ||y||_p.               (PCB4)
```

Here `C_infinity` means an operator-space/completely bounded estimate, not
the already established Hilbert-space inverse.  The correction lies in the
tangent space of `M_(R,S)`, so the exact BS core, involution, and inversion
rows are retained by the chart retraction.

The `O(||F(x)||_op)` error in `(PCB4)` permits a normal splitting written
in approximate coordinates; an exact right inverse is a stronger special
case.  It is important that the assertion is made **off the zero locus**.
An inverse known only at a chosen exact endpoint is circular here, because
finding that endpoint is the coordinate-basin problem.

`gauge-optimized-target-has-uniform-congruence-tangent-gap` supplies the
`2 -> 2` part of `(PCB3)` at exact endpoints after quotienting the correct
gauge.  It supplies neither the `infinity -> infinity` bound nor `(PCB4)`
throughout the passive region.  Thus `(PCB1)--(PCB4)` are the precise new
analytic content, not a restatement of the known tangent gap.

The route `off-zero-cb-newton-closes-passive-iwahori` proves that this
single assertion integrates the passive tuple to an exact moving endpoint
with dimension-free normalized-HS cost.  In particular it bypasses, rather
than assumes, prior operator-norm basin entry.  The tempting weakening to an
off-zero `2 -> 2` splitting followed by spectral truncation is refuted by
`relative-tangent-spectral-cuts-can-have-full-bs-hull`: a relative tangent
commutes with `R`, but need not commute with `S`, and a rank-two high cut can
generate the whole BS packet.

Nor can one repair that failure by imposing `[h,S]=0` on the correction.
`full-core-central-relative-tangent-is-zero-near-first-cubic` gives the
sharp identity

```text
Ad_((XS^2)^3)(h)=-h
```

for every such tangent.  If the first cubic has operator defect below one,
this forces `h=0`.  Therefore the surviving cb theorem must control the
genuine non-`S`-central tangent directions directly; neither full-core
centralization nor spectral reduction is available.
