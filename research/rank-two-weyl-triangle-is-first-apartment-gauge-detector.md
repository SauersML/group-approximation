---
rg: 2
id: rank-two-weyl-triangle-is-first-apartment-gauge-detector
kind: claim
title: The rank-two Weyl triangle is the first relation that detects the independent-overlap tensor swap
distinct_from:
  affine-weyl-apartment-has-independent-lamp-models: that constructs finite canonical models when only the affine-Weyl actor and apartment lamps are retained; this includes the full finite coefficient/root packet in one h-direction and identifies the exact rank-two word on which the tensor-swap gauge fails.
  odd-congruence-lambda-exact-sector-collapses: that uses property T and congruence exactification to kill every corrector in the odd-congruence ultraproduct sector; this is the finite matrix normal form showing why one direction cannot work and why the three-term relation is exactly sharp for the four projection atoms.
  commuting-conjugate-involution-transfer-for-sl3-pair: that asks for overlap collapse in arbitrary canonical matrix microstates; this proves it only after a common full-coefficient inner slot has been decoded and explicitly shows what escapes without the rank-two compatibility.
---

Let `F` be a finite group, let `g in F`, and let

```text
pi = lambda_F tensor 1_2 : F -> U(E),
E = l^2(F) tensor C^2.
```

Let `e` be a rank-one projection on `C^2`, put

```text
p_0 = 1 tensor e in pi(F)',
H = E tensor E,
rho(f) = pi(f) tensor pi(f),
P = p_0 tensor 1_E,
Z(x tensor y) = y tensor x,
V = rho(g) Z.                                             (RWT1)
```

Then `Z` commutes with `rho(F)`, and

```text
V rho(f) V^* = rho(g f g^-1)             (f in F).        (RWT2)
```

Thus `V` implements the complete inner coefficient transport, not merely a
few selected root equations.  Nevertheless, for

```text
Q = V P V^*,
```

one has

```text
Q = 1_E tensor p_0,
[P,Q]=0,
tr(P)=tr(Q)=1/2,
tr(PQ)=1/4.                                             (RWT3)
```

Equivalently the balanced involution `c=1-2P` commutes with `rho(F)`, its
`V`-conjugate commutes with it, and

```text
tr(c V c V^*)=0.                                       (RWT4)
```

This is an exact finite-dimensional realization of the forbidden interior
overlap.  It survives **every** relation internal to the finite coefficient
group and every one-direction equation saying that `h` conjugates a root
packet by an inner finite-quotient slot.  The escape is entirely in the
commutant multiplicity: `Z` exchanges the two identical coefficient factors.

## The first detecting word

Now use the rank-two diagonal packet of `SL_3`.  Put

```text
h   = diag(p,1,p^-1),
h'  = w_12 h w_12^-1,
h'' = w_23 h w_23^-1.
```

With the standard signed permutation representatives,

```text
h (h'')^-1 = h'.                                       (RWT5)
```

Suppose a finite coefficient model has inner slots `G,G',G''` satisfying
the same coefficient identity `G (G'')^-1=G'`, and suppose the three lifted
diagonals have one common corrector `Z` in the full coefficient commutant:

```text
V=GZ,          V'=G'Z,          V''=G''Z.               (RWT6)
```

The common-corrector conclusion is exactly what Weyl conjugacy gives when
`Z` commutes with the full coefficient image, since then
`w Z w^-1=Z`.  Substitution of `(RWT6)` into `(RWT5)` gives

```text
V (V'')^-1 = G Z Z^-1 (G'')^-1 = G' = V' Z^-1.
```

Hence the group relation `V(V'')^-1=V'` forces

```text
Z=1.                                                    (RWT7)
```

In particular `V=G` lies in the coefficient algebra and preserves every
projection in its commutant, so `Q=P` and `tr(PQ)=1/2`.  The tensor-swap
model `(RWT1)` fails precisely at this word: all three Weyl conjugates carry
the same swap, the two swaps on the left cancel, and the uncancelled swap on
the right remains.

## Consequence for the full scalar gate

One cross-apartment root direction, even enlarged to the whole finite
coefficient group and exact inner conjugation, cannot exclude `a=1/4`.
The minimal successful algebraic shape is the rank-two Weyl triangle plus a
proof that the three directions share one corrector in the **full**
coefficient commutant.

That common-gauge extraction is automatic in the exact odd-congruence sector
and is exactly why `odd-congruence-lambda-exact-sector-collapses` works.  It
is unavailable for the live `G_cc` enemy: an arbitrary approximate
`SL_3(Z)` restriction may have no nearby exact coefficient slot, and its
three directional correctors may live only in different parahoric
commutants.  Therefore the remaining matrix-coordinate theorem is now
sharply localized:

```text
root-group gluing + canonical matrix coordinates
  ==> one common full-C commutant gauge on positive four-atom mass. (RWT8)
```

Once `(RWT8)` is proved, the finite three-term calculation above collapses
the interior overlap.  Without `(RWT8)`, the exact tensor-swap model proves
that one-direction root packets have no scalar leverage.
