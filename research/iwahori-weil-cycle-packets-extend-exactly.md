---
rg: 2
id: iwahori-weil-cycle-packets-extend-exactly
kind: claim
title: Quadratic-residue BS(1,4) cycle packets extend exactly through the two Iwahori cubics
artifacts:
  - experiments/bs14_cycle_packet_probe.py
  - experiments/bs14-cycle-packet-probe-smoke.json
distinct_from:
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies every exact metabelian packet; this identifies an arithmetic family, for every prime satisfying the stated order condition, on which the remaining involution exists exactly.
  bs14-relative-involution-extension-stability: that asks for uniform approximate repair over arbitrary sums and multiplicity monodromies; this is an exact multiplicity-one family and does not supply the uniform modulus.
---

Let `p>=7` be a prime with

```text
p=3 mod 4,             ord_p(4)=(p-1)/2=:m.            (WP1)
```

Then the multiplicity-one `BS(1,4)` cycle packet whose `S`-spectrum is the
single fourth-power orbit of a primitive `p`-th root and whose return
monodromy is `+1` admits an involution `X` satisfying exactly

```text
X R X=R^(-1),
(X S^2)^3=1,
(X R S)^3=1.                                         (WP2)
```

The extension is the `(p-1)/2`-dimensional Weil constituent of
`PSL_2(F_p)`, evaluated on the reductions of the arithmetic matrices

```text
x=[[0,-1],[1,0]],
r=diag(2,1/2),
s=[[1,1/2],[0,1]].                                   (WP3)
```

The standard unipotent eigenbasis of this Weil constituent is indexed by
`F_p^*/{+-1}`.  The eigenvalues of `s` are an additive character evaluated
on a fixed nonzero quadratic-residue multiple of `t^2`; hence they are the
quadratic residues in the exponent, each once.  Condition `(WP1)` says that
this is one fourth-power orbit.  The diagonal element `r` transports
`t^2` by multiplication by `4`.  Moreover `4^m=1` implies `2^m=+-1`, so
`r^m=1` in `PSL_2(F_p)` and the cycle monodromy is `+1`.

Finally the matrices `(WP3)` satisfy the exact presentation
`iwahori-square-root-presentation-is-bs14-plus-one-involution` inside
`PSL_2(F_p)`.  Their Weil images therefore satisfy `(WP2)`.

The bounded probe recovers this family at `p=7,11,19,23,47` and rejects the
tested non-family prime `43` by a large residual.  Those computations are
only a diagnostic; the construction above is exact.  The family shows why
the relative stability problem cannot kill every nontrivial periodic packet:
it must recognize and retain the arithmetic Weil packets while charging or
repairing the nonextendable packet mass.
