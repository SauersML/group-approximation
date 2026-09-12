---
rg: 2
id: cyclic-core-character-forces-linear-rms-section-area
kind: claim
title: A cyclic core character forces linear RMS section area at the dyadic level
distinct_from:
  induced-rounding-needs-rms-section-fillings: that gives a sufficient induced-projection repair when the RMS section area is sub-square-root; this proves every section has linear RMS area on the native dyadic quotients.
  repeated-squaring-and-tau-do-not-supply-the-moving-basin: that gives an abstract scalar conditioning firewall; this uses the actual BS14 core character and the actual finite arithmetic quotient to refute the proposed section estimate.
  regular-iwahori-edge-types-have-moving-power-charge: that detects a moving exact edge type against frozen-type padding; this gives a relative two-cell lower bound and remains valid after tensoring with the regular congruence model.
---

Put `N=4^K-1`, `K>=2`, and let

```text
A_N=PSL_2(Z[1/2])/<<s^N>>,       B_N=<r,s><A_N.       (CCA1)
```

For every right-coset section and every choice of its representing words,
the RMS relative filling constant `M_N` in
`induced-rounding-needs-rms-section-fillings` satisfies

```text
M_N>=c K                                                   (CCA2)
```

for one constant `c>0` coming only from the uniform Selberg gap and the
fixed generating set.  In particular the required estimate
`M_N=o(sqrt(K))` is false, not merely unproved.

The obstruction is the core character

```text
chi_K(r)=1 in Z/K,               chi_K(s)=0.           (CCA3)
```

It is well defined on `B_N`.  Indeed `s` has order exactly `N`: the quotient
maps onto reduction modulo `N`, where the unipotent still has order `N`.
If a relation in `B_N` has `r`-exponent `j`, conjugating `s` by that relation
gives `s=s^(4^j)`.  Since the order of `4` modulo `4^K-1` is exactly `K`,
one has `K|j`.

Let `zeta=exp(2 pi i/K)` and `theta_K=zeta^(chi_K)`.  This is a nontrivial
character of `B_N`, so `Ind_(B_N)^(A_N)(theta_K)` has no invariant vector.
For a chosen section, take the flat unit vector whose phase at a coset is
`zeta` raised to the `r`-exponent of its section word.  The uniform Cayley
gap says that the average squared phase discrepancy on its generator edges
is at least a fixed `kappa>0`.

On the other hand extend `chi_K` to the relative free product by sending
`x` to zero.  The four endpoint relators have charges

```text
x^2:0,       (xr)^2:2,
(xs^2)^3:0,  (xrs)^3:3.                              (CCA4)
```

Core and `s^N` cells have charge zero.  Therefore a section edge loop of
relative area `a` has phase discrepancy at most

```text
max(|zeta^2-1|,|zeta^3-1|) a <= (6 pi/K)a.            (CCA5)
```

Squaring `(CCA5)`, averaging the generator edges, and applying the gap gives
`(CCA2)` for every section.

This is a firewall for **fixed-core induction**, not a counterexample to
flexible repair.  The scalar tuple

```text
r=zeta,       s=1,       x=1                           (CCA6)
```

has endpoint defect `O(1/K)` and is `O(1/K)` from the trivial exact tuple
after moving `r`.  More strongly, tensor `(CCA6)` with the regular
representation of any congruence image at this level.  The resulting exact
core is regular and isomorphic to the untwisted regular core, the raw tuple
has canonical limiting character, and moving `r` by `|zeta-1|` repairs it.
Nevertheless its section edge energy stays bounded below by `kappa`, so the
proposed energy estimate `(IRF8)` also fails uniformly on authenticated
regular cores.

Thus property tau averaging after freezing the core necessarily magnifies a
harmless `O(1/K)` continuous core motion into constant section energy.  A
successful proof must first optimize over nearby exact core coordinates, or
replace individual diagram telescoping by a gauge-optimized relative
two-dimensional inequality.  The minimal such sufficient statement is
`gauge-optimized-section-energy-controls-flexible-repair`.
