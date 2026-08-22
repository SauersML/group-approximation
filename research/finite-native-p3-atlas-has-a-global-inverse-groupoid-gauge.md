---
rg: 2
id: finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge
kind: claim
title: Every finite native p-three chart atlas has one global inverse groupoid gauge
distinct_from:
  two-native-p3-weyl-charts-have-the-same-mackey-class: that computes equality on one pairwise overlap; this retains every triple and higher composition in a finite atlas and constructs one simultaneous gauge.
  maslov-finite-subgroup-atlas-no-go: that balances only projective irreducible multiplicity vectors across finite-subgroup restrictions; this includes the transition intertwiners, their scalar factor sets, and all triple-overlap composition laws.
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that uses one literal finite Chevalley packet to kill an external corrector in its coefficient commutant; this concerns the intrinsic projective oscillator factor set and shows that its inverse multiplicity representation always yields an honest full packet.
---

Fix a conductor level and any finite family of native p-three oscillator
charts.  Form the finite transition groupoid `G`: its objects are the chart
types and its arrows are the retained Weyl, opposite-root, parahoric, and
overlap transports.  Stone--von Neumann uniqueness makes the oscillator
transport a projective functor.  For composable arrows write

```text
W_g W_h = alpha(g,h) W_(gh).                            (FGA1)
```

Operator associativity gives

```text
alpha(g,h) alpha(gh,k)
 = alpha(h,k) alpha(g,hk).                              (FGA2)
```

Hence the purported triple-overlap associator is identically trivial:
`delta alpha=1`.  A product of pairwise chart gauges around a triangle may
still be a nontrivial scalar, but it is the ordinary `H^2(G,T)` projective
holonomy represented by `alpha`, not an additional `H^3` obstruction.  The
object-only Cech direction is a pair-groupoid coboundary; the remaining class
is the common isotropy/Mackey class already present in one oscillator packet.

Every finite groupoid cocycle has an exact finite-dimensional inverse
twisted-regular representation.  For each object `x`, let `M_x` have basis
the arrows ending at `x`.  Left composition, weighted by `alpha^(-1)`, gives
maps `Lambda_g:M_(s(g))->M_(t(g))` satisfying

```text
Lambda_g Lambda_h = alpha(g,h)^(-1) Lambda_(gh).        (FGA3)
```

Therefore

```text
R_g = W_g tensor Lambda_g                              (FGA4)
```

is an honest functor on the entire chart groupoid.  It satisfies every
pairwise, triple, and higher native transition relation exactly.  Its
multiplicity is finite, bounded by the number of arrows entering an object
(and hence by `|Mor(G)|`).  Direct sums provide arbitrary further common
multiplicity.

For the p-three Weil--Maslov system, all Weyl/opposite-root restrictions are
the same order-two metaplectic class by
`two-native-p3-weyl-charts-have-the-same-mackey-class`; `(FGA3)` is the global
version of the Pauli inverse sign.  Thus no fixed finite native parahoric
atlas, including the full six-chart `A_2` cycle, yields an uncancelled
triple-overlap scalar or a dimension-independent normalized-HS gap.  The
countermodel has zero defect.

A genuine survivor must exceed this finite groupoid datum: force a
same-model multiplicity ceiling below the twisted-regular dimension, activate
projective commutator rank growing with the model, or impose a global
identification that is not a functor of the native chart groupoid.  Adding
more native charts at one fixed finite level does not suffice.

For the canonical regular congruence sectors, even the first two formulations
do not follow from conductor depth.  By
`regular-p3-parahoric-bands-have-twisted-gauge-surplus`, every regular
parahoric type block already contains `dim(pi)` copies of its complete
inverse twisted-regular gauge.  Different depths are orthogonal direct-sum
bands, so their capacity costs add rather than tensor.  A supercritical route
must first authenticate one shared multiplicity reservoir across depths.
