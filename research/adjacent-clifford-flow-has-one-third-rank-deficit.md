---
rg: 2
id: adjacent-clifford-flow-has-one-third-rank-deficit
kind: claim
title: Every replenished adjacent Clifford flow has a one-third physical-rank deficit
distinct_from:
  adjacent-clifford-orbit-transition-graph: that records sharp source capacities of each orbit arrow; this adds the target inertia-space capacities and rules out simultaneous saturation even with fresh fixed-orbit injections at every depth.
  sparse-dyadic-iwahori-packets-have-a-uniform-boundary: that gives a support-size-dependent floor for arbitrary conductor couplings; this gives a support-size-independent one-third loss for the adjacent-only Clifford flow proposed by the scalar counterprofile.
  pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss: that uses Plancherel branching weights; this applies to arbitrary selected Clifford labels and multiplicities.
  dyadic-ob-inertia-arrows-have-exact-induction-functors: that constructs each OF-to-OB and OB-to-OB arrow and records its dimension inflation separately; this sums target eigenspace capacities in both conductor directions and proves that no simultaneous adjacent replenishment exceeds two-thirds total common rank.
---

Let `Pi_+`,`Pi_-` be equal-dimensional pure dyadic vertex packets, supported
on exact conductors at least three.  Let `H_adj` be any common
subrepresentation of their upper/opposite edge restrictions which is the
orthogonal sum of matches between adjacent conductor bands only:

```text
H_up:   plus depth a  -> minus depth a+1,
H_down: plus depth a  -> minus depth a-1.               (ACF1)
```

Then, for arbitrary newest-layer Clifford orbits, projective inertia labels,
and multiplicities,

```text
dim(H_up)<=d/3,       dim(H_down)<=d/3,
dim(H_adj)<=2d/3.                                      (ACF2)
```

The constants are target-side inertia dimensions, not merely source orbit
capacities.  In particular they remain valid if a fresh full-inertia
`O_F` packet is injected at every depth, or if all recurrent sources are in
`O_B`.  If every common edge constituent of the two packets occurs in
`(ACF1)`, Selberg `(tau)` converts `(ACF2)` into the defect floor

```text
max_(s in S_B)||rho(s)V-V eta(s)||_2 >= kappa_B/sqrt(3) (ACF3)
```

for the full comparison.

At label level the upward functor is explicit.  A participating source
Iwahori label has target newest-layer character `ell_B=(0,1,0)`.  Its
inertia group in `G_(a+1)` is exactly the opposite index-three Iwahori
`I_B`, and Clifford induction gives

```text
xi  |->  Ind_(I_B)^(G_(a+1)) xi,                       (ACF4)
dim Ind(xi)=3 dim(xi).                                  (ACF5)
```

The inducing `ell_B`-eigenspace is one third of the target; the other two
thirds are the two conjugate newest-layer character spaces.  Thus an
`O_F(depth a)->O_B(depth a+1)` source can be fully embedded, but doing so
creates exactly twice its physical rank as unmatched target baggage.
For `O_B->O_B`, the same induction applies separately to its participating
root-character block; the recurrent source capacity `2/3` does not enlarge
the target's `1/3` inducing slot.

Therefore the drifting symmetric nearest-neighbor scalar flow of
`regular-trace-allows-diffuse-dyadic-flow` has no realization by these
Clifford labels: it requested one half of each target from below, while the
exact target capacity is one third.  This does not yet exclude packets using
same-depth or non-adjacent lower-conductor subspaces; `(ACF2)` isolates a
fixed deficit for the proposed adjacent recursive mechanism.
