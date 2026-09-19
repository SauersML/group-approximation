---
rg: 2
id: leavitt-steinberg-bounded-area-carmichael-lift
kind: claim
title: Bound the filling area of the lifted Thompson Carmichael stars inside St20 of the binary Leavitt algebra
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that asks for bounded area in the Bleak--Quick R1--R5 presentation of V; this permits fillings through the much larger finitely presented Steinberg group and its Leavitt coefficient relations.
  leavitt-steinberg-quadratic-radius-pressure: that gives O(n^2) word radius for canonical depth-n prefix roots and explicitly allows error to grow; this asks whether the special common-pivot permutation loops admit a uniform filling shortcut.
  diagonal-leavitt-prefix-transport-cannot-carry-cross-corners: that proves the existing diagonal Whitehead cell is insufficient; this is the surviving target allowing a new stabilized rectangular Morita mechanism or a different bounded diagram.
---

Let `R=L_2(F_2)`, fix a finite presentation

```text
Delta=St_20(R)=<X | R_St>,
```

and use the unique lifted Thompson subgroup
`iota:V->Delta`.  Fix a nontrivial three-cycle `b in iota(V)`.  Prove that
there is one integer `L` such that, for every `M`, one can choose a maximal
prefix code with pivots `p,q`, variable leaves `c_1,...,c_M`, word
representatives

```text
u_i=iota((p q c_i))=h_i b h_i^(-1),
```

and

```text
Area_(R_St)(u_i^3)<=L,
Area_(R_St)((u_i u_j)^2)<=L            (i!=j).             (LSC1)
```

Exact packet existence and the absence of a central lifting phase are
already established by `thompson-v-lifts-through-binary-leavitt-steinberg-cover`.
The open content is only the uniform area in `(LSC1)`.

## Attempts

The standard coefficient derivation does not prove `(LSC1)`: depth-`n`
prefix roots currently have `O(n^2)` word radius, and the common-pivot cycles
contain off-diagonal coefficients `s_u t_v`.  By
`diagonal-leavitt-prefix-transport-cannot-carry-cross-corners`, the available
diagonal Whitehead endomorphisms cannot transport these roots recursively.
The smallest positive replacement is a fixed stabilized rectangular Morita
cell which transports the whole local three-by-three permutation chart—not
the nonmultiplicative coefficient map `a |-> s_u a t_v` rootwise—and whose
overlap on two common-pivot charts has a bounded Steinberg diagram.

The replacement must fill each **combined edge loop** directly.
`finite-mark-centralizer-commutator-area-is-proper` applies in the ambient
group `Delta` as well as inside `V`: distinct correction permutations in
`C_Delta(b)/<b>` escape every bounded Schreier ball, so their individual
commutators with `b` cannot have uniformly bounded area.  Thus the larger
Steinberg presentation does not revive the common-frame proof by two
separately bounded centralizer corrections.  Only an interacting chart
diagram in which the two twisted flows cancel after the vertices are
combined can still establish `(LSC1)`.

Two further constraints now make that interface precise.  First,
`collective-centralizer-cycles-are-free-gauge-identities` shows that a scalar
product of corrections around a cycle freely telescopes: it has zero cost
because it has zero information.  Second,
`a5-carmichael-triangle-covers-involution-kernels` gives the surviving
fixed-size positive mechanism.  The three edge involutions of one Carmichael
triangle have a uniform sum-of-squares gap in every representation of its
local `A_5`.  Thus a stabilized rectangular Morita cell may keep those three
edge defects in separate channels and use the `A_5` gap; it cannot merely
multiply them into one cycle boundary.

Even that separation is not by itself a filling shortcut.
`orthogonal-centralizer-channels-retain-area-properness` proves that a fixed
direct sum of the individual endpoint-correction loops still has proper
ambient filling area, under arbitrary fixed channel mixing.  Accordingly the
rectangular cell must output the three **combined edge defects themselves**
at bounded cost.  It cannot first fill the three centralizer commutators and
then invoke the `A_5` inequality.

If `(LSC1)` holds, `bounded-area-high-chromatic-conjugacy-collapse` applied to
the complete graphs `K_M` kills `b` in every tracial matrix ultraproduct.
Since `b!=1` in `Delta`, this proves that the explicit finitely presented
property-`(T)` group `St_20(L_2(F_2))` is nonhyperlinear.
