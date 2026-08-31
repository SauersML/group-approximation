---
rg: 2
id: two-coordinate-relators-leave-stable-laurent-k2
kind: claim
title: Two inverse-coordinate relators still leave the stable Laurent K2 obstruction
distinct_from:
  one-opposite-steinberg-relator-does-not-close-laurent-cycle: that gives a finite fixed-rank model proving one coordinate word does not imply the other; this kills both coordinate words after stabilization and detects a further infinite K2 quotient
  farey-tree-lift-hits-opposite-steinberg-cycle: that identifies a missing cross-cone Steinberg relation; this shows the full stable obstruction is not exhausted by the two obvious inverse-coordinate relations
  opposite-transvections-are-first-nonore-relative-gate: that is the fixed-rank r>=3 group/RE problem; this is a stable algebraic firewall and explicitly does not decide the unstable rank-three quotient
---

Let `E_inf(R)` and `St(R)` denote the stable elementary and Steinberg
groups.  Form

```text
H_inf=E_inf(R_+) *_(E_inf(R_0)) E_inf(R_-)
```

and let `Q_2` be its quotient by the normal closure of

```text
w_i=[e_12(x_i),e_23(x_i^(-1))]e_13(-1),       i=1,2.
```

The canonical map

```text
q:Q_2 -> E_inf(R_pm)                                         (TKO1)
```

is not injective.  More sharply, there is a surjection

```text
ker(q) ->> K2(R_pm).                                         (TKO2)
```

For a finite coefficient field `k`, homotopy invariance and the fundamental
theorem for Laurent polynomial rings give

```text
K2(R_pm)
 ~= K2(k) (+) K1(k) (+) K1(k) (+) K0(k)
 ~= (k^*)^2 (+) Z.                                           (TKO3)
```

In particular, the residual kernel has an infinite cyclic quotient.  The
`Z` summand is the two-torus class represented by the Steinberg symbol
`{x_1,x_2}`.

The same conclusion holds at finite matrix rank in the classical stability
range.  If `r>=d+3`, form

```text
H_r=E_r(R_+) *_(E_r(R_0)) E_r(R_-)
```

and quotient by the same two words.  The kernel of the canonical map to
`E_r(R_pm)` still surjects onto the group in (TKO3), because
`K2(r,R)=K2(R)` for all four rings in this range.

Thus the two ring-level inverse equations do not give a rank-uniform
presentation of the Laurent elementary group from the two polynomial cone
groups.  They first produce a group surjecting onto the Laurent Steinberg
group; killing its nonzero `K2` is an additional relation packet.

This is a stable-range theorem, not a rank-three theorem.  It applies to the
actual finite-rank Kun--Thom family whenever `r>=d+3`.  Unstable
`K2(3,R_pm)` and the relevant low-rank maps require separate control, so it
does not prove that the pinned rank-three opposite slice is negative or
non-RE.  It does rule out any proof that treats the two coordinate words as a
complete rank-independent quotient presentation.

DERIVATION
polynomial-k2-vanishing-lifts-cones-to-laurent-steinberg-proof
