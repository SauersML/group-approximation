---
rg: 2
id: clifford-direct-sum-dilution-forces-an-exact-good-block
kind: claim
title: Direct-sum dilution of Clifford curvature forces one exactly phase-coherent block
distinct_from:
  finite-clifford-symplectic-section-obstruction: that is a global group-extension nonsplitting theorem; this is a normalized-Hilbert--Schmidt quantization statement for finitely many multiplication triangles in an arbitrary direct sum of Clifford blocks
  wall-energy-amplification: that amplifies a surviving wall by tensor powers; this says tensor padding cannot shrink a nonzero Pauli curvature and that direct sums only average the set of blocks on which it occurs
  minimal-marked-graph-finite-window-phase-space-section: that is the positive exact finite-window target; this proves that the proposed random/direct-sum dilution architecture cannot avoid that target
---

Let

```text
H = directSum_(i in I) H_i
```

be a finite direct sum of irreducible finite Clifford blocks.  For each of
`m` tested multiplication triangles `t`, suppose its blockwise Clifford
curvature has the normal form

```text
D_(t,i) = lambda_(t,i) P_(a_(t,i)),
```

where `lambda_(t,i)` is scalar and `P_(a)` is a Pauli/Weyl operator.  Call
block `i` bad for `t` when `a_(t,i) != 0`.

Then, with weights `w_i = dim(H_i)/dim(H)`,

```text
dist_2(D_t, {directSum_i mu_i 1_(H_i) : |mu_i|=1})^2
   = 2 sum_(i bad for t) w_i.                         (DSD1)
```

In particular, if for every tested triangle

```text
||D_t - 1||_2^2 < 2/m,                               (DSD2)
```

then some block is good for all `m` triangles at once.  Equivalently, on
that block every tested Clifford curvature is scalar.

## Proof

In an irreducible Clifford block every nonidentity Pauli has normalized trace
zero.  Hence for `a != 0` and every scalar `mu`,

```text
||lambda P_a - mu 1||_2^2
 = 1 + |mu|^2 - 2 Re(conjugate(mu) lambda tr(P_a))
 = 1 + |mu|^2.
```

The minimum over arbitrary scalar contractions is `1`, but multiplication
curvatures are unitaries and the harmless comparison phases have modulus one;
over `|mu|=1` the minimum is exactly `2`.  On a good block the curvature
itself is a unit scalar and its distance to the block-unit-scalar set is zero.
Orthogonality of the direct-sum blocks therefore gives `(DSD1)`; equivalently
one may use directly

```text
||lambda P_a - 1||_2^2 = 2
```

for every nonzero Pauli after optimizing the harmless block scalar phase.
Since distance to the block-unit-scalar set is at most `||D_t-1||_2`,
`(DSD2)` implies

```text
sum_(i bad for t) w_i < 1/m.
```

The union of the `m` bad sets has total weight strictly less than one.  Its
complement is nonempty, and any block in that complement is phase-coherent
for all tested triangles.  This proves the claim.

The statement is unchanged by tensor padding: a nonidentity Pauli tensored
with an identity still has trace zero and the same normalized squared
distance.  Only the direct-sum weights can change.

## Consequence for the marked-graph programme

The random/direct-sum experiment proposed in
`minimal-marked-graph-crossed-product-ce` cannot make Pauli-valued factor-set
defects tend to zero merely by spreading different bad triangles among many
completed blocks.  Once the defect is below the fixed `2/m` threshold, one
constituent block already solves every tested phase-space equation exactly.

Direct sums may still average scalar Weil multipliers, but those are not the
hard obstruction: conjugate doubling cancels them.  The surviving target is
therefore the exact local section
`minimal-marked-graph-finite-window-phase-space-section`, not a probabilistic
dilution of its Pauli curvature.
