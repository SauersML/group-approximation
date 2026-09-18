---
rg: 2
id: farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts
kind: claim
title: If a Farrell–Jones group, torsion allowed, acts on a compact zero-dimensional space with every finite subgroup acting freely, the Leavitt tensor of the binary crossed product has vanishing K-theory in every degree
distinct_from:
  cantor-crossed-product-leavitt-tensors-are-k-trivial: that needs a torsion-free Farrell–Jones group and allows any action; this allows torsion, needs only that finite subgroups act freely, and removes the D_∞-type orbits by Davis–Quinn–Reich.
  free-action-leavitt-tensor-hosts-have-trivial-k1-k2: that is the open statement for every finitely generated group acting freely; this proves it, in every degree, for groups satisfying the Farrell–Jones conjecture with additive coefficients.
  fjc-crossed-products-of-k-trivial-regular-rings-vanish: that assembles torsion-free groups from the trivial subgroup and Z; this uses finite and finite-by-Z orbits, whose rings are matrix rings and skew Laurent rings over matrix rings.
---

**ESTABLISHED (derivation from established claims and literature imports;
unreviewed).** Route: `fj-groups-acting-freely-have-k-trivial-leavitt-hosts-proof`.

**Hypotheses.**
- `Λ` is a group satisfying the `K`-theoretic Farrell–Jones conjecture with
  additive categories as coefficients, with respect to `VCyc`. Torsion is
  allowed.
- `X` is a compact Hausdorff zero-dimensional space with a `Λ`-action such
  that every finite subgroup of `Λ` acts freely. Equivalently, no nontrivial
  element of finite order has a fixed point.

Let `B = LC(X, F_2) ⋊ Λ` and `L = L_(F_2)(1,2)`.

**Conclusion.** `K_n(B ⊗ L) = 0` for every `n ∈ Z`.

In particular, `free-action-leavitt-tensor-hosts-have-trivial-k1-k2` holds for
every finitely generated `Λ` in this class acting freely. This closes the
"Farrell-Jones with torsion" sketch recorded in its Attempts.

The fact that `K_1(LC(X, F_2)[Z/2] ⊗ L) ≠ 0` for the trivial action (see
`leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`) shows that the freeness
hypothesis on finite subgroups cannot be dropped, even for `Λ = Z/2`.
