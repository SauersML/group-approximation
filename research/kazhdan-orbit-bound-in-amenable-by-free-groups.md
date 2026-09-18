---
rg: 2
id: kazhdan-orbit-bound-in-amenable-by-free-groups
kind: claim
title: "A finite transitive set of a Kazhdan group that injects into A × F_d (A amenable) with bounded left displacement has size bounded by the Kazhdan pair, the displacement set and A alone"
distinct_from:
  haagerup-hosts-carry-no-weak-expander: that forbids weakly embedded expanders in finitely generated subgroups of a group whose Haagerup property is imported; this is an import-free separator proof for the specific targets A × F_d with A amenable (not necessarily finitely generated), with an explicit bound, used on orbits of topological full groups rather than on subgroups.
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that proves almost every orbit is finite; this bounds the size of each finite orbit uniformly, which is what turns almost-everywhere finiteness into finiteness of the group.
---

**ESTABLISHED** by `kazhdan-orbit-bound-in-amenable-by-free-groups-proof` (self-contained,
no imports).

## Setting

- `K` is a discrete group with property (T): there are a finite `Q ⊂ K` and `ε > 0` such
  that every unitary representation with a unit vector `ξ`, `max_{s∈Q} ||sξ − ξ|| < ε`, has
  a nonzero invariant vector. `(Q, ε)` is a *Kazhdan pair*. By Step 0 of the route, `K` is
  finitely generated and has a Kazhdan pair `(S, ε)` with `S` finite, symmetric and
  generating.
- `P = A × F_d`, with `A` a countable amenable group (Følner form: for every finite
  `E_A ⊂ A` and `δ > 0` there is a finite nonempty `F ⊂ A` with `|aF Δ F| ≤ δ|F|` for all
  `a ∈ E_A`) and `F_d` free of rank `d ≥ 0`.
- `E ⊂ P` is finite. Write `E_A` for its projection to `A` and `R` for the largest reduced
  length of the `F_d`-coordinate of an element of `E`.

## Statement

There is `M = M(S, ε, E, A, d) < ∞` such that the following holds. Let `Z` be a finite
transitive `K`-set and `ι : Z → P` an injective map with

```text
ι(s z) ∈ E · ι(z)        for all s ∈ S, z ∈ Z          (left displacement in E).
```

Then `|Z| ≤ M`. Explicitly one may take

```text
M = C · (128|S|/(3ε²) + 8/3),    C = |F| · |B_T(R)|,
```

where `F ⊂ A` is any `(E_A, ε²/(128|S|))`-Følner set and `|B_T(R)|` is the number of
vertices in a ball of radius `R` of the `2d`-regular tree.

## Remarks

- For `d = 0` this is the folklore fact that Kazhdan Schreier graphs do not inject
  Lipschitz into amenable groups at unbounded size. The tree factor is the point: `A × F_d`
  is not amenable, and the proof combines Følner slabs in the `A` direction with a tree
  centroid in the `F_d` direction.
- If a finitely generated group `P'` is Haagerup, the same conclusion for `P'` follows
  from §2 of `haagerup-hosts-carry-no-weak-expander-proof` (fibres of size one). That
  variant needs the Haagerup property of `P'` as an import and is not asserted here.
- The finiteness of `Z` is essential. An infinite transitive `K`-set has no invariant
  vector in `ℓ²(Z)`, so its Schreier graph is non-amenable, but non-amenable graphs such
  as `T × Z^2` do inject into `F_d × Z^2`. Whether an *infinite* Kazhdan Schreier graph can
  inject with bounded left displacement into `Z^2 × F_d` is the residual question recorded
  in `dense-finite-free-orbits-force-finite-kazhdan-subgroups`.

DERIVATION
kazhdan-orbit-bound-in-amenable-by-free-groups-proof
