---
rg: 2
id: kazhdan-subgroups-of-fibred-subgroups-of-nv-are-finite
kind: claim
title: "Cantor current extensions C(X,Λ) ⋊ H contain an infinite Kazhdan subgroup iff H or Λ does; so the fibred subgroups C(C,V) ⋊ V of 2V and the triangular subgroups T_n of nV contain only finite Kazhdan subgroups"
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is the open finiteness of all Kazhdan subgroups of every nV; this proves it only inside the subgroups preserving a coordinate fibration, and shows that at the least n where it fails the witness preserves no coordinate fibration
  brin-thompson-nv-cnd-proper-on-triangular-subgroup: that asks for a cnd function on nV proper on T_n (Haagerup property of T_n and more); this proves only the weaker consequence that Kazhdan subgroups of T_n are finite, with no Hilbert-space action
  brin-thompson-triangular-subgroup-is-undistorted: that is about growth of the exponent cocycle on single infinite-order elements of T_n; this is about Kazhdan subgroups of the fibred subgroups and uses only Farley's theorem for V plus permanence of property (T)
  cantor-maps-by-v-embed-in-next-brin-thompson-group: that embeds C(C,Γ) ⋊ V in (n+1)V; this shows that this embedding never creates an infinite Kazhdan subgroup that Γ did not already contain
  finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite: that is a finiteness criterion by germs and orbits for arbitrary finitely generated subgroups; this is a structural reduction for Kazhdan subgroups of fibred subgroups, which needs no orbit information
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that concerns measure-preserving amenable orbit full groups via Connes--Weiss; the fibred subgroups here carry no invariant measure hypothesis
---

**ESTABLISHED** by `kazhdan-subgroups-of-fibred-subgroups-of-nv-are-finite-proof`.

## Statement

**Theorem 1 (current extensions).** Let `X` be a nonempty compact totally disconnected
space, `H ≤ Homeo(X)` any subgroup and `Λ` any group. Let `C(X,Λ)` be the group of
locally constant maps `X → Λ` under pointwise multiplication, with `H` acting by
`(h·f)(x) = f(h^{-1}x)`. Let `K ≤ C(X,Λ) ⋊ H` have property (T), and let
`ρ : C(X,Λ) ⋊ H → H` be the projection.
1. `ρ(K)` is a Kazhdan subgroup of `H`.
2. If `ρ(K)` is finite, then `K_0 = K ∩ C(X,Λ)` has finite index in `K`, and there is a
   finite clopen partition `X = X_1 ⊔ … ⊔ X_N` such that evaluation `f ↦ (f|_{X_i})_i`
   is an injective homomorphism `K_0 → Λ^N` whose coordinate images are Kazhdan
   subgroups of `Λ`.
3. Hence `C(X,Λ) ⋊ H` contains an infinite Kazhdan subgroup iff `H` or `Λ` does.

**Theorem 2 (fibred subgroups of nV).** Let `n ≥ 2`, `∅ ≠ J ⊊ {1,…,n}`, `m = |J|`, and
`pr_J : C^n → C^J` the coordinate projection (`C = {0,1}^ω`). Put

```text
Fib_J = { g ∈ nV : pr_J ∘ g = h ∘ pr_J for some homeomorphism h of C^J } .
```

1. `Fib_J` is a subgroup of `nV`, and `Fib_J ≅ C(C^J, (n−m)V) ⋊ mV` via
   `Φ(f,h)(x,y) = (h x, f(h x)(y))` for `x ∈ C^J`, `y ∈ C^{J^c}`.
2. `Fib_J` contains an infinite Kazhdan subgroup iff `mV` or `(n−m)V` does.

**Corollary 3 (unconditional cases).**
1. In `2V`, both fibred subgroups `Fib_{1}` and `Fib_{2}` (each `≅ C(C,V) ⋊ V`)
   contain only finite Kazhdan subgroups.
2. For every `n ≥ 1`, the triangular subgroup `T_n` of
   `brin-thompson-triangular-subgroup-is-undistorted` contains only finite Kazhdan
   subgroups. So does every subgroup of `Homeo(C^n)` isomorphic to a subgroup of `T_n`,
   including all `nV`-conjugates and coordinate permutations of `T_n`.
3. For every `Γ ≤ nV`, the group `C(C,Γ) ⋊ V ≤ (n+1)V` of
   `cantor-maps-by-v-embed-in-next-brin-thompson-group` contains an infinite Kazhdan
   subgroup iff `Γ` does.

**Corollary 4 (shape of a minimal witness).** Suppose some `nV` contains an infinite
Kazhdan subgroup, and let `n_0 ≥ 2` be the least such `n`. Then no infinite Kazhdan
`K ≤ n_0V` is isomorphic to a subgroup of any `Fib_J(n_0V)`. In particular no
subgroup of `n_0V` isomorphic to `K` (for instance an `n_0V`-conjugate or a coordinate
permutation of `K`) maps every fibre of any coordinate projection `pr_J` into a fibre.
For `n_0 = 2`, `K` is not isomorphic to a subgroup of `C(C,V) ⋊ V`.

## Class killed

These constructions of an infinite Kazhdan subgroup of `nV` all fail, and fail at the
same step: the base image in `mV` is finite, and the finite-index kernel sits in a
finite power of `(n−m)V`.
- Fibred constructions and their iterates: current groups over a base action,
  triangular towers, and products `mV × (n−m)V`.
- The inductive step `Γ ↦ C(C,Γ) ⋊ V`.

The invariant that kills them is a coordinate projection that the whole subgroup
preserves. A Kazhdan partner for Zaremsky 2.19 or 2.7 at the least dimension must
therefore use genuinely mixing elements, of baker's-map or Turing-machine type, that
move information between coordinates. Such elements are not fibred.

## Scope and credit

- The argument is elementary permanence of property (T) plus Farley's theorem for `V`.
  It is plausibly folklore. No source stating it was found, and the search was limited
  to this graph.
- Theorem 1 needs no hypothesis on `H` beyond acting by homeomorphisms. Theorem 2 uses
  only the prefix-replacement structure of `nV`.
- It proves nothing about Kazhdan subgroups that preserve no coordinate fibration.
  The open claim `kazhdan-subgroups-of-brin-thompson-groups-are-finite` is untouched
  for those.
