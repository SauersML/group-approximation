---
rg: 2
id: cantor-maps-by-v-embed-in-next-brin-thompson-group
kind: claim
title: "For every subgroup Γ of nV, the group C(C,Γ) ⋊ V embeds in (n+1)V"
distinct_from:
  brin-thompson-nv-embeds-in-mv: that embeds nV in mV by g ↦ g x id; this embeds the much larger group C(C,Γ) ⋊ V of Γ-valued locally constant maps, fibred over the first coordinate, in (n+1)V
  twisted-power-cloning-groups-embed-in-v: that embeds V-type cloning groups over a finite group in V (its case φ0 = φ1 = id is C(C,G) ⋊ V for finite G); this handles every subgroup Γ of a Brin-Thompson group, finite or not, at the cost of one extra dimension
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Let `C = {0,1}^N` and `n ≥ 1`, and let `Γ ≤ nV` be any subgroup. Let
`C(C,Γ) ⋊ V` be the group of locally constant maps `C → Γ`, under pointwise
multiplication, extended by Thompson's group `V` acting by precomposition
`(h·f)(x) = f(h^{-1}x)`. Then `C(C,Γ) ⋊ V` is isomorphic to a subgroup of the
Brin–Thompson group `(n+1)V`, via
`Φ(f,h)(x,p) = (hx, f(hx)(p))` for `(x,p) ∈ C × C^n`.

Consequences:

- `C(C,Z) ⋊ V ≤ 2V`.
- `C(C,V) ⋊ V ≤ 2V`.
- If some `nV` with `n ≥ 2` is a-T-menable, Brothier's Problem B
  (arXiv:1906.03789v3: is `C(C,Γ) ⋊ V` a-T-menable whenever `Γ` is?) has a
  positive answer for every `Γ ≤ (n-1)V`, in particular for `Γ = Z`
  (using `brin-thompson-nv-embeds-in-mv` and heredity of the Haagerup property).

Novelty: not established. The construction is elementary and plausibly folklore;
no source stating it was found, but the search was limited (see the lane note).
