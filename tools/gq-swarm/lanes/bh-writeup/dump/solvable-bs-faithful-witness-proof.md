---
rg: 2
id: solvable-bs-faithful-witness-proof
kind: route
title: The HNN extension of BS(1,m) along a^p -> a^q, s -> s has trivial tree kernel because q/p is not a unit of Z[1/m]
target: solvable-bs-groups-have-faithful-generalized-bs-witnesses
requires:
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
---

Write `G = Z[1/m] ⋊ <s>`, where `s^-1` acts on `Z[1/m]` as multiplication by `m`.

1. **Index and isomorphism.** `C = pZ[1/m] ⋊ <s>` and `C' = qZ[1/m] ⋊ <s>`. Since `p, q` are
   coprime to `m`, `Z[1/m]/pZ[1/m] ≅ Z/p`, so `[G : C] = p` and `[G : C'] = q`. Both are
   isomorphic to `G` via `a^p ↦ a` and `a^q ↦ a`. So `ψ(x s^j) = (q/p) x s^j` is an
   isomorphism `C -> C'` with `ψ(a^p) = a^q` and `ψ(s) = s`.
2. **Kernel.** The kernel of the action of `W` on its Bass--Serre tree is the largest normal
   subgroup `K` of `W` inside `G`. It satisfies `K ⊴ G`, `K ⊆ C`, and `ψ(K) = K`. Suppose
   `K ≠ 1`.
   - If `K ⊄ Z[1/m]`, pick `g = x s^j ∈ K` with `j ≠ 0`. Then `[g, a]` is a nontrivial element
     of `K ∩ Z[1/m]`, since `s^j` acts on `a` by multiplication by `m^(±j) ≠ 1`.
   - So in all cases `L := K ∩ Z[1/m] ≠ 0`. `L` is normal in `G`, so it is a
     `Z[1/m]`-submodule of `Z[1/m]`, that is `L = ℓ Z[1/m]` with `ℓ ∈ Z_{>0}` coprime to `m`.
   - `ψ(K) = K` gives `ψ(L) = L`, that is `(q/p) ℓ Z[1/m] = ℓ Z[1/m]`, so `q/p` would be a unit
     of `Z[1/m]`. It is not, because `p` and `q` are distinct primes coprime to `m`.
     Contradiction.
   So `K = 1` and the action is faithful.
3. **Class.** `W` is a one-vertex, one-edge graph of groups whose vertex group `G` and edge
   group `C ≅ G` are commensurable with `G`, and both edge inclusions have finite index. So
   `W ∈ BS_G`, and `W` is nontrivial. `G` is of type `F_∞`: the one-relator presentation
   complex is aspherical, since the relator is not a proper power.
4. **Conclude.** BLIW Theorem 11.1 needs `G` finitely presented. The TeX version, label
   `thm:main-BS`, needs `G` of type `F_n` with `n >= 2`, and gives a simple group of type `F_n`.
   It applies, so every group in `BS_G` embeds in a simple group of type `F_∞`. Item 4 of the
   target is `faithful-generalized-bs-witnesses-pass-to-direct-products` together with this
   witness. ∎
