---
rg: 2
id: haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core
kind: claim
title: "If finitely many automorphic images of a subgroup H meet in a finite group, then a group has the Haagerup property iff some cnd function is proper modulo H"
distinct_from:
  haagerup-splits-as-coset-plus-subgroup-properness: that splits the Haagerup property into properness modulo H plus properness on H, for any H; this shows that the second half is redundant as soon as finitely many images of H under automorphisms meet in a finite group
  braid-haagerup-iff-proper-on-noncentral-normal-subgroup: that removes a half of a split for braid groups through a normal subgroup; this removes the fibre half for a non-normal subgroup through automorphic images
---

**ESTABLISHED** by `haagerup-proper-mod-finite-automorphic-core-proof`.

**Definitions.** As in `haagerup-splits-as-coset-plus-subgroup-properness`: `G` is a countable
group, a cnd function is `ψ = ‖b‖²` for a 1-cocycle `b` of an orthogonal representation (so
`ψ ≥ 0`, `ψ(e) = 0`), and `φ` is *proper modulo `H`* if every sublevel set `{φ ≤ R}` lies in a
finite union of left cosets of `H`.

**Statement.**

1. If `ψ` is cnd and proper modulo `H`, and `α ∈ Aut(G)`, then `ψ ∘ α` is cnd and proper modulo
   `α^{-1}(H)`.
2. If `ψ_1, ψ_2` are cnd, `ψ_1` proper modulo `H_1` and `ψ_2` proper modulo `H_2`, then
   `ψ_1 + ψ_2` is cnd and proper modulo `H_1 ∩ H_2`.
3. Let `H ≤ G` and let `α_1, ..., α_r ∈ Aut(G)` be such that `α_1(H) ∩ ... ∩ α_r(H)` is finite.
   Then `G` has the Haagerup property if and only if some cnd function on `G` is proper modulo
   `H`. More precisely, if `ψ` is proper modulo `H`, then `Σ_i ψ ∘ α_i^{-1}` is a proper cnd
   function.

**Use.** For a simple group no normal subgroup is available, and
`haagerup-splits-as-coset-plus-subgroup-properness` leaves two independent-looking halves. Item 3
says the fibre half comes for free whenever `H` has a finite automorphic core. It applies to
`nV` with `H = T_n` (`brin-thompson-nv-haagerup-iff-proper-modulo-triangular`).
