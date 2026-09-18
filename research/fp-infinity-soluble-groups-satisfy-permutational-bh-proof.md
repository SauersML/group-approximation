---
rg: 2
id: fp-infinity-soluble-groups-satisfy-permutational-bh-proof
kind: route
title: Soluble FP_∞ groups are virtually torsion-free minimax, hence residually finite of finite rank, hence in B_A
target: fp-infinity-soluble-groups-satisfy-permutational-bh
requires:
  - rf-soluble-minimax-groups-satisfy-permutational-bh
  - elementary-amenable-fp-infinity-groups-virtually-soluble
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Lane `bh-solvable`, 2026-09-18.

1. **Soluble case.** Let `H` be soluble of type `FP_∞`. It is finitely generated, since
   `FP_1` is equivalent to finite generation.
   - By Martínez-Pérez--Nucinkis, Theorem 1.1 and p. 136 (read at source), `H` is virtually
     torsion-free and minimax.
   - A finitely generated soluble minimax group has finite Prüfer rank. A minimax group is
     residually finite if and only if its maximal periodic normal subgroup `τ` is finite
     (Pyber--Segal, arXiv:0711.0687, §3, citing Lennox--Robinson Ch. 5, which was not read here).
   - If `N` is a torsion-free normal subgroup of finite index, then `τ(H) ∩ N = 1`. So `τ(H)`
     embeds in `H/N` and is finite, and `H` is residually finite.
   - So `H ∈ B_A` by `rf-soluble-minimax-groups-satisfy-permutational-bh`.
2. **Virtually soluble case.** Let `G` be virtually soluble of type `FP_∞`, and let `H` be a
   soluble subgroup of finite index, which we may take normal.
   - `H` is of type `FP_∞`, by restricting a resolution to a finite-index subgroup.
   - By step 1, `H ∈ B_A`.
   - By part 2 of `boone-higman-type-a-class-closed-under-finite-extensions` (finite-index
     overgroups), `G ∈ B_A`.
3. **Elementary amenable case.** By `elementary-amenable-fp-infinity-groups-virtually-soluble`,
   an elementary amenable group of type `FP_∞` is virtually soluble. Apply step 2.
4. **Envelope.** Groups in `B_A` have solvable word problem and embed in finitely presented
   simple groups (part 3 of `boone-higman-type-a-class-closed-under-finite-extensions`). ∎
