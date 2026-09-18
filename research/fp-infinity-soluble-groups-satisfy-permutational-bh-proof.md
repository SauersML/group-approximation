---
rg: 2
id: fp-infinity-soluble-groups-satisfy-permutational-bh-proof
kind: route
title: Kropholler's Theorem B gives finite rank and virtual torsion-freeness modulo T, and residually finite soluble groups of finite rank are in B_A
target: fp-infinity-soluble-groups-satisfy-permutational-bh
requires:
  - rf-soluble-minimax-groups-satisfy-permutational-bh
  - elementary-amenable-fp-infinity-groups-virtually-soluble
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Lane `bh-solvable`, 2026-09-18.

0. **Reductions.** Type `FP_∞` over `Z` implies type `FP_∞` over `Q`: tensor a resolution by
   finitely generated projective `ZG`-modules with `Q`. It also implies that `G` is finitely
   generated (`FP_1`). Let `T` be as in Kropholler's Theorem B.
1. **Constructible groups have finite Prüfer rank and are torsion-free.** Let `B` be soluble
   of Prüfer rank `r`, and let `G = B*_φ` be an ascending HNN extension. Then
   `G = B_∞ ⋊ ⟨t⟩` with `B_∞ = ∪_n t^-n B t^n`. Every finitely generated subgroup of `B_∞`
   lies in some `t^-n B t^n ≅ B`, so it needs at most `r` generators. Hence `G` has rank at
   most `r + 1`. By Britton's lemma, an ascending HNN extension of a torsion-free group is
   torsion-free. By induction from the trivial group, every constructible soluble group is
   torsion-free of finite rank. So every constructible-by-finite group is virtually
   torsion-free of finite rank.
2. **Residual finiteness.** A finitely generated soluble group of finite rank is minimax. A
   minimax group is residually finite if and only if its maximal periodic normal subgroup
   `τ` is finite.
   - This is the equivalence recalled in Pyber--Segal, arXiv:0711.0687, §3, which cites
     Lennox--Robinson, *The theory of infinite soluble groups*, Ch. 5. That book was not
     read here; the equivalence is used as quoted there.
   - For a virtually torsion-free group `Q` with torsion-free normal subgroup `N` of finite
     index, `τ(Q) ∩ N = 1`. So `τ(Q)` embeds in `Q/N` and is finite.
3. **(a).** `G/T` is finitely generated, virtually soluble and constructible-by-finite. By
   step 1 it has finite rank, and by step 2 it is residually finite. By
   `rf-soluble-minimax-groups-satisfy-permutational-bh`, `G/T` lies in `B_A`.
4. **(b).** Let `T` be finite.
   - `G` has finite rank: `rk(G) <= rk(G/T) + |T|`.
   - `τ(G)` is finite, since `τ(G)T/T ⊆ τ(G/T)`, which is finite by step 2.
   - By step 2, `G` is residually finite, and it is finitely generated and soluble.
   - So `G ∈ B_A` by the same node.

   The three special cases:
   - if `G` is torsion-free, the locally finite `T` is trivial;
   - if `G` is metanilpotent, Kropholler's Theorem C makes `G` itself constructible-by-finite;
   - if `G` is constructible-by-finite, apply step 3 with `T = 1`.
5. **(c).** Type `FP_∞` passes to finite-index subgroups, by restricting a resolution. So
   the soluble subgroup `H` of finite index given by
   `elementary-amenable-fp-infinity-groups-virtually-soluble` satisfies the hypotheses of (b)
   whenever `T_H` is finite. That holds if `G` is virtually torsion-free, since then `H` is too.
   Then `H ∈ B_A`, and `G ∈ B_A` by part 2 of
   `boone-higman-type-a-class-closed-under-finite-extensions` (finite-index overgroups).
6. **Envelope.** Groups in `B_A` embed in finitely presented simple groups (part 3 of
   `boone-higman-type-a-class-closed-under-finite-extensions`). ∎
