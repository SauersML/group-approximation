---
rg: 2
id: deligne-lattices-and-torelli-quotients-contain-heisenberg-groups
kind: claim
title: Deligne's lattice over Sp_4(Z) and every Torelli lower-central quotient Mod(S_g)/T_g[c+1] (g >= 3, c >= 2) contain the integer Heisenberg group, so a no to H_3(Z) in nV excludes them from every Brin-Thompson host
distinct_from:
  heisenberg-group-embeds-in-no-brin-thompson-group: that is the open non-embedding of H_3(Z) into mV; this shows two non-residually-finite Kazhdan BH test cases contain H_3(Z), so that open claim would exclude them from all mV.
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that would exclude them because they are infinite Kazhdan groups; this gives an independent exclusion through a nilpotent subgroup.
requires:
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - torelli-lower-central-quotients-have-solvable-word-problem
artifacts:
  - research/artifacts/gq-bh-bh-free-38-torelli-quotients.md
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

1. **Torelli quotients.** Let `g >= 3`, `c >= 2`, and
   `N = T_g/T_g[c+1] ≤ Q_{g,c}`.
   - `N` is finitely generated nilpotent, so it has a torsion-free subgroup `N'`
     of finite index.
   - `N` is not virtually abelian. Its rational Malcev Lie algebra
     `t_g/t_g[c+1]` is non-abelian: Hain's central line `z_g ⊂ t_g[2]` survives
     modulo `t_g[3]` (Nowak Thm `thm:hainkernel`(iii), arXiv:2609.12196
     l.2282), so `[t,t] ≠ 0` there. Finite-index subgroups have the same Malcev
     algebra.
   - So `N'` is a torsion-free nilpotent group of some class `k ≥ 2`. Pick `y`
     in `γ_{k-1}(N')` and `x ∈ N'` with `z = [x,y] ≠ 1`. This is possible
     because `γ_k(N') = [N', γ_{k-1}(N')] ≠ 1`.
   - Then `z ∈ γ_k(N')` is central and has infinite order, so
     `⟨x,y⟩ ≅ H_3(Z)`. Every nontrivial normal subgroup of the torsion-free
     nilpotent group `H_3(Z)` meets its center `⟨[x,y]⟩`, so the natural map
     from `H_3(Z)` is injective.
2. **Deligne's lattice.** Let `Γ~` be the preimage of `Sp_4(Z)` in the universal
   cover `p: G~ → G = Sp_4(R)`.
   - The unipotent radical `U` of the Klingen parabolic of `Sp_4` is the
     3-dimensional Heisenberg group, and `U(Z) = U(R) ∩ Sp_4(Z) ⊇ H_3(Z)` as a
     lattice.
   - `U(R)` is simply connected, so `p^{-1}(U(R))` is a trivial covering. It
     contains a unique subgroup mapping isomorphically onto `U(R)`.
   - That subgroup meets `Γ~` in a copy of `U(Z)`. So `Γ~ ⊇ H_3(Z)`.

**Consequence.** If `heisenberg-group-embeds-in-no-brin-thompson-group` holds
(OPEN for `m >= 2`), then `Γ~` and every `Q_{g,c}` with `g >= 3`, `c >= 2` embed
in no `mV`, and in no finite-index subgroup of one either.
- This gives a second route to excluding them from Brin–Thompson hosts,
  independent of `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.
- For `m = 1` it is already true: `thompson-v-has-no-heisenberg-subgroup`.

**Inputs.**
- Hain's line, via Nowak's statement.
- Klingen parabolic structure: textbook.
- Covering of a simply connected group is trivial: textbook.
- Every nontrivial normal subgroup of a torsion-free nilpotent group meets the
  center: textbook.
