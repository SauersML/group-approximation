---
rg: 2
id: acyclic-host-twisted-rope-container-is-of-type-fp3
kind: claim
title: "Some acyclic-host twisted rope container of a universal finitely presented group is of type FP_3"
refuted_by: acyclic-host-twisted-rope-container-is-never-fp3
distinct_from:
  twisted-rope-trick-container-is-not-fp3-over-fp2-hosts: that proves the twisted container fails over hosts with finite rational H_2 and whenever the two embeddings agree on H_2; this is the case it leaves open, a host with infinite rational H_2 on which the embeddings differ injectively
  universal-fp-group-embeds-in-an-rp-fp3-group: that only asks for some recursively presented FP_3 host of a universal group; this names one explicit finitely presented candidate host
artifacts:
  - research/artifacts/zp-z1-01-ffz-fp3-level-three-2026-09-13-part2.md
---

**REFUTED 2026-09-13 (unreviewed).**
- Refuted by `acyclic-host-twisted-rope-container-is-never-fp3` (lane z1-01-ffz-fpinf, a9735c0298), an
  instance of `split-edge-hnn-with-non-fp2-edge-is-not-fp3`: for every choice below, `K_ac(G)` is not
  `FP_3(Q)`.
- Lane z1-01-ffz-fp3 reached the same conclusion independently, by the degree-one computation recorded
  under Attempts.
- The two elementary directions of the product test used there are proved from scratch in
  `product-coefficient-fp-tests-elementary-directions`.

**Construction.**
- Let `G = F/R` be a finitely presented, integrally acyclic group containing a universal finitely
  presented group. It exists by Baumslag–Dyer–Miller, Topology 22 (1983), who embed every recursively
  presented group in a finitely presented acyclic group.
- Let `L = F_1 *_R F_2` be the double and `π: L → G` the map killing `F_2`.
- Let `ι_0: L → P_0` embed `L` in a finitely presented acyclic group (BDM again).
- Let `K_ac(G)` be the HNN extension of `A = P_0 × L × G` along `L` conjugating
  `f_1(y) = (ι_0(y), 1, 1)` to `f_2(y) = (1, y, π(y))`. This is the twisted rope-trick container of
  `twisted-rope-trick-embeds-g-in-a-finitely-presented-group` over the host `P = P_0 × L`.

**Claim (false).** For some such choice of `G`, `P_0` and `ι_0`, `K_ac(G)` is of type `FP_3`.

**Facts that remain true (derivations in the artifact; unreviewed).**
1. `K_ac(G)` is finitely presented, although its vertex group is not.
2. `K_ac(G)` contains `G`.
3. `K_ac(G)` is an integral homology circle.

So it passes every trivial-coefficient test and fails only on product coefficients.

## Attempts

- **Degree-one injectivity: fails.** Put `W = Π_I ZK`, `N = P_0 × 1 × G` and `Γ = f_2(L)`, so
  `A = N ⋊ Γ`.
  - `FP_3` needs `H_2(K; W) = 0`, hence `H_1(f_2; W): H_1(L; W) → H_1(A; W)` must be injective. The
    `f_1` term vanishes because `P_0` is `FP_2`.
  - `N` is finitely presented, so `H_1(N; W) = 0`. The five-term sequence of `N ⊴ A` then makes
    `H_1(A; W) → H_1(Γ; W_N)` injective.
  - The coinvariants `W_N = Π_I Z[N\K]` are free over `Γ`: `N a k = N k` forces `a ∈ N`, so every
    `N`-coset has trivial stabilizer and there are no permutation summands.
  - The collapse `ZK → Z[N\K]` restricted to each coset `Ak` is the sum map `⊕_{n ∈ N} ZΓ → ZΓ`. It is
    split, and its kernel is free.
  - So the kernel of `H_1(f_2; W)` contains `H_1(L; Π_I ZL)`, which is nonzero for a suitable `I`
    because the double `L` is finitely generated and not `FP_2`. Hence `K_ac(G)` is not `FP_3`.
- **Degree-two surjectivity:** moot after the above.
- **Lesson for a higher rope trick.** Do not send the edge group as a graph over a direct factor of the
  vertex group with finitely presented complement. The product defect of the double then survives into
  `H_2`. The general form is `split-edge-hnn-with-non-fp2-edge-is-not-fp3`.
