---
rg: 2
id: f2-leavitt-path-unit-groups-fp-simple-steinberg
kind: claim
title: Unit groups of F_2 Leavitt path algebras with trivial unit class and nonzero det(1 - N^t) are finitely presented and simple
distinct_from:
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that transfers Khanh's theorem to B tensor L_2 for simple B; this transfers it to Leavitt path algebras of other finite graphs, whose K_0 need not vanish and whose words end at several vertices.
  central-simple-leavitt-tensor-unit-groups-are-simple: that proves simplicity for B tensor L_2 with B central simple; this targets simplicity for graph algebras L_(F_2)(E) through the same abstract root-detection theorem.
  leavitt-square-unit-group-is-fp-simple-and-acyclic: that is the single host (L_2 tensor L_2)^x; this is a family of hosts parametrised by finite graphs, containing rings not isomorphic to L_2 such as the K_0 = Z/2 example.
  leavitt-unit-group-finitely-presented: that is finite presentability of the one group L_2^x, imported from Khanh; this targets finite presentability for unit groups of other graph algebras, with nonzero K_0 allowed.
  binary-leavitt-unit-group-is-simple: that is simplicity of L_2^x; this targets simplicity of L_(F_2)(E)^x for graphs E with trivial unit class, which needs the centre of a general graph algebra.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**OPEN.** Let `E` be a finite graph with no sinks and no sources, cofinal, with
condition (L). Put `L = L_(F_2)(E)` and `D = det(1 - N_E^t)`, and assume
`[1_L] = 0` in `K_0(L)` and `D != 0`. Then:
- `GL_m(L) = E_m(L)` for `m >= 2`, and `H_1 = H_2 = 0` for every `GL_r(L)`;
- `St_r(L) ≅ GL_r(L)` for `r >= 3`;
- `L^x` is finitely presented, simple, infinite and nonabelian;
- if `D = ±2^k`, every `GL_r(L)` is integrally acyclic.

**Example.** The two-vertex graph with `N = [[2,3],[1,2]]` has `K_0 = Z/2`,
`[1] = 0` and `D = -2` (`leavitt-path-k-theory-over-finite-fields-via-det`). So it
gives a candidate integrally acyclic finitely presented simple group whose host
ring is not isomorphic to `L_2`.

**Boone--Higman value, stated honestly.** Once cancellation holds, `[1] = 0`
yields a unital copy of `L_2`, so `L_2^x <= L^x`. No Boone--Higman class beyond
those of `L_2^x` and `(L_2 ⊗ L_2)^x` follows from these hosts yet. What they add
is a family of new host candidates and the SFT full groups `[[G_E]]` as monomial
units. Word problems in `L_(F_2)(E)^x` are uniformly elementary, so the family is
not universal either, by `complexity-bounded-host-classes-are-not-universal`.

## Attempts

- **Proved inputs:**
  - (P3), vanishing of `K_1`, `K_2` and of all higher K-groups:
    `leavitt-path-k-theory-over-finite-fields-via-det`.
  - (P2), the multiplier half of simultaneous division:
    `leavitt-path-algebras-have-simultaneous-strong-division`.
  - (P4): a finite graph gives a finite presentation of `L` over `F_2`.
- **Missing inputs:**
  - (P1) and the complement half of (P2):
    `purely-infinite-leavitt-path-v-monoid-cancellation`.
  - The central-unit hypothesis for simplicity:
    `simple-leavitt-path-algebra-center-is-coefficient-field`.
- **Assembly.** With both, the paper transfer of
  `research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md` Sections
  2--4 is expected to run line by line, with Theorem B replacing its Lemma 2.2:
  - Prop 3.1 needs only `e, f` and `H_n(GL_∞) = 0`;
  - Cor 2.5 needs only frame extension;
  - Lemma 5.3 needs strong division and `K_1 = 0`;
  - Krstić--McCool needs a finite ring presentation.
  That transfer has not been reviewed.
- **Not pursued.** Hosts with `[1] != 0` (for instance one vertex with `n >= 3`
  loops). Khanh's Theorem 2.2 needs `A^2 ≅ A`, and homological stability for them
  would need a different frame complex.
