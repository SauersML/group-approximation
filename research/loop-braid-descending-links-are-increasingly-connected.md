---
rg: 2
id: loop-braid-descending-links-are-increasingly-connected
kind: claim
title: "The descending links L_n(LB_*) of the loop braid cloning system become arbitrarily highly connected"
artifacts:
  - research/artifacts/zp-loop-braid-descending-links-model-2026-09-13.md
---

For the cloning system on `LB_n = ΣAut_n` (Witzel–Zaremsky, arXiv:1405.5491v3,
Lemma 10.1), and for every m ≥ 0, there is N such that the simplicial complex
`L_n(LB_*)` is m-connected for all n ≥ N.

Definition (their §5.3, p. 31): a simplex of `L_n(G_*)` is a class `[g, Γ]`,
with `g ∈ G_n` and Γ a non-trivial matching of the linear graph `L_n`. Two
pairs `(g_1, Γ_1)`, `(g_2, Γ_2)` are equivalent if Γ_1 and Γ_2 have the same
number m of edges, `g_2^{-1} g_1 ∈ im κ_{Γ_1}`, and
`Γ_2 = (g_2^{-1} g_1)κ_{Γ_1}^{-1} · Γ_1`. Faces come from subgraphs. By their
Observation 5.8 this is the descending link in the Stein–Farley complex.

## Attempts

- 2026-09-13 (lane z2-12-loop-bv), m = 0: `L_n(LB_*)` is connected for `n ≥ 5`.
  This is the proof of WZ Lemma 5.10 together with generation of `LB_n` by
  cloning images (artifact of `loop-braid-cloning-system-is-properly-graded`,
  §4).
- m = 1: split off as
  `loop-braid-descending-links-are-eventually-simply-connected`. The plan there
  uses a strict fundamental domain `OM(K_n)` for the `PΣAut_n` action and a
  colimit presentation of `PΣAut_n` by cabling subgroups.
- Complete join over the combinatorial matching complex: DEAD.
  - Take `e: PΣAut_n → Z^{n(n−1)}`, the exponent sums of conjugators (a
    homomorphism).
  - `f = e_13 − e_23 − e_14 + e_24` vanishes on the cabling subgroups at
    `{1,2}` and `{3,4}`, but `f(α_13) = 1`.
  - So two fusion bands can clasp: vertices over an edge of the base need not
    span a simplex. Details are in artifact §3.
- Candidate routes for all m (artifact §5):
  - (R1) complexes of framed fusion bands in `B³ \ unlink`, with a Hatcher-flow
    and defect argument as in BFMWZ §3;
  - (R2) Hatcher–Wahl Theorem 3.6 labeled joins over tori or spheres.
    Warning: spheres around two loops are not preserved by cabling;
  - (R3) Abels–Holz higher generation by cabling subgroups;
  - (R4) comparison with Collins' marked cactus graphs.
