---
rg: 2
id: lanner-tree-noncrossing-intervals-are-not-lattices
kind: claim
title: "The noncrossing partition interval [1,c]_W is not a lattice for the compact hyperbolic Coxeter groups [5,3,3,3], [4,3,3,5], [5,3,3,5], [4,3,5] and [5,3,5], so the dual Garside lattice step fails for every compact hyperbolic 4-simplex tree group"
distinct_from:
  noncrossing-interval-of-5-3-3-11-is-not-a-lattice: that proves the same failure for [5,3,3^{1,1}], [3,5,3] and [5,3^{1,1}]; this covers the other five compact hyperbolic tree groups, three of them rank-5 targets of the K(π,1) node, with new certificates that need roots of larger height and label 4.
  compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1: that is the open K(π,1) conjecture for the four rank-5 Lannér trees; this rules out one proof method (the lattice property of the dual interval) for all four of them and proves no case of the conjecture.
  artin-groups-of-rank-at-most-four-satisfy-k-pi-1: that proves K(π,1) for rank at most 4; here the rank-4 groups [4,3,5] and [5,3,5] only answer the lattice question for the noncrossing interval.
artifacts:
  - experiments/artin-dual-lattice-2026-09-17/bowties_label4.py
  - experiments/artin-dual-lattice-2026-09-17/verify_bowtie_label4.py
  - experiments/artin-dual-lattice-2026-09-17/cert-5333.json
  - experiments/artin-dual-lattice-2026-09-17/cert-5334.json
  - experiments/artin-dual-lattice-2026-09-17/cert-5335.json
  - experiments/artin-dual-lattice-2026-09-17/cert-435.json
  - experiments/artin-dual-lattice-2026-09-17/cert-535.json
  - experiments/artin-dual-lattice-2026-09-17/results-lanner.txt
---

Proof: [[lanner-tree-noncrossing-intervals-are-not-lattices-proof]].

**Setting.**
- `(W, S)` is a Coxeter system acting on `V = R^n` by the geometric representation, with
  `B(α_i, α_j) = −cos(π/m_ij)`.
- `T` is the set of reflections and `ℓ_T` is reflection length. `u ≤_T w` means
  `ℓ_T(u) + ℓ_T(u^{-1}w) = ℓ_T(w)`.
- For a Coxeter element `c`, `[1,c]_W = {w : w ≤_T c}` is the noncrossing partition interval.
- `[1,c]_W` is a lattice for spherical `W` (Bessis; Brady–Watt) and in rank 3 (Delucchi–Paolini–Salvetti,
  arXiv:2206.14518). It fails for most affine `W` (McCammond). Which `W` give a lattice is open (Paolini,
  arXiv:2112.05255).

**Theorem.** Let `W` be one of the paths below and `c` any Coxeter element of `W`. Then `[1,c]_W` is not a lattice.

| Group | Diagram (path) | Rank |
|---|---|---|
| `[5,3,3,3]` | `s_1 −5− s_2 −3− s_3 −3− s_4 −3− s_5` | 5 |
| `[4,3,3,5]` | `s_1 −5− s_2 −3− s_3 −3− s_4 −4− s_5` | 5 |
| `[5,3,3,5]` | `s_1 −5− s_2 −3− s_3 −3− s_4 −5− s_5` | 5 |
| `[4,3,5]` | `s_1 −4− s_2 −3− s_3 −5− s_4` | 4 |
| `[5,3,5]` | `s_1 −5− s_2 −3− s_3 −5− s_4` | 4 |

**How the failure shows up.** There are distinct reflections `a`, `b` and distinct rank-3 elements `p`, `q` of
`[1,c]_W` with `a, b ≤_T p` and `a, b ≤_T q`, and no rank-2 element of `[1,c]_W` lies above both `a` and `b`. So `a`
and `b` have no join.
- The rank-3 elements come from 3-letter subwords of explicit length-`n` reflection factorizations of `c = s_1 ⋯ s_n`.
- The criterion excluding a rank-2 element above `a` and `b` is `det(E^T B (1−c)^{-1} E) ≤ 0` for `E = [α_a, α_b]`.
  By Lemma D of the proof, every rank-2 element `z` of `[1,c]_W` has this determinant positive on `Mov(z)`.
- The determinants are `−φ/4` for `[5,3,3,3]`, `[4,3,3,5]`, `[4,3,5]` and `−φ/2` for `[5,3,3,5]`, `[5,3,5]`, with
  `φ = (1+√5)/2`.
- For example, for `[5,3,3,3]`: `α_a = (1+φ)α_1 + 2φα_2 + φα_3 + φα_4 + φα_5`,
  `α_b = (1+φ)α_1 + 2φα_2 + 2φα_3 + φα_4`, and `p = s_{α_5} s_{α_a} s_{α_3} = s_{α_3} s_{α_b} s_{α_5}`.

**Consequence for K(π,1).**
- Together with [[noncrossing-interval-of-5-3-3-11-is-not-a-lattice]], the lattice property of `[1,c]_W` fails for all
  four rank-5 compact hyperbolic tree groups `[5,3,3,3]`, `[4,3,3,5]`, `[5,3,3,5]`, `[5,3,3^{1,1}]`. These are exactly the
  groups of [[compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1]]. It also fails for all four rank-4 compact
  hyperbolic tree groups.
- The dual approach proves K(π,1) from a Garside structure on the interval group of `[1,c]_W`: Bessis and Brady–Watt
  for spherical groups, and Paolini–Salvetti for affine groups through McCammond–Sulway's enlargement. The step
  "`[1,c]_W` is a lattice" is false for every target group and every Coxeter element.
- A dual proof for these groups therefore needs a lattice enlargement of `[1,c]_W`. None is known for hyperbolic `W`.

**Verification tier.** Complete hand proof of the criterion (Lemma D and the Proposition), with exact certificates
checked in `Q(√2, √5)` by a sympy verifier that shares no code with the search. Unrefereed.

**Not covered.**
- The cyclic compact hyperbolic diagrams, where Coxeter elements need not be conjugate.
- Lattice enlargements in the style of McCammond–Sulway.
- No case of the K(π,1) conjecture is proved or refuted.

## Attempts

- 2026-09-17 (sw-042, reframing lane, unreviewed). Exact rank-(1,3) bowtie search over 3-letter subwords of the
  height-bounded Hurwitz orbit of `s_1 ⋯ s_n`, with roots in `Z[√2, φ]` (`bowties_label4.py`); the log is
  `results-lanner.txt`.

  | Group | Height bound | Factorizations of `c` | Candidate pairs | Pairs with `det ≤ 0` | Verified |
  |---|---|---|---|---|---|
  | `[5,3,3,3]` | 9 / 13 | 4015 / 8829 | – / 826 | 0 / 12 | – / `cert-5333.json` |
  | `[4,3,3,5]` | 10 / 12 | 6642 / 9388 | 686 / 976 | 0 / 1 | – / `cert-5334.json` |
  | `[5,3,3,5]` | 11 / 13 | 9100 / 14296 | 1063 / 1633 | 0 / 5 | – / `cert-5335.json` |
  | `[4,3,5]` | 8 / 11 | 396 / 584 | – / – | 0 / 1 | – / `cert-435.json` |
  | `[5,3,5]` | 13 | 841 | 513 | 2 | `cert-535.json` |

  - Spherical controls `B_4`, `F_4`, `B_5` give 0 candidates. A dumped `F_4` pair is rejected by the verifier
    (det `1/4`, exit 1).
  - Earlier null results at smaller heights (recorded in [[noncrossing-interval-of-5-3-3-11-is-not-a-lattice]]) were
    only a matter of the height bound: the certificates use roots of height 11–13.
