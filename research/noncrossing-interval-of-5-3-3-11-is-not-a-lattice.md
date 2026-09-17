---
rg: 2
id: noncrossing-interval-of-5-3-3-11-is-not-a-lattice
kind: claim
title: "The noncrossing partition interval [1,c]_W is not a lattice for the compact hyperbolic Coxeter groups [5,3,3^{1,1}], [3,5,3] and [5,3^{1,1}], so the dual Garside route to K(π,1) fails at its lattice step for [5,3,3^{1,1}]"
distinct_from:
  compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1: that is the open K(π,1) conjecture for the four rank-5 Lannér trees; this rules out one proof method (the lattice property of the dual interval) for one of them and proves no case of the conjecture.
  artin-complexes-of-5333-and-533-11-are-contractible: that is contractibility of the Artin complex (parabolic cosets); this is a statement about the reflection-length interval [1,c]_W of the Coxeter group, which feeds the separate dual Garside approach.
  noncrossing-partition-diagonal-links-are-cat1: that is the classical type-A noncrossing partition complex; this is the hyperbolic noncrossing interval, and it proves failure of the lattice property.
artifacts:
  - experiments/artin-dual-lattice-2026-09-17/rank3_bowties.py
  - experiments/artin-dual-lattice-2026-09-17/lattice_bowties.py
  - experiments/artin-dual-lattice-2026-09-17/verify_bowtie.py
  - experiments/artin-dual-lattice-2026-09-17/cert-53311.json
  - experiments/artin-dual-lattice-2026-09-17/cert-353.json
  - experiments/artin-dual-lattice-2026-09-17/cert-5311.json
  - experiments/artin-dual-lattice-2026-09-17/results.txt
  - experiments/artin-dual-lattice-2026-09-17/rank24_bowties.py
  - experiments/artin-dual-lattice-2026-09-17/verify_bowtie24.py
  - experiments/artin-dual-lattice-2026-09-17/mixed_bowties.py
  - experiments/artin-dual-lattice-2026-09-17/cert24-53311.json
  - experiments/artin-dual-lattice-2026-09-17/results-rank5.txt
---

Proof: [[noncrossing-interval-of-5-3-3-11-is-not-a-lattice-proof]].

**Setting.**
- `(W, S)` is a Coxeter system with `S = {s_1, …, s_n}`, acting on `V = R^n` by the geometric
  representation, with `B(α_i, α_j) = −cos(π/m_ij)`.
- `T` is the set of reflections, `ℓ_T` is reflection length, and `u ≤_T w` means
  `ℓ_T(u) + ℓ_T(u^{-1}w) = ℓ_T(w)`.
- For a Coxeter element `c`, `[1,c]_W = {w ∈ W : w ≤_T c}` is the noncrossing partition interval.
- For the lattice question: `[1,c]_W` is a lattice for spherical `W` (Bessis; Brady–Watt) and for
  rank 3 (Delucchi–Paolini–Salvetti, arXiv:2206.14518). It fails for most affine `W` (McCammond).
  The survey arXiv:2112.05255 (Paolini) lists as open for which `W` it is a lattice.

**Theorem.** Let `W` be one of the three trees below, and `c` any Coxeter element. Then `[1,c]_W` is
not a lattice.

| Group | Diagram |
|---|---|
| `[5,3,3^{1,1}]` | `s_1 −5− s_2 −3− s_3`, plus `s_4`, `s_5` joined to `s_3` by label 3 |
| `[3,5,3]` | the path `s_1 −3− s_2 −5− s_3 −3− s_4` |
| `[5,3^{1,1}]` | `s_1 −5− s_2`, plus `s_3`, `s_4` joined to `s_2` by label 3 |

**How the failure shows up.** There are distinct reflections `a`, `b` and distinct rank-3 elements
`p`, `q` of `[1,c]_W` with `a, b ≤_T p` and `a, b ≤_T q`, such that no rank-2 element of `[1,c]_W`
lies above both `a` and `b`. So `a` and `b` have no join.

**Certificate for `[5,3,3^{1,1}]`**, with `c = s_1 s_2 s_3 s_4 s_5` and `φ = (1+√5)/2`:
- The reflections are `a = s_{α_a}` and `b = s_{α_b}`, with
  - `α_a = α_1 + φα_2 + φα_3 + φα_5`,
  - `α_b = α_1 + φα_2 + φα_3 + φα_4`.
- `p = s_{α_5} s_{α_a} s_{α_4} = s_{α_4} s_{α_b} s_{α_5}`.
- `q = s_{α_2+α_3+α_5} s_{α_a} s_{α_2+α_3+α_4} = s_{α_2+α_3+α_4} s_{α_b} s_{α_2+α_3+α_5}`.
- Each of these four words is a 3-letter subword of a reflection factorization of `c` of length 5.
  The factorizations are listed in the proof.
- The criterion that excludes a rank-2 element above `a` and `b` is
  `det(E^T B (1−c)^{-1} E) = −φ/4 ≤ 0`, where `E = [α_a, α_b]`. By Lemma D of the proof, every rank-2
  element `z` of `[1,c]_W` has this determinant positive on `Mov(z)`.

**Consequence for K(π,1).** The dual approach (Brady, Brady–Watt and Bessis for spherical groups;
Paolini–Salvetti for affine groups, through McCammond–Sulway's Garside enlargement) proves the conjecture for `A_W` from a Garside
structure on the interval group of `[1,c]_W`.
- For `[5,3,3^{1,1}]` the step "`[1,c]_W` is a lattice" is false.
- A dual proof for this group therefore needs a lattice enlargement of `[1,c]_W`, as McCammond–Sulway built for
  affine groups. No such enlargement is known for hyperbolic `W`.
- `[3,5,3]` and `[5,3^{1,1}]` have rank 4. There K(π,1) is already known through
  `artin-groups-of-rank-at-most-four-satisfy-k-pi-1`, so for them the theorem only answers the lattice question.

**Not covered.**
- `[5,3,3,3]`, `[5,3,3,5]`, `[4,3,3,5]`, `[4,3,5]` and `[5,3,5]` are not covered here. At the height bounds used here the
  exact search found no certificate for them (see `results.txt` and `results-rank5.txt`). With larger height bounds and a
  label-4 search, certificates do exist. The follow-up claim
  [[lanner-tree-noncrossing-intervals-are-not-lattices]] proves `[1,c]_W` is not a lattice for
  all five.
- No case of the K(π,1) conjecture is proved or refuted here.

## Attempts

- 2026-09-17 (sw-042, reframing lane, unreviewed). Exact search for rank-(1,3) bowties over
  3-letter subwords of the bounded Hurwitz orbit of `s_1 ⋯ s_n`, with the determinant criterion.
  The sympy verifier shares no code with the search.

  | Group | Height bound | Candidate pairs | Certified |
  |---|---|---|---|
  | `[3,5,3]` | 8 | 282 | 13 |
  | `[5,3^{1,1}]` | 8 | 292 | 17 |
  | `[5,3,3^{1,1}]` | 7 | 343 | 9 |
  | `[5,3,3,3]` | 7 / 9 | 227 / 413 | 0 / 0 |
  | `[5,3,3,5]` | 7 / 9 | 387 / 713 | 0 / 0 |
  | `[5,3,5]` | 10 | 376 | 0 |

  - Every spherical group tried (`H_4` with 101 pairs, `A_5` with 90, `D_5` with 133) gave 0 certificates, as
    it must. A dumped `H_4` candidate is rejected by the verifier (det `1/4`, exit 1).
  - On every run the determinant sign and the reflection test excluded exactly the same pairs.
  - In the three recorded certificates, `χ_c` restricted to `span(α_a, α_b)` is the symmetric form `B/2` of
    Lorentzian signature.
- 2026-09-17 (sw-042, unreviewed). Two further rank-5 shapes, with the same lemma D criterion (`results-rank5.txt`).
  - **Rank-(2,4) bowties** (`rank24_bowties.py`, verifier `verify_bowtie24.py`). The shape is rank-2 `x ≠ y`
    below coatoms `u ≠ v`, with `det χ_c|(Mov x + Mov y) ≤ 0`, so no rank-3 element lies above `x, y`.
    - `[5,3,3^{1,1}]` at height 6: 10 certificates. `cert24-53311.json` is verified, with det `−φ/8`.
    - `[5,3,3,3]` at heights 6, 7, 8 (up to 2146 pairs) and `[5,3,3,5]` at heights 6, 7, 8 (up to 4110 pairs): 0
      certificates. Every pair has det `> 0`.
    - `A_5`: 0 certificates. A dumped candidate is rejected (det `1/8`, exit 1).
  - **Mixed non-joins** (`mixed_bowties.py`). The shape is `det χ_c|U2 ≤ 0`, with `a, b ≤ p` of rank 3 and
    `a, b ≤ u` a coatom, and `Mov(p) ⊄ Mov(u)`. Then `a ∨ b` would have to be `p`, and it is not below `u`.
    - `[5,3,3,3]` up to height 9: 0. Every examined pair has det `> 0`.
    - `[5,3,3,5]` at height 9: 33 pairs have det `≤ 0`, so they have no rank-2 upper bound. Each lies below
      exactly one rank-3 element `p` found, and every coatom found above it contains `Mov(p)`. This is the pattern of
      a lattice with rank-3 joins, and it certifies nothing either way.
