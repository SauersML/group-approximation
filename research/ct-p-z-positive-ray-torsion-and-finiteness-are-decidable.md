---
rg: 2
id: ct-p-z-positive-ray-torsion-and-finiteness-are-decidable
kind: claim
title: "In CT(Z), the torsion problem and the finiteness problem for finitely generated subgroups are decidable for inputs whose slopes lie in γ^Z with γ an integer, with an explicitly computable bound on orders; so any undecidable torsion family in CT(Z) must have mixed-sign or rank-two slopes"
distinct_from:
  ct-z-torsion-problem-and-the-brin-thompson-transplant: that records that the torsion problem of CT(Z) is open and why the Belk–Bleak coding does not transplant; this decides it on the positive-ray class, where orders are computably bounded, in contrast with 2V.
  ct-p-z-order-is-decided-by-elliptic-reduction: that characterizes finite order (bounded degree sums, elliptic reduction) for single elements; this turns the positive-ray case into an algorithm with an explicit bound, for single elements and for finitely generated subgroups.
---

**ESTABLISHED** (lane proof, not reviewed). It is a corollary of bh-kourovka's ray-cocycle
pumping theorem (`periodic-k-graph-subgroups-with-ray-cocycle-are-finite`), whose constants are
explicit. No priority is claimed.
- **What is decided.** The torsion problem of CT(Z) on the positive-ray class.
- **What stays open.** The torsion problem in general
  (`ct-z-torsion-problem-and-the-brin-thompson-transplant`), and in particular gap (G1) of the
  21.74(a) route (`ct-z-residue-partition-certificates-live-on-s-adic-coordinates`).

## Statement

- **Input.** A finite set `S` of elements of `CT_P(Z)`, for a finite set `P` of odd primes, given
  by rcwa tables (or as words in class transpositions).
- **Hypothesis.** Every slope of every piece lies in `γ^Z` for one integer `γ ≥ 2`. Equivalently,
  the degree cocycle lies in `Zv` with `v ∈ N^k ∖ {0}`. This covers `V = CT_∅(Z)`, and slopes in
  `2^Z` or `6^Z` in `CT_{{3}}(Z)`.
- **The bound.** The input theorem fixes a **symmetric** generating set, so the constants are taken
  over the tables of `S ∪ S^(−1)` (referee repair, bh-ref-d, e64cfcbeeb). Put:
  - `D` = the depth, so that every piece of every element of `S ∪ S^(−1)` has degree `≤ D·1`;
  - `K = max |κ|` over the pieces of `S ∪ S^(−1)`, where the piece has slope `γ^κ`;
  - `E = (D + K‖v‖_∞)·1`, `C = m_E`, `B = K·C`, and `n = D + 2B‖v‖_∞`;
  - `N(S) = (2B + 1)·m_(n·1 + Bv)`, where `m_d = ∏ p^(d_p)`.
- **Conclusions.**
  1. **Orders are computably bounded.** If `g ∈ ⟨S⟩` has finite order, its order divides
     `e(S) = lcm(1, …, N(S))`. If `⟨S⟩` is finite, `|⟨S⟩| ≤ N(S)!`.
  2. **Torsion is decidable.** `g` has finite order iff `g^(e({g}))` is the identity. Here the
     constants in `e({g})` are computed from the tables of both `g` and `g^(−1)`.
  3. **Finiteness is decidable.** Enumerate balls of `⟨S⟩` using the word problem. If a ball stops
     growing, the group is finite. If some ball exceeds `N(S)!` elements, it is infinite.
     Exactly one of the two happens.

## Proof

- **The input theorem.** `periodic-k-graph-subgroups-with-ray-cocycle-are-finite` applies to the
  one-vertex `k`-graph of `CT_P(Z)` (`ct-p-z-is-a-one-vertex-k-graph-full-group`): it is
  aperiodic, with `p ≥ 2` edges of colour `p`, and `|Λ^d| = m_d`.
  - For a finitely generated periodic `H = ⟨S⟩` with ray cocycle, its steps give the bound
    `|κ(h, x)| ≤ B` on `H` (pumping, with `C = |Λ^E| = m_E`).
  - They then give an embedding `H ↪ Sym(F_n)`, where `F_n` is a set of cylinders of degrees
    `n·1 + κv` with `|κ| ≤ B`. So `|F_n| ≤ N(S)`.
  - The constants depend only on the tables of `S`, and the ray hypothesis holds for `⟨S⟩` as soon
    as it holds for `S`. All of this is in the input node.
- **1.**
  - If `g` has finite order, then `⟨g⟩` is finitely generated and periodic, so it embeds in
    `Sym(N)` with `N ≤ N({g})`. Its order divides the exponent `lcm(1, …, N)` of that group.
  - If `⟨S⟩` is finite, it is periodic and embeds in `Sym(F_n)`.
- **2.** Compute `g^(e)` by repeated squaring of rcwa tables, which is exact integer arithmetic,
  and compare with the identity table. Then use 1.
- **3.** The word problem of `CT(Z)` is decidable, by comparing reduced rcwa tables. If `⟨S⟩` is
  infinite, its balls grow without bound. If it is finite, they stabilize at `|⟨S⟩| ≤ N(S)!`. ∎

## Contrast and consequences

- **Brin–Thompson.** In `2V` the largest order of a torsion element with at most `n` rectangles is
  not computably bounded (Belk–Bleak, arXiv:1405.0982, Thm 4.5, recorded in
  `ct-z-torsion-problem-and-the-brin-thompson-transplant`). On the positive ray in `CT_P(Z)` it
  is computably bounded, by `N(S)`.
- **Where undecidable torsion can live.** Any family in `CT(Z)` with undecidable torsion problem,
  such as the one gap (G1) of the 21.74(a) route asks for, must have slopes of rank two or on a
  mixed-sign ray.
- **The mixed-sign ray.** There, finiteness is equivalent to a bounded cocycle, and to a frozen tail
  at every point (`ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits`). But no computable
  bound is known.
  - This is the moving-head regime.
  - Barbieri–Kari–Salo (arXiv:2303.17270) prove the torsion problem undecidable for elementary
    Turing machines.
- **Kourovka 19.46.** bh-kourovka's positive-ray answer is effective: the finite group is
  explicit.

## Credits

- bh-kourovka, for the theorem and all the constants: the pumping, the contraction lemma and the
  finite permutation model.
- Belk–Bleak, for the contrast.
- The lane that wrote `ct-z-torsion-problem-and-the-brin-thompson-transplant`, for posing the open
  problem in this form.

## Lesson for general BH

**Decision problems in arithmetic hosts follow the same cone line as orbits and torsion.**
- **Positive drift.** Returns nest, pumping finds them at a computable resolution, and torsion is
  decidable with computable order bounds.
- **Mixed drift or rank two.** Returns only intersect, or carries read every depth. Only there can
  undecidable torsion, and Belk–Bleak-type unbounded orders, live.

**For hosts with a hard word problem (gate 1, HARD-(A)).** A host whose hardness must come from
torsion or return dynamics cannot get it from positive-drift pieces. It needs a moving-head
(mixed-sign) or two-base mechanism.
