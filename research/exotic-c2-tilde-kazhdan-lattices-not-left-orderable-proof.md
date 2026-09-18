---
rg: 2
id: exotic-c2-tilde-kazhdan-lattices-not-left-orderable-proof
kind: route
title: Normal forms in two irreducible BMW groups, positive-cone SAT on their type-preserving kernels, and Titz Mite–Witzel's locally convex embeddings exclude left orders on the exotic C~_2 lattices
target: exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable
requires: []
artifacts:
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.out
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/radu_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/radu_sat.out
---

All scripts are in `experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/`. Reproduce with
`python3 bmw_sat.py radu 4 6`, `python3 bmw_sat.py jw 2 4`, and the same with `prod_radu`,
`prod_jw` (seconds each; needs `python-sat`). Output is in `bmw_sat.out`.

References: TMW = T. Titz Mite, S. Witzel, *Non-residually finite C~_2-lattices*,
arXiv:2509.05054 (labels below are the paper's LaTeX labels).

## 1. The two BMW groups

A BMW group of degree `(d_1, d_2)` is a group acting regularly on the vertices of `T_1 × T_2`
(TMW §2). By Brown's theorem (TMW Proposition `brown`) the Radu and Janzen–Wise groups have the
presentations

- `Γ_R = ⟨a,b,c,x,y,z | a^2, b^2, c^2, x^2, y^2, z^2, axax, ayay, azbz, bxbx, bycy, cxcz⟩`
  (TMW Proposition `gamma33_pres`, degree (3,3));
- `Γ_JW = ⟨a,b,x,y | axay, ax^{-1}by^{-1}, ay^{-1}b^{-1}x^{-1}, bxb^{-1}y^{-1}⟩`
  (TMW Proposition `JanzenWise`, degree (4,4)).

Both are irreducible (same propositions, part 2). Call `a,b,c` (resp. `a^{±1}, b^{±1}`)
horizontal and `x,y,z` (resp. `x^{±1}, y^{±1}`) vertical. Every relator has the shape
`h_1 v_1 h_2 v_2`.

## 2. Complete rewriting system

Each relator `h_1 v_1 h_2 v_2` gives four equations `h v = v' h'`:
`h_1 v_1 = v_2^{-1} h_2^{-1}`, `h_2 v_2 = v_1^{-1} h_1^{-1}`, `h_2^{-1} v_1^{-1} = v_2 h_1`,
`h_1^{-1} v_2^{-1} = v_1 h_2`. `build()` collects them and asserts that they define a
*bijection* from the `|H|·|V|` pairs `(h, v)` to the pairs `(v', h')` (consistent where equations
coincide, and all pairs covered). This is the vertex-link condition: the link is the complete
bipartite graph.

Rewriting system: `c c^{-1} → ε` for every letter, and `h v → v' h'`.

- *Termination.* No rule lengthens a word, and `hv → v'h'` lowers the number of (horizontal,
  vertical) letter pairs in that order by exactly one while cancellation does not raise it.
- *Local confluence.* Left sides have length 2, so there are no inclusion overlaps. The overlaps
  are `h h^{-1} v`, `h v v^{-1}` and `c c^{-1} c`. `confluence()` reduces both sides of each and
  asserts they agree: 24 critical pairs for Radu, 40 for Janzen–Wise (18+6 and 32+8).
- By Newman's lemma the system is complete. Every rule is a consequence of the relators, and
  `confluence()` checks that every relator rewrites to `ε`. So the rule congruence equals the
  group congruence, and each element has exactly one irreducible word: a freely reduced
  vertical word followed by a freely reduced horizontal word.

`make()` implements multiplication on normal forms by pushing vertical letters leftwards through
the horizontal part. `selftest()` checks associativity and inverses on 2000 random triples and
that every relator evaluates to the identity. These checks are sanity checks; soundness rests on
the completeness argument, since `mul` computes the irreducible form of the concatenated word.

## 3. The type-preserving kernel is `π_1(S)`

TMW §2: bicolour each tree. The type-preserving subgroup `Γ^+` acts regularly on each of the
four vertex types, `Γ/Γ^+` is the Klein group `D_2 = ⟨σ_A, σ_X⟩`, and `S = Γ^+ \ (T_1 × T_2)`
is the four-vertex square complex; `Γ^+ = π_1(S)`. Examples `SquareRadu` and
`SquareJanzenWise` define the generators by `a: [γ] ↦ [a^{-1} * σ_A(γ)]` and so on, so a
horizontal letter swaps the `T_1`-colour and a vertical letter the `T_2`-colour. Hence
`π_1(S) = {normal forms (v, h) with |v|, |h| both even}`, which is the kernel `K` used by
`run()`. It is torsion-free, being the fundamental group of a compact non-positively curved
square complex.

## 4. Positive-cone certificate

**Lemma.** Let `G` be a group, `B` a finite subset containing 1 and `K ≤ G`. If `K` is
left-orderable then the CNF on variables `p_g` (`g ∈ K ∩ B`, `g ≠ 1`) with clauses

- `(p_g ∨ p_{g^{-1}})` and `(¬p_g ∨ ¬p_{g^{-1}})` whenever `g, g^{-1} ∈ B`,
- `(¬p_g ∨ ¬p_h ∨ p_{gh})` whenever `g, h, gh ∈ K ∩ B`, `gh ≠ 1`,
- `(¬p_g ∨ ¬p_h)` whenever `gh = 1`,

is satisfiable.

*Proof.* Put `p_g = [g > 1]`. Exactly one of `g, g^{-1}` is positive for `g ≠ 1`, and the positive
cone is a subsemigroup not containing 1. ∎

`run(name, L)` takes `B = B_L` (word ball in the generators, elements as normal forms), asserts
that no element of `K ∩ B` is its own inverse, and emits exactly these clauses (the second
family is emitted for all ordered pairs, which covers the `gh = 1` case). Results, CaDiCaL 1.5.3
and Glucose 4 agreeing (`assert res[0]==res[1]`):

| group | L | `|B_L|` | `|K ∩ B_L| − 1` | clauses | result |
|---|---|---|---|---|---|
| `Γ_R` | 4 | 244 | 96 | 1920 | SAT |
| `Γ_R` | 6 | 1540 | 576 | 38784 | **UNSAT** |
| `Γ_JW` | 2 | 49 | 24 | 96 | SAT |
| `Γ_JW` | 4 | 865 | 384 | 15000 | **UNSAT** |
| `prod_radu` | 6 | 1540 | 576 | 38784 | SAT |
| `prod_jw` | 4 | 865 | 384 | 15000 | SAT |

So `π_1(S_R)` and `π_1(S_JW)` are not left-orderable. The UNSAT answers were rerun on
2026-09-17 by the relaunched worker (`bmw_sat.py jw 4`, 2 s).

**Calibration.** `prod_*` keeps the letters and the involution/inverse structure but lets every
square commute. The groups are `(C_2 * C_2 * C_2)^2` and `F_2 × F_2`; the kernels `K` are
`F_2 × F_2` and a finite-index subgroup of `F_2 × F_2`, left-orderable. The script answers SAT
with the same ball sizes and clause counts, so the UNSAT answers are not artefacts of the
encoding. `radu_sat.py` is an independent earlier implementation for Radu: it reproduces UNSAT
on `B_6`, gives UNSAT on `B_8` (3072 elements, 669 696 clauses), UNSAT for the second
index-4 kernel `K2`, and SAT for the product calibration on `B_4, B_6, B_8` (`radu_sat.out`).

## 5. Embedding into the exotic lattices

- TMW Theorem `main_2`, Part 1: subdividing `S_R` along the diagonals from `v_00` to `v_11`
  gives a `C~_2` chamber complex that embeds in `Y^2_1` via the explicit assignment
  `v_00 ↦ v, v_11 ↦ w, a ↦ f_4, …, s_i ↦ g_i`, and "`π_1(S_R)` embeds into `Γ^2_1` by Lemma
  `locally_convex`".
- TMW §7 (thickness 4): each `Y^3_k`, `k = 1..4`, contains a subdivision of `S_JW` as a
  subcomplex, and `π_1(S_JW) ↪ Γ^3_k` by Lemma `locally_convex` and Theorem
  `building_cartan-hadamard`.
- Lemma `locally_convex` is Bridson–Haefliger II.4.14 (locally convex subspaces of complete
  non-positively curved spaces are `π_1`-injective).

A subgroup of a left-orderable group is left-orderable, so `Γ^2_1` and all `Γ^3_k` are not
left-orderable, and neither is any group containing one of them (`Γ̄^q_k`, `Aut(X^2_1)`).

## 6. Context facts used only in the statement

TMW Main theorem: the `Γ^q_k` are uniform lattices on exotic `C~_2` buildings, hence CAT(0) with
property (T), and not residually finite. For `q = 2`, `Γ^2_1` is its own finite residual; TMW
Corollary (via Lécureux–Witzel Theorem A) makes the finite residuals simple. For `q = 3`,
`[Γ^3_k : Γ̌^3_k] = 4` (`k = 1,2`) or `8` (`k = 3,4`). The non-orderability proof uses none of
these facts.

## Approach record

- *Why it can succeed where dead approaches failed.* No unipotent Heisenberg configuration,
  linearity or boundary theory: these groups are not residually finite, so not linear. The
  certificate uses only the local square combinatorics of an embedded tree-product lattice.
- *Falsifiable first step.* SAT on `π_1(S_R) ∩ B_6`; checked in minutes.
- *Calibration.* The commuting-square products stay satisfiable at the same radii.
