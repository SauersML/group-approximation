---
rg: 2
id: computable-finite-cloning-group-not-cocf-not-in-v-proof
kind: route
title: "Coset-tree cloning over a recursive but super-polynomial lamp stabilizer: computable data, solvable word problem, polynomial-time obstruction to coCF and to V"
target: computable-finite-cloning-group-not-cocf-not-in-v
requires:
  - finite-cloning-groups-realize-every-lamplighter-over-thompson-f
---

Complete hand proof (unreviewed). Notation: `x_0, x_1` are the standard generators of
Thompson's group `F`, acting on `[0,1]`; `x_0` is `t/2` on `[0,1/2]`.

## 1. A recursive set that is not polynomial-time in unary

Fix an effective list `M_0, M_1, ...` of Turing machines and a computable bijection
`⟨e,c⟩ : N × N → N`. Every `i ≥ 1` is uniquely `2^{⟨e,c⟩}(2m+1)`. Put `i ∈ S` iff
`M_e` does **not** accept the unary input `1^i` within `i^c` steps.

- `S` is recursive: decode `(e,c)` from `i` and simulate `M_e` for `i^c` steps.
- No machine decides `S` in time polynomial in `i`. Suppose `M_e` decides `S` on unary
  inputs within `C i^d + C` steps. Pick `c` with `i^c ≥ C i^d + C` for all `i ≥ 2`
  (any `c ≥ d + 1 + log_2(2C)` works), and an `i ≥ 2` of index `(e,c)`. Then
  `M_e` halts on `1^i` within `i^c` steps. If it accepts, `i ∉ S` by definition, and if
  it rejects, `i ∈ S`. Either way it answers wrongly at `i`.

## 2. The subgroup H_S and its decidability

- Let `φ(t) = 5/16 + t/8`, a dyadic affine map of `[0,1]` onto `[5/16, 7/16]`. Let `y`
  be `φ x_0^{-1} φ^{-1}` on `[5/16,7/16]` and the identity elsewhere. Then `y ∈ F`,
  `supp y = [5/16, 7/16]`, and `y` has right slope `2` at `5/16` (because `x_0^{-1}` has
  slope `2` on `[0,1/4]`). For `n ∈ Z`, `y^n` has right slope `2^n` at `5/16`.
- `J_i := [2^{-i-2}, 2^{-i-1}] = x_0^i([1/4,1/2])`, with pairwise disjoint interiors, and
  `g_i := x_0^i y x_0^{-i}` is supported in `int J_i`.
- `H_S := ⟨g_i : i ∈ S⟩`. As in `finite-cloning-group-with-undecidable-lamp-stabilizer`
  (step 2), the `g_i` commute, every element of `H_S` is a finite product
  `∏_{i∈S} g_i^{n_i}`, and `g_i ∈ H_S ⇔ i ∈ S`.

**Membership in `H_S` is decidable.** Input: `f ∈ F` as a tree pair (so its finitely many
breakpoints and slopes are known exactly). Then `f ∈ H_S` iff all of the following hold:

1. the right slope of `f` at `0` is `1`, so `f` is the identity on `[0, ε]`, where `ε` is
   the first breakpoint; and `f` is the identity on `[1/2, 1]`;
2. `f(2^{-k}) = 2^{-k}` for every `k ≥ 1` (only the finitely many `k` with `2^{-k} ≥ ε`
   need checking, by 1);
3. for each of the finitely many `i` with `J_i ⊄ [0,ε]`, the map
   `h_i := x_0^{-i} (f|_{J_i}) x_0^i` (extended by the identity; on `J_i` conjugation by
   `x_0^i` is the scaling `t ↦ 2^i t`) equals `y^{n_i}`, where `2^{n_i}` is the right slope
   of `h_i` at `5/16` (reject if that slope is not an integer power of 2, or if `h_i`
   moves a point outside `[5/16,7/16]`), and `n_i = 0` unless `i ∈ S`.

Necessity is clear from the normal form. Sufficiency: by 1 and 2, `f` restricts to each
`J_i` and is the identity on all but finitely many of them and on `[1/2,1]`, so
`f = ∏_i x_0^i h_i x_0^{-i} = ∏_i g_i^{n_i}` with `n_i = 0` for `i ∉ S`. Each test is a
finite computation in `F` (compose tree pairs, compare), plus finitely many queries to
the recursive set `S`.

## 3. The cloning system is computable

Take the coset-tree cloning system of `finite-cloning-groups-realize-every-lamplighter-over-thompson-f`
for `H = H_S` and `A = Z/2`: `D_n = ⊔_{j ≤ n} Trees_j/~`, with `W ~ W'` iff
`[W,W'] ∈ H_S`, `G_n = (Z/2)^{D_n}`, `ι` extension by zero, and `κ^n_k` pushforward
along `[W]_j ↦ [W c_k]_{j+1}` (`k ≤ j`), `[W]_j ↦ [W]_j` (`k > j`). The finite sets
`Trees_j` can be listed, `~` is decidable by section 2, so class representatives of
`D_n` and the maps `s_k`, hence `ι` and `κ^n_k`, are computable. By that claim it is a
properly graded pure cloning system on finite groups, `T(G_*)` is finitely generated, and
`t = [•, 1, •]` satisfies `[t, f] = 1 ⇔ f ∈ H_S` for `f ∈ F`, with
`Γ := ⟨x_0, x_1, t⟩ = Z/2 ≀_{F/H_S} F`.

## 4. Γ has solvable word problem

`Γ = (Z/2)^{(F/H_S)} ⋊ F`, where `t` is the lamp at the coset `H_S` and `f t f^{-1}` is
the lamp at `f H_S`. Given a word `w` in `x_0^{±1}, x_1^{±1}, t`, read it left to right.
Keep the current prefix value `f ∈ F` as a tree pair, and every time a letter `t` is read
record the element `f_r := f`. Then `w` represents
`(∑_r δ_{f_r H_S}) · f_{end}`, so `w = 1` iff `f_end = 1` and every coset occurs an even
number of times among `f_1 H_S, ..., f_m H_S`. Coset equality `f_r H_S = f_s H_S` is
`f_r^{-1} f_s ∈ H_S`, decidable by section 2. So the word problem is solvable.

## 5. Γ is not coCF, and neither Γ nor T(G_*) embeds in V

- Let `ŷ` be a fixed word in `x_0^{±1}, x_1^{±1}` representing `y`, and
  `w_i := t · x_0^i ŷ x_0^{-i} · t · x_0^i ŷ^{-1} x_0^{-i}`. It represents
  `t g_i t^{-1} g_i^{-1} = [t, g_i]` (recall `t = t^{-1}`), has length `4i + 2|ŷ| + 2`,
  and can be written down in time `O(i)`. By section 3, `w_i = 1` in `Γ` iff `g_i ∈ H_S`
  iff `i ∈ S`.
- Suppose `Γ` is coCF. The co-word problem over the monoid generators
  `x_0^{±1}, x_1^{±1}, t` is then context-free (it does not depend on the finite
  generating set, Holt–Rees–Röver–Thomas 2005). Fix a Chomsky normal form grammar for
  it. The Cocke–Younger–Kasami algorithm decides membership of a word of length `ℓ` in
  time `O(ℓ^3)` on a random-access machine, hence in polynomial time on a Turing machine.
  So `i ↦ [w_i ≠ 1]` is decidable in time polynomial in `i`, and by complementing, so is
  `S`. This contradicts section 1.
- `T(G_*)` is finitely generated and contains `Γ`. Being coCF passes to finitely
  generated subgroups (HRRT 2005), so `T(G_*)` is not coCF.
- Every finitely generated subgroup of `V` is coCF, since `V` is coCF
  (Lehnert–Schweitzer, arXiv:math/0507090) and coCF passes to finitely generated
  subgroups. So neither `Γ` nor `T(G_*)` embeds in `V`.

This establishes `computable-finite-cloning-group-not-cocf-not-in-v`.

## 6. Scope

- The argument uses only that the word problem of a coCF group, and of a finitely
  generated subgroup of `V`, is decidable in polynomial time. The same diagonalisation
  against a clock `T(i)` in place of `i^c` gives, for every computable bound `T`, a
  computable coset-tree cloning system on finite groups with a finitely generated
  subgroup whose word problem is decidable but not within time `T` (up to the linear
  length of `w_i` and the cost of the reduction).
- It says nothing about Lehnert's conjecture, since the witness is not coCF.
- What a positive answer would need: a restriction of the class of cloning systems under
  which the lamp stabilizers (or, more generally, the point stabilizers of the cloning
  maps' index sets) are context-free-recognisable. The coset-tree systems show that the
  axioms (C1)–(C3), proper grading and finiteness of each `G_n` impose no such bound.
