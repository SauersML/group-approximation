---
rg: 2
id: bmw-klein-free-quaternionic-parity-kernels-proof
kind: route
title: Proof via a quaternionic representation over F_2(t), a tree-path faithfulness argument, the PGL_2 inversion lemma, and cone-propagation trees
target: bmw-klein-free-quaternionic-parity-kernels
requires: []
artifacts:
  - experiments/bmw-klein-free-2026-09-18/verify_quat_rep.py
  - experiments/bmw-klein-free-2026-09-18/verify_quat_rep.log
  - experiments/bmw-klein-free-2026-09-18/verify_cone.py
  - experiments/bmw-klein-free-2026-09-18/verify_cone.log
  - experiments/bmw-klein-free-2026-09-18/tree_31_30_26.json
  - experiments/bmw-klein-free-2026-09-18/tree_31_31_12.json
---

# Proof

Throughout, `c` is class `31_30` #26 or `31_31` #12 of
`experiments/bmw-census-left-orders-2026-09-17/census_31_30.json` or `census_31_31.json`.

## 0. The groups

- There are three h-letters `A = {h_0,h_1,h_2}` with inversion `iA = (1,0,2)`: `h_1 = h_0^{-1}`, and
  `h_2` is an involution.
- There are three v-letters `B = {v_0,v_1,v_2}`, with inversion `iB = (0,1,2)` (all involutions) for #26
  and `iB = (1,0,2)` for #12.
- There are nine squares `h v = v' h'`, one for each pair `(h, v)` (`reps[c]` in the census file).
- `Γ` is presented by the generators `A ∪ B`, the relations `x · iA(x) = 1` and `y · iB(y) = 1`, and the
  nine squares.
- **Normal form.** Every `γ ∈ Γ` can be written `γ = V H`, with `V` a reduced v-word and `H` a reduced
  h-word. To get it, move h-letters to the right through the squares, then cancel `x iA(x)` and
  `y iB(y)`. Only existence is used in §3.
- **Parity.** Every relation preserves the parity of the number of h-letters and of v-letters. So
  `ε : Γ → (Z/2)²` is well defined, and `Γ^+ = ker ε`.

## 1. The algebra

Let `K = F_2(t)`, `a = t`, `b = t² + t + 1`, and let `D` have basis `1, i, j, k = ij` with
`i² = i + a`, `j² = b`, `j i = (i + 1) j`. The multiplication table is:

| `·` | `i` | `j` | `k` |
|---|---|---|---|
| `i` | `a + i` | `k` | `a j + k` |
| `j` | `j + k` | `b` | `b + b i` |
| `k` | `a j` | `b i` | `a b` |

For example `k k = i j i j = i (j + k) j = i (b + b i) = a b`.

- `verify_quat_rep.py` checks associativity on all 64 basis triples. So `D` is the quaternion algebra
  `[a, b)` of characteristic 2.
- **Trace, conjugate and norm.** For `x = c_0 + c_1 i + c_2 j + c_3 k`, `Trd x = c_1` and
  `x̄ = (c_0 + c_1) + c_1 i + c_2 j + c_3 k`. Then `x x̄ = x̄ x = Nrd x ∈ K`, with
  `Nrd x = N(c_0 + c_1 i) + b N(c_2 + c_3 i)` and `N(u + w i) = u² + u w + a w²`.
- So `x` is invertible iff `Nrd x ≠ 0`, and then `x^{-1} = x̄ / Nrd x`.
- In `D^*/K^*`, `x² ∈ K^*` iff `x² = Trd(x) x − Nrd(x)` is scalar, i.e. iff `Trd x = 0` (for `x ∉ K`).

**Ramification.**
- *At `P = b`.* The residue field is `F_4`, and `x² + x + t` has no root modulo `b` (checked; `t` maps
  to a primitive cube root `ω`, and `Tr_{F_4/F_2}(ω) = 1`). So `K_P(i)` is the unramified quadratic
  extension. Its norms have even valuation, while `b` is a uniformizer. So `b ∉ N(K_P(i)^*)`, and
  `D_P` is a division algebra. Hence `D` is a division algebra.
- *At a finite place `Q ≠ P`.* `a` is integral and `b` is a unit. `K_Q(i)/K_Q` is split or
  unramified, so every unit is a norm, and `D_Q` splits.
- *At `∞`.* The ramification set of a quaternion algebra over a global field has even size, so `D` is
  ramified exactly at `b` and `∞`.

This paragraph is not used in §3–§5.

**The order.** Let `O = F_2[t]⟨1, i, j, k⟩`. The table shows that `O` is a ring.
- `det(Trd(e_r e_s))_{r,s} = b²` (checked).
- If `O ⊂ O'` are orders, then `det(O) = [O' : O]² det(O')`. So `O_Q = O ⊗ F_2[t]_{(Q)}` is a maximal
  order at every `Q ∤ b`, in particular at `t` and at `t + 1`.
- At `Q ∈ {t, t+1}`, `D_Q ≅ M_2(K_Q)`, and we may take `O_Q = M_2(O_Q)`, since maximal orders are
  conjugate. `Nrd` becomes `det`.

**The trees.** Let `Δ_Q` be the Bruhat–Tits tree of `PGL_2(K_Q)`, whose vertices are the homothety
classes of `O_Q`-lattices in `K_Q²`. The residue field is `F_2`, so `Δ_Q` is 3-regular.
- Let `o_Q = [O_Q²]`, and let `D_Q^*/K_Q^*` act by `x [Λ] = [x Λ]`.
- If `x ∈ M_2(O_Q) ∖ π M_2(O_Q)`, the elementary divisors of `x` are `1, π^n` with `n = val_Q(det x)`.
  So `d(o_Q, x o_Q) = val_Q(Nrd x)`.
- In general, `d(o_Q, x o_Q) = val_Q(Nrd x) − 2 min_r val_Q(c_r)`. This is the function `dist` of the
  scripts.
- `PGL_2(K_Q)` acts faithfully on `Δ_Q`.

## 2. The representation

Write the coordinates as `(c_0, c_1, c_2, c_3)`.

| letter | #26 | #12 |
|---|---|---|
| `h_0` | `t + i + j` | `t + i + j` |
| `h_1` | `(t+1) + i + j` | `(t+1) + i + j` |
| `h_2` | `t + j` | `t + j` |
| `v_0` | `k` | `1 + i` |
| `v_1` | `(t²+t+1) + (t+1) j` | `i` |
| `v_2` | `j + k` | `(t+1) + j` |

`verify_quat_rep.py` checks, exactly in `F_2[t]`, that each of the following equals a nonzero scalar
times the other side:
- `ρ(x) ρ(iA x)` and `ρ(y) ρ(iB y)`, compared with `1`;
- `ρ(h) ρ(v)` and `ρ(v') ρ(h')`, for all nine squares.

So `ρ` extends to a homomorphism `Γ → D^*/K^*`.

It also checks, with `H = t + 1` (the h-place) and `V = t` (the v-place):
- **(T1)** Every `ρ(h)` has primitive coordinates at `H` and at `V`, with `val_H Nrd = 1` and
  `val_V Nrd = 0`. Every `ρ(v)` is the same with `H` and `V` exchanged. In fact `Nrd ρ(h) = t + 1`
  for both classes, and `Nrd ρ(v) = t(t²+t+1)` for #26 and `t` for #12.
- **(T2)** For distinct h-letters `x ≠ y`, `d_H(o_H, ρ(x)^{-1}ρ(y) o_H) ≠ 0`. For distinct v-letters,
  the same holds at `V`.

By §1, (T1) says:
- each `ρ(h)` fixes `o_V` and moves `o_H` to a neighbour;
- each `ρ(v)` fixes `o_H` and moves `o_V` to a neighbour.

(T2) says that distinct letters move the base vertex to distinct neighbours. Since there are three
letters and three neighbours, every neighbour is hit exactly once.

The mutation test in the README confirms that the checker rejects a wrong assignment.

## 3. Faithfulness, the lattice, and irreducibility

Let `Ψ(γ) = (ρ(γ) o_H, ρ(γ) o_V)`, a vertex of `Δ_H × Δ_V`.

**Lemma 3.1.** If `V H` is a reduced v-word followed by a reduced h-word, and `ρ(V H)` fixes both
`o_H` and `o_V`, then `V` and `H` are empty.

*Proof.* Every `ρ(v)` fixes `o_H`, so `ρ(H) o_H = ρ(V)^{-1} ρ(VH) o_H = o_H`. Write
`H = x_1 ⋯ x_n` with `x_{k+1} ≠ iA(x_k)`, and let `p_k = ρ(x_1 ⋯ x_k) o_H`.
- `p_k` and `p_{k+1} = ρ(x_1 ⋯ x_k) ρ(x_{k+1}) o_H` are adjacent, because `ρ(x_{k+1}) o_H` is a
  neighbour of `o_H` (T1).
- `p_{k-1} = p_{k+1}` would mean `ρ(x_k)^{-1} o_H = ρ(x_{k+1}) o_H`. Since `ρ(x_k)^{-1} = ρ(iA x_k)`
  in `D^*/K^*`, (T2) would force `x_{k+1} = iA(x_k)`, which is excluded.

So `p_0, …, p_n` is a non-backtracking path in a tree, and `d(p_0, p_n) = n`. Since `p_n = p_0`, we get
`n = 0`. Then `ρ(V)` fixes `o_V`, and the same argument at `V` gives `V` empty. ∎

**Consequences.**
1. *`ρ` is injective, and normal forms are unique.* If `ρ(γ) = 1`, write `γ = V H` (§0). Lemma 3.1
   gives `γ = 1`. If `V H = V' H'` in `Γ`, then `V'^{-1} V` and `H' H^{-1}` reduce to a reduced pair
   representing `1`, so they are equal: the normal form is unique.
2. *`Ψ` is a bijection onto the vertices of `Δ_H × Δ_V`.*
   - It is injective: `Ψ(γ) = Ψ(γ')` means `ρ(γ^{-1} γ')` fixes both base vertices.
   - Its image contains `(o_H, o_V)`, and it is closed under moving to a neighbour in either factor.
     The neighbours of `ρ(γ) o_H` are `ρ(γ) ρ(x) o_H` for `x ∈ A` (T2 and 3-regularity), and
     `ρ(γ x) o_V = ρ(γ) o_V`. The same holds for v-letters.
   - `Δ_H × Δ_V` is connected, so `Ψ` is surjective.
3. `Ψ(γ x)` and `Ψ(γ y)` are the neighbours of `Ψ(γ)`, so `Ψ` is a `Γ`-equivariant isomorphism from
   the Cayley square complex `T_3 × T_3` of `Γ` onto `Δ_H × Δ_V`.
4. *`ρ(Γ)` is a lattice.* It acts simply transitively on the vertices of `Δ_H × Δ_V`. Vertex
   stabilizers in `PGL_2(K_H) × PGL_2(K_V)` are compact open, and they meet `ρ(Γ)` trivially. So
   `ρ(Γ)` is a discrete, cocompact lattice.
   - This is the arithmetic `{t, t+1}`-lattice attached to `D`, since `D` is ramified at `∞`.
   - It is not used below.

**Irreducibility.** `D^*/K^* → PGL_2(K_V)` is injective, because `K_V^* ∩ D^* = K^*`. `PGL_2(K_V)` acts
faithfully on `Δ_V`.
- By Consequence 1, `⟨A⟩ ≅ Z * Z/2` acts faithfully on `Δ_V`. Under `Ψ`, this is the action of `⟨A⟩`
  on the vertical tree `T_v`.
- By Consequence 2, `⟨A⟩` is exactly the stabilizer of `o_V` in `Γ`.
- This stabilizer acts with infinite image. Hence the projection of `Γ` to `Aut(T_v)` is not discrete,
  and `Γ` is irreducible (Burger–Mozes, Prop. 1.2). This is the criterion used by
  `lo_census.finite_image`.

## 4. The PGL_2 inversion lemma

**Lemma 4.1.** Let `F` be any field and `a, b ∈ GL_2(F)`, with `a b a^{-1} = λ b^{-1}` for some
`λ ∈ F^*`, and `b` not scalar. Then `a²` or `b²` is scalar. In `PGL_2(F)`: if `a b a^{-1} = b^{-1}`
and `b ≠ 1`, then `a² = 1` or `b² = 1`.

*Proof.* Work over the algebraic closure `F̄`. Being scalar does not depend on the field.

- *Case 1: `b` has two distinct eigenvalues `μ_1 ≠ μ_2`,* with eigenlines `L_1, L_2`.
  - `λ b^{-1}` has the same eigenlines, and on `L_r` it has eigenvalue `λ/μ_r`.
  - If `b e = μ e`, then `λ b^{-1} (a e) = a b e = μ (a e)`. So `a` permutes `{L_1, L_2}`.
  - *If `a` fixes both lines,* then `λ/μ_r = μ_r`, so `μ_1² = μ_2² = λ`. Since `μ_1 ≠ μ_2`, this forces
    `μ_2 = −μ_1` and characteristic `≠ 2`, and `b² = λ` is scalar.
  - *If `a` swaps the lines,* then in the eigenbasis `a = [[0, x], [y, 0]]` and `a² = x y` is scalar.
- *Case 2: `b` is not diagonalizable.* Then `b = μ(1 + n)` with `n² = 0`, `n ≠ 0`, and `L = ker n` is
  the unique eigenline of `b` and of `b^{-1}`.
  - `a` preserves `L`, so in a basis `(e_1 ∈ L, e_2)` we have `a = [[x, y], [0, z]]`, `n = [[0,1],[0,0]]`,
    and `a n a^{-1} = (x/z) n`.
  - `a b a^{-1} = μ(1 + (x/z) n)` must equal `λ b^{-1} = (λ/μ)(1 − n)`. So `μ² = λ` and `x/z = −1`.
  - *If `char F ≠ 2`,* `a = [[x, y], [0, −x]]` has trace `0`. By Cayley–Hamilton, `a² = −det a` is
    scalar.
  - *If `char F = 2`,* `b² = μ²(1 + n)² = μ²` is scalar.

Both cases give the claim. ∎

**Corollary 4.2.** Let `char F = 2`, let `a, b ∈ PGL_2(F)` with `b` of infinite order, and let
`a b^p a^{-1} = b^q` with `p, q ≠ 0`. Then `q = p`, or `q = −p` and `a² = 1`.

*Proof.* By Case 2 (`char 2`), a non-diagonalizable `b` has `b² = 1`. So `b` has distinct eigenvalues,
and `r = μ_1/μ_2` is not a root of unity, since `b^m = 1` iff `r^m = 1`.
- For `m ≠ 0`, `b^m` has eigenvalue ratio `r^m ≠ 1` and the same eigenlines as `b`. As in Case 1, `a`
  permutes them.
- If `a` fixes them, comparing ratios gives `r^p = r^q`, so `p = q`.
- If `a` swaps them, then `r^p = r^{-q}`, so `q = −p`, and `a` is antidiagonal, so `a² = 1`. ∎

Lemma 4.1 and Corollary 4.2 apply to `Γ` through the injection
`Γ → D^*/K^* → PGL_2(F_2((t)))` of §3.

## 5. No Klein pair, and no Klein-power chain

**Lemma 5.1.** `Γ^+` is torsion-free.

*Proof.* By (T1), `d(o_H, ρ(γ) o_H) ≡ val_H Nrd ρ(γ)` modulo 2, and this is the number of h-letters of
`γ` modulo 2. The same holds at `V`. So `Γ^+` acts on both trees without inverting types.

A finite-order `γ ∈ Γ^+` has a bounded orbit, so it fixes a point of each tree (Bruhat–Tits fixed-point
theorem). That point is a vertex or the midpoint of an edge. A type-preserving automorphism fixing a
midpoint fixes both ends. So `γ` fixes a vertex `Ψ(δ)` of `Δ_H × Δ_V`. Then `δ^{-1} γ δ` fixes
`(o_H, o_V)`, and Lemma 3.1 gives `γ = 1`. ∎

**Theorem 5.2 (part 3 of the claim).**
1. If `a, b ∈ Γ`, `b ≠ 1` and `a b a^{-1} = b^{-1}`, then `a² = 1` or `b² = 1`.
2. `Γ^+`, and every torsion-free subgroup of `Γ`, contains no pair `a, b` with `b ≠ 1` and
   `a b a^{-1} = b^{-1}`. In particular it has no Klein pair, of any word length.
3. If `a, b ∈ Γ^+`, `b ≠ 1` and `a b^p a^{-1} = b^q` with `p, q ≠ 0`, then `p = q`.

*Proof.*
1. Apply Lemma 4.1 in `PGL_2(F_2((t)))`, using the injection of §3.
2. By part 1 and torsion-freeness, `a = 1` or `b = 1`. Since `b ≠ 1`, we get `a = 1`, so `b = b^{-1}`,
   `b² = 1`, and `b = 1`, a contradiction.
3. By Lemma 5.1, `b` has infinite order. Corollary 4.2 gives `q = p`, or `q = −p` with `a² = 1`. In the
   second case `a = 1`, so `b^{2p} = 1`, which is impossible. ∎

So `Γ^+` contains no subgroup isomorphic to the Klein-bottle group `BS(1, −1)`, and no `BS(p, q)` with
`p ≠ q`. The pure-pair searches of `bmw-klein-frame-chain-certificates` (lengths `|A| < 18`,
`|B| < 16`) and the conjugate-frame searches were empty for this reason. The bound on length is now
removed.

**Corollary 5.3 (part 4).** Corollary 3 of `bmw-census-klein-power-chain-certificates-proof` needs a
cycle of nontrivial elements with at least one step of type (K): `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}`.
By Theorem 5.2(2), no such step exists in `Γ^+`, or in any torsion-free subgroup of `Γ`. So no
Klein-power chain certifies `Γ^+`, or any torsion-free subgroup of `Γ`, whatever the lengths. ∎

**Scope.** §4 uses only an injection `Γ → PGL_2(F)`. So for every BMW class whose group embeds in some
`PGL_2(F)`, the parity kernel has no Klein pair. If the kernel is torsion-free, it also has no
Klein-power chain. In characteristic `0`, unipotent elements do allow `BS(1, n)`, but Theorem 5.2(2)
still holds.

## 6. A cone-propagation certificate (part 5)

**Certificates.** A certificate is a binary tree.
- A node `["split", g, T_1, T_2]` has `g ∈ Γ^+` with `nf(g) ≠ ()`. Its branch `T_1` assumes `g ∈ P`,
  and `T_2` assumes `g^{-1} ∈ P`.
- A leaf `["leaf", [x, y], steps]` lists steps `[z, u, w]`. Each step asserts `z = u w` in `Γ`, with
  `u, w` already in `P`, so `z ∈ P`. They are already in `P` if they were assumed on the path to the
  leaf or derived by an earlier step of the same leaf. Finally, the leaf asserts `x, y ∈ P` and
  `x y = 1`.

**Soundness.** Suppose `Γ^+` had a left order with positive cone `P`, so `P P ⊆ P` and
`Γ^+ = P ⊔ P^{-1} ⊔ {1}`.
- At a split, `nf(g) ≠ ()` gives `g ≠ 1`, by the uniqueness of normal forms in §3. `verify_cone.py`
  checks this independently: it verifies Newman's critical pairs for the rewriting system
  `h v → v' h'`, `x iA(x) → 1`, `y iB(y) → 1`, which terminates. So `g ∈ P` or `g^{-1} ∈ P`, and
  some branch is consistent with `P`.
- Following the consistent branches reaches a leaf all of whose assumptions hold for `P`. Each step
  keeps us in `P`: `nf(z) = nf(u w)` implies `z = u w`, since each rule is a relation of `Γ`.
- At the leaf, `x ∈ P` and `x^{-1} = y ∈ P`, which contradicts `P ∩ P^{-1} = ∅`.

So `Γ^+` is not left-orderable. For these two classes, this gives a solver-free proof of what
`small-degree-irreducible-bmw-parity-kernels-not-left-orderable` proves with a SAT solver.

**The two trees** are found by `dtree.py` on the radius-4 ball. There are no trees of depth 1 or 2,
and both trees have depth 3, 6 leaves and 54 product steps in all. The second half of each tree mirrors the
first, with `P` and `P^{-1}` exchanged.

`31_30` #26, `tree_31_30_26.json`:

| path | leaf `x, y` | steps |
|---|---|---|
| `+v0v2, +v0v2h1h2, +v2v0h1h1` | `v0v1h2h1, v2v0h2h1` | 6 |
| `+v0v2, +v0v2h1h2, −v2v0h1h1` | `v0v2h2h0, v2v1h2h0` | 12 |
| `+v0v2, −v0v2h1h2` | `h1h1, h0h0` | 9 |
| `−v0v2, +v0v2h1h2` | `h0h0, h1h1` | 9 |
| `−v0v2, −v0v2h1h2, +v2v0h1h1` | `h1h2h0h2, h2h1h2h0` | 12 |
| `−v0v2, −v0v2h1h2, −v2v0h1h1` | `v2v1v0v2, v2v0v1v2` | 6 |

`31_31` #12, `tree_31_31_12.json`:

| path | leaf `x, y` | steps |
|---|---|---|
| `+v1v1h2h1, +v2v0v0v2, +v2v0h2h0` | `v2v1h1h1, v2v1h0h2` | 7 |
| `+v1v1h2h1, +v2v0v0v2, −v2v0h2h0` | `h0h0h2h1, h0h2h1h1` | 7 |
| `+v1v1h2h1, −v2v0v0v2` | `v1v2h1h1, v1v2h2h0` | 13 |
| `−v1v1h2h1, +v2v0v0v2` | `v1v2h2h0, v1v2h1h1` | 13 |
| `−v1v1h2h1, −v2v0v0v2, +v2v0h2h0` | `v1v2h2h0, v1v2h1h1` | 7 |
| `−v1v1h2h1, −v2v0v0v2, −v2v0h2h0` | `v2v1h0h2, v2v1h1h1` | 7 |

Here `+g` means `g ∈ P` and `−g` means `g^{-1} ∈ P`.

`verify_cone.log` records `certificate OK: 6 leaves, 54 product steps` for both classes. The checker
uses only the census squares. Every factor it uses must already be in `P`, and every product must lie
in `Γ^+`.

By Theorem 5.2, no step of these trees is a Klein relation. The certificates are genuinely
non-abelian. Each leaf uses at most 13 product steps inside the radius-4 ball.

## 7. What is and is not ruled out

- *Ruled out, at every length:* pure and conjugate Klein pairs, and Klein-power chains in the sense of
  Corollary 3, for `Γ^+` and for every torsion-free subgroup of `Γ`. Likewise any certificate needing
  `a b a^{-1} = b^{-1}` with `b ≠ 1`, or `a b^p a^{-1} = b^q` with `p ≠ q`, inside `Γ^+`.
- *Not ruled out:* (P) and (R) power steps alone, which cannot close a cycle strictly. Neither is the
  use of Klein relations in `Γ` involving torsion (for example `h_2 w h_2 = w^{-1}`, where
  `h_2² = 1`).
- *Left orders:* `Γ^+` has none, by §6. So no Burns–Hale or Dehornoy-type construction can exist, and
  the step's first alternative is closed.
