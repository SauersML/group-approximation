---
rg: 2
id: bmw-quaternionic-type-53-parity-kernels-proof
kind: route
title: Proof via explicit representations in [1, t+1) and [t, t²+t+1) over F_2(t), the tree-path faithfulness argument with a valency-5 tree, the PGL_2 inversion lemma, and cone trees
target: bmw-quaternionic-type-53-parity-kernels
requires: []
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep2.py
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep2.log
  - experiments/bmw-cone-trees-2026-09-18/quat2_53.out
  - experiments/bmw-cone-trees-2026-09-18/verify_cone.py
  - experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.log
---

# Proof

The argument is that of `bmw-klein-free-quaternionic-parity-kernels-proof`, carried over from two
valency-3 trees to a valency-5 and a valency-3 tree. Everything used is restated below. Only the
numbers change.

## 0. The groups

A class `c` of `census_<pattern>.json` (in `experiments/bmw-census-left-orders-2026-09-17/`) consists
of:
- h-letters `A` (`|A| = m`) with inversion `iA`, and v-letters `B` (`|B| = n`) with inversion `iB`;
- `m n` squares `h v = v' h'`, one for each pair `(h, v)`.

`Γ` is presented by `A ∪ B`, the relations `x · iA(x) = 1` and `y · iB(y) = 1`, and the squares.
- **Normal form.** Every `γ` is `V H`, with `V` a reduced v-word and `H` a reduced h-word.
- **Parity.** `ε : Γ → (Z/2)²` counts letters of each kind mod 2, and `Γ^+ = ker ε`.

For the six classes of family 53, `m = 5` and `n = 3`. For `30_30` #16, `m = n = 3` and all letters are
involutions.

## 1. The algebra `D = [1, t+1)` and its trees

Let `K = F_2(t)`, `a = 1` and `b = t + 1`. `D` has basis `1, i, j, k = ij`, with `i² = i + a`, `j² = b`
and `j i = (i+1) j`. This is the multiplication table of `bmw-klein-free-quaternionic-parity-kernels-proof`
§1 with `a = 1`.

`verify_quat_rep2.py` checks associativity on all 64 basis triples. It also checks:
- `Trd x = c_1`, `x̄ = (c_0 + c_1) + c_1 i + c_2 j + c_3 k`;
- `Nrd x = N(c_0 + c_1 i) + b N(c_2 + c_3 i)`, with `N(u + w i) = u² + u w + w²`.

**Ramification.**
- *At `t+1`.* `x² + x + 1` has no root mod `t + 1` (checked), so `K_{t+1}(i)` is the unramified
  quadratic extension. Its norms have even valuation, while `b` is a uniformizer. So `D_{t+1}` is a
  division algebra, and hence `D` is one.
- *At a finite `Q ≠ t+1`.* `b` is a unit, and units are norms from an unramified or split extension.
  So `D` splits at `Q`, in particular at `t` and at `t²+t+1`.
- `F_2(i) = F_4`, so `D ⊃ F_4(t)` and `j` acts on it by Frobenius.

**The order.** `O = F_2[t]⟨1, i, j, k⟩` is a ring with `det(Trd(e_r e_s)) = b²` (checked). So `O_Q` is
maximal at every `Q ∤ b`. At `Q ∈ {t, t²+t+1}` we may take `O_Q = M_2(O_Q)`, and `Nrd` becomes `det`.

**Trees.** `Δ_Q` is the Bruhat–Tits tree of `PGL_2(K_Q)`, with base vertex `o_Q = [O_Q²]`.
- It is 3-regular at `Q = t` (residue field `F_2`) and 5-regular at `Q = t²+t+1` (residue field `F_4`).
- For `x = Σ c_r e_r ≠ 0`, `d(o_Q, x o_Q) = val_Q(Nrd x) − 2 min_r val_Q(c_r)`. This is `dist` in the
  scripts: after dividing by the content, `x ∈ M_2(O_Q) ∖ π M_2(O_Q)` has elementary divisors
  `1, π^{val det}`.

**Degree formula.** `u² + u w + w²` is anisotropic over `F_2`, so `deg N(u + w i) = 2 max(deg u, deg w)`.
The two summands of `Nrd` have even and odd degree, so
`deg Nrd x = max(2 deg(c_0, c_1), 2 deg(c_2, c_3) + 1)`. This is used only in §7.

## 2. The representations

Coordinates `(c_0, c_1, c_2, c_3)` mean `c_0 + c_1 i + c_2 j + c_3 k`. The h-tree is at
`H = t² + t + 1`, and the v-tree at `V = t`.

| class | `h_0` | `h_1` | `h_2` | `h_3` | `h_4` | `v_0` | `v_1` | `v_2` |
|---|---|---|---|---|---|---|---|---|
| `50_31` #243 | `t+1 + tk` | `j + tk` | `j + (t+1)k` | `t + j + k` | `t + j` | `i + k` | `1 + i + k` | `t+1 + k` |
| `51_30` #660 | `(t+1)i + tk` | `t+1 + (t+1)i + tk` | `(t+1)j + tk` | `(t+1)j + k` | `t+1 + tk` | `1 + j` | `1 + j + k` | `1 + k` |
| `51_31` #279 | `(t+1)i + tk` | `t+1 + (t+1)i + tk` | `j + (t+1)k` | `j + tk` | `t+1 + tk` | `1 + i + k` | `i + k` | `1 + k` |
| `51_31` #309 | `1 + (t+1)i` | `t + (t+1)i` | `t + k` | `t + j` | `t + j + k` | `(t+1)i + k` | `t+1 + (t+1)i + k` | `t+1 + k` |
| `52_30` #386 | `(t+1)i + tk` | `t+1 + (t+1)i + tk` | `t + (t+1)i` | `1 + (t+1)i` | `t + k` | `1 + j` | `1 + j + k` | `t+1 + k` |
| `52_31` #185 | `(t+1)i + tk` | `t+1 + (t+1)i + tk` | `t+1 + i` | `t + i` | `t + k` | `1 + i + k` | `i + k` | `t+1 + k` |

For example, `Nrd(t + j) = t² + (t+1) = t² + t + 1` and `Nrd(t+1 + k) = (t+1)² + (t+1) = t(t+1)`.

`verify_quat_rep2.py` checks, exactly in `F_2[t]`:
- **(R)** `ρ(x) ρ(iA x)` and `ρ(y) ρ(iB y)` are nonzero scalars. For every square, `ρ(h) ρ(v)` is a
  nonzero scalar multiple of `ρ(v') ρ(h')`. So `ρ` is a homomorphism `Γ → D^*/K^*`.
- **(T1)** Every `ρ(h)` has content prime to `H` and to `V`, with `d_H = 1` and `d_V = 0`. Every
  `ρ(v)` has `d_V = 1` and `d_H = 0`.
- **(T2)** For distinct h-letters `x ≠ y`, `d_H(o_H, ρ(x)^{-1} ρ(y) o_H) ≠ 0`. For distinct v-letters,
  the same holds at `V`.

`ρ(x)^{-1}` is computed as `x̄`, which is the same element of `D^*/K^*`. The log `verify_quat_rep2.log`
ends with `all 7 representations OK`.

By §1:
- (T1) says that each `ρ(h)` fixes `o_V` and moves `o_H` to a neighbour, and each `ρ(v)` fixes `o_H`
  and moves `o_V` to a neighbour.
- (T2) says that distinct letters of one kind give distinct neighbours. There are five h-letters and
  five neighbours of `o_H`, and three v-letters and three neighbours of `o_V`. So each neighbour is hit
  exactly once.

## 3. Faithfulness, irreducibility, torsion

**Lemma 3.1.** If `V H` is a reduced v-word followed by a reduced h-word, and `ρ(V H)` fixes `o_H` and
`o_V`, then `V` and `H` are empty.

*Proof.* `ρ(V)` fixes `o_H`, so `ρ(H)` fixes `o_H`. Write `H = x_1 ⋯ x_r` and
`p_k = ρ(x_1 ⋯ x_k) o_H`.
- Consecutive points are adjacent, by (T1).
- `p_{k-1} = p_{k+1}` would give `ρ(iA x_k) o_H = ρ(x_{k+1}) o_H`, so `x_{k+1} = iA x_k` by (T2),
  which is excluded.

So `(p_k)` is a non-backtracking path in a tree, and `p_r = p_0` forces `r = 0`. Then `ρ(V)` fixes
`o_V`, and the same argument gives `V` empty. ∎

As in `bmw-klein-free-quaternionic-parity-kernels-proof` §3:
1. `ρ` is injective and normal forms are unique.
2. `Ψ(γ) = (ρ(γ) o_H, ρ(γ) o_V)` is a `Γ`-equivariant isomorphism from `T_5 × T_3` (resp. `T_3 × T_3`)
   onto `Δ_H × Δ_V`. The neighbours of `ρ(γ) o_H` are exactly the points `ρ(γ) ρ(x) o_H`, by (T2) and
   5-regularity.
3. `⟨A⟩` is the stabilizer of `o_V`. It acts faithfully on `Δ_V`, since `D^*/K^* → PGL_2(K_V)` is
   injective and `PGL_2(K_V)` acts faithfully. It is infinite, so its image in `Aut(T_v)` is not
   discrete and `Γ` is irreducible (Burger–Mozes, Prop. 1.2).
4. `Γ^+` is torsion-free. By (T1), `d(o_H, ρ(γ) o_H) ≡ val_H Nrd ρ(γ)`, which is the number of
   h-letters of `γ` mod 2, and likewise at `V`. So `Γ^+` preserves types on both trees. A finite-order
   element then fixes a vertex of `Δ_H × Δ_V`, and after conjugation Lemma 3.1 makes it trivial.

## 4. No Klein pair

**Lemma 4.1 (PGL_2 inversion lemma).** Let `F` be a field and `a, b ∈ PGL_2(F)` with
`a b a^{-1} = b^{-1}` and `b ≠ 1`. Then `a² = 1` or `b² = 1`.

*Proof* (lift to `GL_2(F̄)`, with `a b a^{-1} = λ b^{-1}`).
- *`b` has distinct eigenvalues `μ_1 ≠ μ_2`.* Then `a` permutes the two eigenlines.
  - If it swaps them, `a` is antidiagonal in the eigenbasis, so `a²` is scalar.
  - If it fixes them, `μ_r² = λ` for both `r`. So `μ_2 = −μ_1` in characteristic `≠ 2`, and `b²` is
    scalar.
- *`b = μ(1 + n)` with `n² = 0 ≠ n`.* Then `a` preserves `ker n`, and comparing gives `a n a^{-1} = −n`.
  - In characteristic `≠ 2`, `a` has trace `0`, so `a²` is scalar.
  - In characteristic 2, `b² = μ²` is scalar. ∎

In characteristic 2, and with `b` of infinite order, the same eigenline argument turns
`a b^p a^{-1} = b^q` (`p, q ≠ 0`) into `q = p`, or `q = −p` with `a² = 1`
(`bmw-klein-free-quaternionic-parity-kernels-proof`, Corollary 4.2).

Apply this through the injection `Γ → D^*/K^* → PGL_2(F_2((t)))` of §3.
- If `a b a^{-1} = b^{-1}` in `Γ^+` with `b ≠ 1`, then `a² = 1` or `b² = 1`. Torsion-freeness gives
  `a = 1`, then `b² = 1`, then `b = 1`, a contradiction. So `Γ^+`, and every torsion-free subgroup of
  `Γ`, has no Klein pair at any length.
- `Γ^+` has no `BS(p, q)` with `p ≠ q`.
- Every Klein-power chain (Corollary 3 of `bmw-census-klein-power-chain-certificates-proof`) needs a
  (K) step `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` with `x_i ≠ 1`. So none exists for `Γ^+`.

## 5. Cone trees

A certificate is a binary tree with the format and the soundness argument of
`bmw-klein-free-quaternionic-parity-kernels-proof` §6.
- `["split", g, T_1, T_2]` branches on `g ∈ P` or `g^{-1} ∈ P`, where `g ∈ Γ^+` and `nf(g) ≠ ()`. By
  the uniqueness of normal forms, which `verify_cone.py` rechecks through the critical pairs of the
  rewriting system, this means `g ≠ 1`.
- A leaf derives elements of `P` by products `z = u w` of elements already in `P`, and ends with
  `x, y ∈ P` and `x y = 1`.

If `P` were the positive cone of a left order on `Γ^+`, the branches consistent with `P` would lead to
a leaf, which is a contradiction.

The seven trees are the records `(50_31, 243)`, `(51_30, 660)`, `(51_31, 279)`, `(51_31, 309)`,
`(52_30, 386)`, `(52_31, 185)` and `(30_30, 16)` of `trees.jsonl.gz`. `verify_trees.log` has, for
instance, `50_31 243 R=4 census_50_31.json 243 certificate OK: 10 leaves, 318 product steps`. The
sizes are listed in the claim.

By §4, no step of these trees is a Klein relation inside `Γ^+`.

## 6. `30_30` #16 in `[t, t²+t+1)`

Here `D = [t, t²+t+1)`, which is §1 of `bmw-klein-free-quaternionic-parity-kernels-proof`. The v-tree is
at `t` and the h-tree at `t + 1`.

| `h_0` | `h_1` | `h_2` | `v_0` | `v_1` | `v_2` |
|---|---|---|---|---|---|
| `t²+t+1 + tj` | `t²+t+1 + tj + k` | `t²+t+1 + (t+1)j + k` | `t²+t+1 + (t+1)j` | `k` | `j + k` |

`verify_quat_rep2.py` checks (R), (T1) and (T2) as in §2, and §3–§5 apply unchanged with two
3-regular trees.

## 7. Exhaustiveness of the negative search (`50_30` #499, #515, `50_31` #235, `51_30` #661)

`findquat.py census c 1 1 3 2 7` (`runquat2_53.sh`) searches `D = [1, t+1)`, `V = t`, `H = t²+t+1`, over
all primitive letters with coordinates of degree at most 1 that satisfy (T1). Involutions are
restricted to `Trd = 0`, which is forced, because `x² = Trd(x) x − Nrd(x)`. The search is a complete
backtracking over the candidates, with propagation through the squares.

Suppose a representation with base vertices `o_H, o_V` of `O` has every letter's `Nrd` supported on
`{t, t²+t+1, t+1}`.
- By (T1), after scaling, `Nrd ρ(v) = t (t+1)^e` and `Nrd ρ(h) = (t²+t+1)(t+1)^e`.
- One may take `e ≤ 1`. At the ramified place, `val_{t+1} Nrd x ≥ 2` means `x ∈ j² O_{t+1}`, that is,
  `x` is divisible by `t + 1`.
- So `deg Nrd ≤ 3`, and the degree formula of §1 gives coordinates of degree at most 1.

The search covers all such letters and found none for these four classes. Other maximal orders, other
algebras, and non-`S`-integral models were not searched.

For each of the six classes of §2 it found exactly two representations (both logged); §2 lists the
first.
