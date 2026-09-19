---
rg: 2
id: bmw-quaternionic-char3-type-44-parity-kernels-proof
kind: route
title: Proof via explicit representations in (−1, t+1) over F_3(t), the tree-path faithfulness argument with two 4-regular trees, the PGL_2 inversion lemma, and cone trees
target: bmw-quaternionic-char3-type-44-parity-kernels
requires: []
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep3.py
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep3.log
  - experiments/bmw-cone-trees-2026-09-18/quat3_44.jsonl
  - experiments/bmw-cone-trees-2026-09-18/quat3b_44.jsonl
  - experiments/bmw-cone-trees-2026-09-18/findquat3.py
  - experiments/bmw-cone-trees-2026-09-18/verify_cone.py
  - experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.log
---

# Proof

The argument is that of `bmw-quaternionic-type-53-parity-kernels-proof`, moved to characteristic 3.
Its §0 (the groups, normal forms `V H`, the parity map `ε` and `Γ^+ = ker ε`) is used unchanged, with
`m = n = 4`. Below, only what changes is written out.

## 1. The algebra and its trees

Let `K = F_3(t)` and `D = (−1, t+1)`, with basis `1, i, j, k = ij` and relations `i² = −1`,
`j² = b = t + 1`, `ji = −ij`. `verify_quat_rep3.py` checks associativity of the structure constants on
all 64 basis triples. For `x = x_0 + x_1 i + x_2 j + x_3 k`:
- `x̄ = x_0 − x_1 i − x_2 j − x_3 k`;
- `Nrd x = x x̄ = (x_0² + x_1²) − b (x_2² + x_3²)`.

**Ramification.**
- *At `t+1`.* `−1` is not a square in `F_3`, the residue field (checked). So `K_{t+1}(i)` is the
  unramified quadratic extension, its norms have even valuation, and `b` is a uniformizer. Hence
  `D_{t+1}` is a division algebra, and so is `D`.
- *At a finite `Q ≠ t+1`.* Both `−1` and `b` are units, and `p = 3` is odd, so the Hilbert symbol is
  trivial and `D` splits at `Q`. In particular it splits at `t` and at `t − 1`.
- *At `∞`.* By the product formula `D` is ramified at `∞` as well. `F_3(i) = F_9`, and `j` acts on
  `F_9(t)` by Frobenius.

**The order and the trees.** `O = F_3[t]⟨1, i, j, k⟩` has `det(Trd(e_r e_s)) = −16 b²`, a unit times
`b²` (checked). So `O_Q` is maximal at every `Q ≠ t+1`. At `Q ∈ {t, t−1}` we identify
`O_Q = M_2(O_Q)`, so that `Nrd = det`.
- `Δ_Q` is the Bruhat–Tits tree, with base vertex `o_Q = [O_Q²]`.
- It is 4-regular, since the residue field is `F_3`.
- `d(o_Q, x o_Q) = val_Q Nrd x − 2 min_r val_Q x_r`.

**Degree formula.** `x² + y²` is anisotropic over `F_3`, so `deg(x_0² + x_1²) = 2 deg(x_0, x_1)`. Hence
`deg Nrd x = max(2 deg(x_0, x_1), 2 deg(x_2, x_3) + 1)`. This is used only in §5.

## 2. The representations

The h-tree is at `H = t − 1`, and the v-tree at `V = t`. The letters, as found by `findquat3.py` and
logged in `quat3_44.jsonl`, are (inverse pairs as in the census files: `iA` and `iB`):

| class | `h_0` | `h_1` | `h_2` | `h_3` | `v_0` | `v_1` | `v_2` | `v_3` |
|---|---|---|---|---|---|---|---|---|
| `40_40` #818 | `i+j+k` | `i+j−k` | `i−j+k` | `i−j−k` | `i+j` | `i+k` | `i−j` | `i−k` |
| `41_40` #1182 | `1+j+k` | `1−j−k` | `i+j+k` | `i−j−k` | `(t+1)i+k` | `(t+1)i−k` | `(t+1)i−j` | `(t+1)i+j` |
| `42_40` #472 | `1+i+k` | `1−i−k` | `1−i+k` | `1+i−k` | `(t+1)i+k` | `(t+1)i+j` | `(t+1)i−k` | `(t+1)i−j` |
| `42_40` #535 | `1+j+k` | `1−j−k` | `1+j−k` | `1−j+k` | `i+j` | `i+k` | `i−k` | `i−j` |
| `42_41` #318 | `1+i+k` | `1−i−k` | `1+i−k` | `1−i+k` | `1−j` | `1+j` | `i−j` | `i+j` |
| `42_41` #500 | `1+j+k` | `1−j−k` | `1+j−k` | `1−j+k` | `(t+1)−k` | `(t+1)+k` | `(t+1)i+k` | `(t+1)i−k` |
| `42_41` #533 | `1+i+k` | `1−i−k` | `1+i−k` | `1−i+k` | `1−k` | `1+k` | `i−k` | `i+k` |
| `42_42` #97 | `1+i+k` | `1−i−k` | `1−i+k` | `1+i−k` | `(t+1)−j` | `(t+1)+j` | `(t+1)−k` | `(t+1)+k` |
| `42_42` #114 | `1+j+k` | `1−j−k` | `1+j−k` | `1−j+k` | `1−k` | `1+k` | `1−j` | `1+j` |

In `40_40` #818 all eight letters are involutions. The inverse pairs are `h_0 h_1` (`41_40` #1182),
`h_0 h_1` and `h_2 h_3` (`42_40`), these plus `v_0 v_1` (`42_41`), and these plus `v_2 v_3` (`42_42`). In each such pair the
second letter is the conjugate `x̄` of the first, so `x x̄ = Nrd x ∈ K^*`; for instance
`(1 + i + k)(1 − i − k) = 1 − (i + k)² = 1 − t`. Every other letter is an involution and is a
pure quaternion, as it must be: `x² = Trd(x) x − Nrd(x)`.

For example, `Nrd(i + j + k) = 1 − (t+1) − (t+1) = t − 1`, and `Nrd((t+1) i + k) = (t+1)² − (t+1) = t(t+1)`.

`verify_quat_rep3.py` reads the letters from `quat3_44.jsonl` and checks, exactly in `F_3[t]`, the
conditions (R), (T1) and (T2) of `bmw-quaternionic-type-53-parity-kernels-proof` §2:
- **(R)** `ρ` respects the inverse pairs and all 16 squares in `D^*/K^*`;
- **(T1)** h-letters have content prime to `H` and `V`, with `d_H = 1` and `d_V = 0`, and v-letters the
  reverse;
- **(T2)** distinct letters of one kind move the base vertex to distinct neighbours.

The log `verify_quat_rep3.log` ends with `all 9 representations OK`. There are four letters of each
kind and four neighbours, so each neighbour is hit exactly once.

## 3. Faithfulness, irreducibility, torsion

Lemma 3.1 of `bmw-quaternionic-type-53-parity-kernels-proof` uses only (T1), (T2) and the fact that
`Δ_H` and `Δ_V` are trees, so it holds verbatim. Hence:
- `ρ` is injective;
- `Ψ(γ) = (ρ(γ) o_H, ρ(γ) o_V)` is a Γ-equivariant isomorphism `T_4 × T_4 → Δ_H × Δ_V`;
- `⟨A⟩ = Stab(o_V)` is infinite and acts faithfully on `Δ_V`, so `Γ` is irreducible (Burger–Mozes,
  Prop. 1.2).

`Γ^+` is torsion-free. The h-letters have `val_H Nrd = 1` and `val_V Nrd = 0`, and the v-letters the
reverse. So `Γ^+` preserves types on both trees. A torsion element therefore fixes a vertex of the
product, which after conjugation is `(o_H, o_V)`, and Lemma 3.1 makes it trivial.

## 4. No Klein pair, no `BS(p, q)`

Lemma 4.1 of `bmw-quaternionic-type-53-parity-kernels-proof`, the PGL_2 inversion lemma, holds over any
field. Through `Γ ↪ D^*/K^* ↪ PGL_2(F_3((t)))` it gives, exactly as there, that there is no
`a b a^{-1} = b^{-1}` with `b ≠ 1` in `Γ^+`. Hence no Klein-power chain exists.

**`BS(p, q)` in characteristic 3.** Take `b ∈ PGL_2(F)` of infinite order, with `char F = 3`.
- A scalar times a unipotent has order 3 in `PGL_2`. So `b` is semisimple over `F̄`, with an eigenvalue
  ratio `μ` that is not a root of unity.
- Every `b^p` with `p ≠ 0` has the same two eigenlines. If `a b^p a^{-1} = b^q`, then `a` permutes
  these lines.
  - If `a` fixes them, `μ^p = μ^q`, so `p = q`.
  - If `a` swaps them, `q = −p` and `a²` is scalar.
- In the torsion-free group `Γ^+` the second case gives `a = 1`, then `b^{2p} = 1`, then `b = 1`.

So `a b^p a^{-1} = b^q` with `b ≠ 1` forces `p = q`.

## 5. Exhaustiveness of the search

Suppose a representation of a class in `D` satisfies (T1) and (T2) at `V = t` and `H = t − 1` with the
base vertices of `O`, and every letter's `Nrd` is supported on `{t, t−1, t+1}`. Scale each letter to be
primitive in `F_3[t]^4`.
- By (T1), `Nrd ρ(h) = c (t−1) (t+1)^e` and `Nrd ρ(v) = c t (t+1)^e`, with `c ∈ F_3^*`.
- `O_{t+1}` is the maximal order of the local division algebra, since its discriminant is `b`. So
  `val_{t+1} Nrd x ≥ 2` means `x ∈ (t+1) O_{t+1}`, and primitivity forces `e ≤ 1`.
- Then `deg Nrd ≤ 2`, and the degree formula of §1 gives `deg(x_0, x_1) ≤ 1` and `deg(x_2, x_3) = 0`.

`findquat3.py` with `STRICT=1` and `d = 1` enumerates all primitive letters of this shape. Its
normalisation makes the first nonzero coordinate monic, which fixes the projective class. Involutions
are restricted to `x_0 = 0`, which is forced. It then runs a complete backtracking search over these
candidates.

So for the classes of `quat3_44.jsonl` marked `found: false` in `D`, with these places and this order,
no such representation exists. Other maximal orders (other base vertices), other pairs of places and
other algebras are not covered.
