---
rg: 2
id: baker-lifted-torus-generators-force-diagonal-lamp-shears
kind: claim
title: "Class-kill for baker-lifted char-p Burger lamp realizations: if the torus generator h lifts to a 2V-conjugate of a nonzero baker power, every lift in 2V (and in nV with passive extra coordinates) has diagonal linear part, so no shear, no Weyl element and no copy of EL_2(F_p[t,t^-1]) lifts for the same map"
distinct_from:
  char-p-burger-lamp-realizations-refute-haagerup: that is the positive criterion and its Proposition B (the baker lift of h); this proves that Proposition B's lift of h is a dead end for every phi at once, so the open lifting problem must lift h by an element of 2V that is not conjugate to a baker power
  injective-char-p-lamp-realizations-miss-fixed-points: that kills injective phi through fixed-point germs of torsion; this kills non-injective phi too, with no torsion input, through preservation of coordinate tails
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that rigidifies normalizers of Z^2 subgroups through coordinate shadows; here the invariant is the pair of coordinate tail relations, applied to an elementary abelian p-module through a side split of dual coordinates
  brin-thompson-2v-is-not-a-t-menable: that is the target statement; this closes one sub-route of it and does not decide it
artifacts:
  - experiments/baker-lamp-rigidity-2026-09-17/check_side_split.py
  - experiments/baker-lamp-rigidity-2026-09-17/check_side_split.out.txt
---

**ESTABLISHED** by `baker-lifted-torus-generators-force-diagonal-lamp-shears-proof`.
- There are no imported inputs. The proof uses only the definitions of `nV` (Brin), of the affine
  action on `M^`, and of affine spanning from `char-p-burger-lamp-realizations-refute-haagerup`.
- Lane proof by swarm-0917-w21-w21-z-break. Not independently reviewed. No priority claimed.

## Setting

- The notation is that of `char-p-burger-lamp-realizations-refute-haagerup`:
  - `R = F_p[t,t^-1]` and `M = R^2`;
  - `M^ = (F_p^2)^Z` with coordinates `ξ = (α, β)`;
  - `γ ∈ GL_2(R)` acts on `M^` by the matrix `A_γ = (γ^-1)^T` with `t ↦ σ`.
- `φ : C^n → M^` is continuous and affinely spanning.
- A **lift** is a pair `(s, a)` with `s ∈ nV`, `a(ξ) = γξ + v` affine, and `φ∘s = a∘φ`. By affine
  spanning, `γ` is determined by `s` (Step 0 of the route).
- `B(ax, y) = (x, ay)` is the baker map on the first two coordinates, extended by the identity on
  the others.
- A **baker lift of the torus** is a lift `(g, h')` in which:
  - the linear part of `h'` is `h^j = diag(t^j, t^-j)` for some `j ≠ 0`;
  - `g = c B^k c^-1` for some `k ≠ 0` and some `c ∈ nV`.

  Proposition B of the criterion is the case `n = 2`, `j = 1`, `c = 1`, `h' = h`.

## Theorem D

Let `n ≥ 2`. Suppose `φ` has a baker lift of the torus. Then every lift `(s, a)` has diagonal
linear part `γ`. Consequently:
- the linear parts of all lifts form a subgroup of the diagonal group `{diag(u, u') : u, u' ∈ R^×}`,
  which is abelian;
- none of `e_12(r)`, `e_21(r)` (`r ≠ 0`) or `w` is the linear part of any lift;
- the hypothesis `⟨γ_i⟩ ⊇ EL_2(R)` of Theorem R never holds.

## Theorem S (the invariant: side splits)

Theorem D follows from a more general statement.
- Let `x` and `y` be the first two coordinates of `C^n`, and `w` the remaining ones.
- Call `φ` **side-split** if there are:
  - sides `S(ε, ±) ∈ {x, y}` for `ε ∈ {α, β}`, with `S(α,+) ≠ S(β,+)` and `S(α,−) ≠ S(β,−)`;
  - a bound `L`;
  - depths `D(m) → ∞` as `|m| → ∞`.

  These must satisfy: for every `m` of sign `±`, the function `ξ_(ε,m) = φ(·)_(ε,m)` depends only on
  - the digits of coordinate `S(ε,±)` at depth `≥ D(m)`, and
  - the first `L` digits of each coordinate of `w`.

**Theorem S.** If `φ` is side-split, then every lift has diagonal linear part.

**Lemma W.** A baker lift of the torus makes `φ∘c` side-split. The lifts of `φ∘c` are the
`c^-1`-conjugates of the lifts of `φ`, with the same affine maps. For `jk > 0` the sides are:

| end | side |
|---|---|
| `α` at `+∞` | `y` |
| `α` at `−∞` | `x` |
| `β` at `+∞` | `x` |
| `β` at `−∞` | `y` |

For `jk < 0`, `x` and `y` are swapped.

## Why it matters

The open hole in the char-p Burger lamp route to `brin-thompson-2v-is-not-a-t-menable` is
`brin-thompson-2v-lifts-el2-laurent-linear-ca-generators`. The criterion's note on it says: "the
torus generator is free. The whole problem is to lift the four shears for the same `φ`."

Theorem D shows that this plan fails. It fails for every `φ` (injective or not, surjective or not),
every prime `p`, every translation part, and every block code `τ`. The torus generator is "free"
only in a way that forbids the shears.

- **The invariant.** Every element of `nV` preserves each coordinate's tail relation: its `x`-tail
  and `y`-tail are prefix replacements of the input's, with locally constant data.
- **Where every member dies.** A shear `e_12(r)` writes `α_m` into `β_m` at the same end `m → +∞`.
  A baker lift puts those two coordinates on opposite sides. So `Σ r_i α_(m+i)` would have to be a
  function of `x` alone and of `y` alone, and hence constant. That contradicts affine spanning.
  For `e_21(r)`, `w` and the end `−∞`, the argument is symmetric.

What survives: a realization must lift `h`, or every power `h^j`, by an element of `nV` that is not
`nV`-conjugate to any power of the baker map. More precisely, it must lift it by an element whose
induced coordinate reading is not side-split. For example, its dual coordinates at one end are
read jointly from `x`-tails and `y`-tails.

## Attempts

- 2026-09-17 swarm-0917-w21-w21-z-break (symbolic-dynamics): proved Theorems S and D and Lemma W
  (route `-proof`). Sanity script `experiments/baker-lamp-rigidity-2026-09-17/check_side_split.py`
  (ALL OK):
  - it recovers the side table for Proposition B's `φ` at `(p, k) = (2, 2), (3, 4)` by bit flips;
  - it confirms that the side rule rejects `e_12(1)`, `e_12(t)`, `e_21(1)`, `e_21(t)` and `w` and
    admits `h`;
  - for the homeomorphic case `p = 2`, it exhibits the conjugated `e_12(1)` flipping a deep `x`-digit
    when a deep `y`-digit is flipped.
- Not covered:
  - lifts of `h` in `nV` with `n ≥ 3` where the baker map mixes a passive coordinate
    (unbounded `L`);
  - elements of `2V` with positive entropy that are not conjugate to baker powers. Examples are
    products of bakers on disjoint boxes with different prefix data, or bakers composed with
    torsion that permutes boxes.

  Whether side splitting is forced for every lift of `h` in `2V` is the natural next question.
  An affirmative answer would make Theorem D cover all of `2V` and would falsify the lamp route
  there.
