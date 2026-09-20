---
rg: 2
id: ct-z-kourovka-21-74a-reduces-to-base-coarse-structure
kind: claim
title: "Kourovka 21.74(a), all slopes: for any g in CT(Z) whose S-adic base splits into a finite-order part and finitely many clopen components that no power of g decomposes, the question is decidable from that splitting; mixed-sign slopes do not obstruct this (Conway's amusical permutation, a full 3-shift, is decided: NO), so what remains for rank two is computing the base's clopen sets invariant under powers of g"
distinct_from:
  ct-p-z-neutral-primes-kourovka-21-74a-is-decidable: that decides the positive ray, where the splitting is supplied by Gilabert Vio's decomposition; this proves the fibre half for every g in CT(Z), with any slopes, given the splitting.
  ct-z-21-74a-reductions-must-move-coarse-components: that shows YES depends only on the coarse action; this shows the fibre part of the coarse action is always computable, so only the base's invariant clopen structure can carry hardness.
  conway-amusical-permutation-is-the-full-three-shift: that conjugates Conway's map to the full 3-shift; this uses it to decide 21.74(a) for that map.
---

**ESTABLISHED** (lane proof, bh-2174-rank2, 2026-09-19; **referee PASS**, bh-ref-e,
`ct-z-21-74a-base-reduction-review` at 38687f1d6c, clarity repairs applied; the review also checks
item 2 of the Conway node, which the Corollary uses). No priority claimed.
Kourovka 21.74(a) (S. Kohl) stays **OPEN** for rank-two and mixed-sign slopes. This node proves
that the whole difficulty there is in the base.

## Setting

- `g ∈ CT(Z)`; `S` is the set of primes dividing a modulus of `g`, `2 ∈ S`. The base is
  `X = Z_S = ∏_{p∈S} Z_p`, and `ĝ` acts on `Ẑ = X × Φ`, `Φ = ∏_{ℓ∉S} Z_ℓ`, as a skew product whose
  fibre map at `x` is the formula `y ↦ λy + β` of `g`'s piece at `x`
  (`ct-z-residue-partition-certificates-live-on-s-adic-coordinates`, Theorem 1). Here `λ ∈ Q_{>0}`
  is an `S`-unit, so every fibre map is a unit-slope rational affine map on every `Z_ℓ`.
- Residue classes are boxes (base box) × (product of balls), and permuted partitions of `Z` into
  classes are permuted box partitions of `Ẑ`.
- **Splitting (Σ).** Clopen sets `U, R_1, …, R_s` partitioning `X`, with:
  - `U` is `g`-invariant and `g^N` has identity formulas on `U` for some `N ≥ 1`;
  - `g` permutes the `R_j`, and for some `M` every `R_j` is `g^M`-invariant;
  - (*indecomposable*) for every `t ≥ 1`, the only `g^(Mt)`-invariant clopen subsets of `R_j` are
    `∅` and `R_j`.
  All sets are given as explicit finite unions of boxes.

For the positive ray, Σ is the decomposition `U ⊔ R_1 ⊔ … ⊔ R_s` of the cone node (Lemma A), after
neutral deep digits are moved to the fibre as in `ct-p-z-positive-ray-kourovka-21-74a-is-decidable`.

## Theorem R

There is an algorithm that, given `g ∈ CT(Z)` and a splitting Σ, decides whether `g` permutes a
nontrivial partition of `Z` into residue classes.

*Proof.* Everything is the proof of `ct-p-z-neutral-primes-kourovka-21-74a-is-decidable`, with Σ
in place of the tree decomposition; only three points need new arguments.
- **Lemmas B.1 and B.3** (V node) use only indecomposability and the skew product: every part
  meeting `R_j × Φ` has base `⊇ R_j`, and every holonomy `(β^(N)_(x′))^(−1) β^(N)_x`,
  `x, x′ ∈ R_j`, fixes every fibre box of such a part. There are finitely many base candidates,
  since a box containing a nonempty open `R_j` has bounded radii at every prime.
- **(1) Every component carries a nontrivial holonomy, found by enumeration.** Suppose all
  holonomies over `R_j` are trivial. Then `g^M` has one formula `y ↦ λy + t` on all of `R_j`, and
  maps `R_j` onto itself. A canonical map of slope `λ` multiplies Haar measure by `λ^(−1)`, so
  `λ = 1`, and `t ∈ Z` because slope-one canonical maps are integer translations. `t ≠ 0`, since
  otherwise every clopen subset of `R_j` would be `g^M`-invariant. Pick an `S`-smooth `m` for which
  `R_j` meets two cosets of `mZ_S`. Then `g^(Mm)` is translation by `mt` on `R_j`, so it preserves
  `R_j ∩ (a + mZ_S)`, a proper nonempty clopen subset. This contradicts indecomposability. So a
  nontrivial holonomy exists, and enumerating `N` and the finitely many formulas of `g^N` on `R_j`
  finds one.
- **(2) Bounds.** If the holonomy found is a translation `y ↦ y + τ`, `τ ≠ 0`, every `ℓ`-ball of a
  fibre box over `R_j` has depth `≤ v_ℓ(τ)`, which is `≥ 1` for finitely many `ℓ`. If it is
  hyperbolic, `ψ_j` with fixed point `q_j` and slope `λ_j ≠ 1`, run the degeneracy test of Lemma 1.2
  there, with `q_i` defined as the fixed point of `ψ_i` instead of an attractor's formula. The proof
  of ⇐ is unchanged. For ⇒, a degenerate center is fixed by the hyperbolic `ψ_i`, so it is `q_i`.
  Then either a moving holonomy gives the two-center bound, or the component is degenerate and D1–D3
  hold. If some component of a `σ`-cycle yields a nonzero translation holonomy, the whole cycle is
  nondegenerate: degeneracy is a cycle property (Lemma 1.1), and a nonzero translation fixes no
  point. So the centers `q_i` are needed only for cycles all of whose found holonomies are
  hyperbolic (clarity repair, bh-ref-e).
- **(3) Radial truncation and search.** Lemmas 2–3 used only conditions 1–3, B.1, B.3 and
  coordinatewise unit-slope rational affine fibre maps, so they hold verbatim. In Step 3, `E_ℓ`
  also includes the translation bounds `v_ℓ(τ)` (clarity repair, bh-ref-e). The finite search and
  its ⇐ direction are unchanged, with `ĝ^N = id` on `U × Φ` by the first bullet of Σ. ∎

## Corollary (Conway's amusical permutation)

Let `α(n) = 3n/2` (`n` even), `(3n+1)/4` (`n ≡ 1 mod 4`), `(3n−1)/4` (`n ≡ 3 mod 4`). **`α`
permutes no nontrivial partition of `Z` into residue classes.** It has mixed-sign slopes on
every piece: each one expands `Z_2` and contracts `Z_3`.

*Proof.*
- **Base.** `α ∈ CT_{3}(Z)` with `X = Z_2 × Z_3`, and `α` is conjugate there to the two-sided full
  3-shift (`conway-amusical-permutation-is-the-full-three-shift`, item 2; lane proof). Every power of
  a full shift is topologically mixing, so no power fixes a nontrivial clopen set. So
  Σ = (`U = ∅`, `R_1 = X`), and every part of a permuted partition has base `X` (Lemma B.1).
- **Fibre.** Take `x ∈ 1(4)` and `x′ ∈ 3(4)`, with formulas `F_1(y) = (3y+1)/4` and
  `F_2(y) = (3y−1)/4`. The `N = 1` holonomy `F_2^(−1) F_1` is `y ↦ y + 2/3`, and
  `v_ℓ(2/3) = 0` for every `ℓ ≥ 5`. So every fibre ball is all of `Z_ℓ` (bound (2)).
- So every part is all of `Ẑ`. ∎

The same two-line argument decides any `g` whose base is one mixing component: compute one
nontrivial holonomy, bound the fibre, and search a finite set.

## What blocks rank two

- **Not the saddles.** A natural candidate obstruction, one class on which two primes
  expand and contract at once, is harmless in itself. Conway's `α` has it on every piece, and the
  Corollary decides it.
- **The block is the splitting Σ.** Theorem R turns 21.74(a) into one base question: compute the
  Boolean algebra of clopen subsets of `X` fixed by some power of `g`, outside the finite-order
  part, and check that it is finite. Σ can fail in two ways:
  1. **Infinite coarse algebra.** Infinitely many clopen sets are invariant under powers of `g`
     away from its finite-order part, e.g. odometer-like isometric directions. On the positive ray
     this is what neutral coordinates cause, and moving them to the fibre repairs Σ. In rank two
     a prime can be isometric on one component and not on another; whether the same move always
     works component by component is open.
  2. **Finite but not uniformly computable.** The components exist, but finding them is as hard as
     orbit questions of 3x+1 type. Kohl's `G_T` has orbit structure equivalent to 3x+1 finiteness
     (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`).
- **Consequence for undecidability attempts.** A reduction for 21.74(a)
  (`ct-z-21-74a-reductions-must-move-coarse-components`) must make the base's invariant clopen
  algebra depend on halting, on rank-two or mixed-sign elements. Fibre coding and neutral primes on
  a positive ray are ruled out, and saddle dynamics alone is not enough (the Corollary).

## Lesson for general BH

**Coordinate questions in arithmetic hosts split cleanly into base and fibre, and the fibre is
tame whenever the base splits.** Holonomy (Lemma B.3) forces every hidden coordinate to bounded depth or to radial
structure around one rational center, which truncates. Hyperbolicity, even full-shift mixing, is
no obstruction; in the Corollary it made the answer easier. What can be hard is only the invariant clopen
structure of the base action: a "which clopen sets survive under powers" question, which is where
3x+1-type orbit questions live.
