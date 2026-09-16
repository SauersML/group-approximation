# Labbé crossed product: covariant Kakutani towers make one scale decide exact matriciality

Swarm agent `swarm-labbe-wang-shift-crossed-produ`, 2026-09-16. Target:
`labbe-wang-shift-crossed-product-is-exactly-matricial` (row 7). Locked for 180m.

## 0. Setup and plan

- Row 7 is equivalent (reviewed torus criterion) to nonzero finite-dimensional modules of
  `𝒯_(D,Λ)(Ω_U, F_q)` at every scale `D`.
- Earlier attempt (un-labbe-torus-decider, artifact §5): constant-shape inflation gives "one scale
  suffices" for constant-shape self-similar SFTs, but it was believed not to reach `Ω_U`, because
  Labbé's `ω` has letter-dependent shapes and at torus level "which columns widen" is a non-scalar
  projection, so the inflated torus is not defined.
- Plan: inflate at the level of *covariant families* (idempotents plus commuting translations),
  where a quantum skeleton is harmless: the inflated space is an operator Kakutani--Rokhlin tower
  over the parent space, and the translations are tower maps. Over a finite field, restriction to
  the period lattice returns to tori (Theorem 1(b) of the torus criterion).

## 1. Results (all unreviewed; full proofs in the artifact)

Artifact: `research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md`.

- **Theorem A** (`morphism-towers-double-covariant-tiling-scales`, direct proof route): a 2-dimensional
  morphism `ω : L(Ω_S) -> L(Ω_T)` (Labbé's definition, `ω(L_S) ⊆ L_T`), with every letter image of shape
  `>= (2,2)`, turns a nonzero finite-dimensional covariant `D'`-family for `Ω_S` (`D' >= 1`) into one for `Ω_T` at
  scale `2D'` over the same field, of dimension `sum_a w(a) h(a) rank E'_a(0)`.
- **Theorem B** (`morphic-sft-matricial-iff-scale-one-torus-module`): for a free minimal SFT with such a
  self-morphism and a finite field `k`, `LC(Ω,k) ⋊ Z^2` is exactly matricial iff some `𝒯_(1,Λ)(Ω,k)` has a nonzero
  finite-dimensional module. Proof: TC(a) induction, iterate Theorem A to scales `2^n`, TC(b) restriction over `k`,
  DESC to all scales, TC(d).
- **Theorem C** (`labbe-ring-matricial-iff-scale-one-torus-module`): Theorem B applies to `Ω_U` with `ω^2`. By exact
  computation, `ω^2` has minimum width `2` and minimum height `2`. Import-only alternative: `ω^8`, using `M^7 > 0`
  and one `(2,2)` letter.
- **Open holes created** (both with Attempts):
  - `labbe-torus-tiling-algebra-has-scale-one-module` (routes to row 7 positive);
  - `labbe-torus-tiling-algebra-has-no-scale-one-module` (routes to row 7 negative).
- **Routes:** `labbe-matricial-via-scale-one-torus-module` and `labbe-not-matricial-via-no-scale-one-module`.

Outcome: a **reduction**. Row 7 becomes one question at scale `1` over `F_q`, involving only legal `3×3` patches
and commutation within sup-distance `2`. Row 7 itself is not decided.

## 2. Approaches and where each died

1. **Torus-level inflation of `𝒯_(D,Λ)` modules along `ω`: dies.** It needs a scalar "column width" at each torus
   column. For letter-dependent shapes, the width projection `M(0) = sum_(w(a)=2) E'_a(0)` is a non-scalar idempotent,
   so no inflated torus exists. This is the un-labbe-torus-decider firewall, and it is not refuted here.
2. **Covariant-family inflation via an operator Kakutani–Rokhlin tower: works (Theorem A).**
   - Put `W_T = ⊕_(i,j) P_ij W'`, where `P_ij` cuts out the letters whose image has cell `(i,j)`.
   - Translations are tower maps: move inside the image block, or exit to the next parent site via `u_1` / `u_2`.
   - Key Lemma 1: `M` is column-constant (it commutes with `u_2`) and `N` is row-constant (it commutes with `u_1`).
     The reason is shape consistency (M1) on legal vertical and horizontal dominoes, applied inside the commutative
     algebra `𝒞_Q`. This makes the tower maps commute.
   - Tile idempotents are diagonal on the tower, and Proposition 5 evaluates them through `ev_Q` on
     `Q = [0,2D']^2`.
   - (Q3) at scale `2D'` reduces to legality of `ω` applied to legal `Q`-patterns. That uses (M2)/(M3) and
     `ω(L) ⊆ L`.
3. **Shapes of `ω` itself: insufficient.** `ω` has letters of shape `(1,1)` (tiles `0`, `1`), so it does not
   double the scale. `ω^2` has widths `2..3` and heights `2..3` (Fibonacci growth, script check 4). So Theorem A is
   applied to `ω^2`.
4. **Deciding the scale-1 question: not attempted computationally.**
   - Reviewed firewalls force any module to be contextual, with both axis periods `>= 6`.
   - A search over tori with `>= 36` sites and `19` idempotents per site, over noncommutative matrix algebras, is far
     beyond single-threaded budgets without more structure. Recorded in the hole's Attempts.

5. **Exact sanity test of the tower bookkeeping: passes.** Artifact §7.1, `tower_sanity.py`, 316 s.
   - Setting: a toy SFT with letter-dependent shapes and a genuinely noncommutative covariant 1-family over
     `F_1000003`, with dimension 36.
   - The tower has dimension 240. Lemma 1, Lemma 2 and (Q1) hold, (Q2) holds on `B_4` and domino (Q3) at scale 2.
   - Proposition 5 matches an independent classical layout of `ω(σ)` for all `z ∈ [0,4]^2`.
   - The child family is noncommutative.
   - Negative control: widths not column-constant break Lemma 1 and Lemma 2.

## 3. Weakest steps (for the referee)

- Proposition 5 induction and support bookkeeping. This covers the Lemma 3 support bounds, the containment
  `K + e_1 ⊆ Q`, and the vanishing of cross terms, which uses that all evaluated operators lie in the commutative
  `𝒞_Q`.
- The claim that `ω` is a 2-dimensional morphism on `L(Ω_U)` with `ω(L) ⊆ L`.
  - Labbé states it (verbatim quotes in artifact §9).
  - The script independently checks all 19 images as Wang patches, and width/height consistency on all 79 vertical
    and 46 horizontal colour-matching dominoes with matching seams.
  - The step "blockwise image of a valid tiling is valid" uses only nearest-neighbour matching.

## 4. Literature consulted

- Labbé, arXiv:1802.03265. TeX e-print fetched 2026-09-16; definition of `d`-dimensional morphism l.814–823,
  `ω(L_X) ⊆ L_Y` l.985.
- Four web searches (2026-09-16) for 2024–2026 resolutions: quantum Wang tilings, LEF full groups of `Z^2`-subshifts,
  subshift/Steinberg algebras, Labbé tiles. Title-only and unverified: arXiv 2302.04503, 2106.09145, 2104.07111,
  2211.15249, 2412.15951, 2607.06733, 2012.03892, 2312.03652, 2606.24693. No resolution of row 7 found.
- A refresh failed: search budget exhausted, arXiv API HTTP 429 and tunnel reset.

## 5. Files

- `research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md`
- `experiments/labbe-covariant-tower-inflation-2026-09-16/omega_shapes.py` and `output.txt` (reproduces byte for
  byte, 0.46 s)
- `experiments/labbe-covariant-tower-inflation-2026-09-16/tower_sanity.py` and `tower_sanity_output.txt` (316 s)
- 10 research nodes: the 5 claims and 5 routes listed in §1.
