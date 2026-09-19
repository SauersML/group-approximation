---
rg: 2
id: h4-w15-coincidence-lifts-to-f45-x-flats-block-local-lifts
kind: claim
title: In H_4 the w15 Case 1 coincidence [u,a] = [v,b] already holds in F_45 for Brieskorn lifts, but the three rank-2 X-flats lie in 9, 10 and 5 collision walls, so A_X has no local lifts to the completed arrangement and every lift of Case 1 data depends on the base point
distinct_from:
  h4-ker-rho-x-is-f45-mod-transported-collision-twists: that presents ker ρ_X as F_45/R; this computes the braid monodromy of explicit loops in the completed arrangement and asks which identities of P hold before the quotient by R.
  h4-case1-vertex-centres-fail-by-orthogonal-parabolics: that certifies the coincidence [u,a] = [v,b] in P; this lifts it to the 46-strand braid group of the fibre and shows that it holds exactly in F_45.
---

**Setting.** As in `h4-ker-rho-x-is-f45-mod-transported-collision-twists`.
- `𝒜°` is `𝒜` plus the 106 collision walls `D_E`, with `M° = V ∖ ⋃𝒜°` and `P° = π_1(M°) = F_45 ⋊ B°`.
  `B° = π_1` of `V/L_X` minus the 15 X-planes and the 106 D-planes.
- The fibre of `M° → M°/L_X` over `b` is `ℂ` minus the 45 fibre punctures `y_h(b) = −h(b)/h(ℓ)`.
  Tracking the punctures and the moving point `m` gives `μ̂ : P° → PB_46`. On `F_45` it is the point-pushing
  embedding, which is injective.
- A word `g` in `s_1^{±1}, …, s_4^{±1}` has a *Brieskorn lift* `L_{x,y}(g) ∈ π_1^{orb}(M°/W)` at a base point
  `(x, y)` of the fundamental chamber.
  - For `s_i`, the real part runs linearly from `x` to `s_i x`. The imaginary part is `ε sin(πt) y`.
  - For `s_i^{-1}`, the path is the `s_i`-image of the reversed `s_i` path, with imaginary part `ε sin(πt) s_i y`.
  - In `P` the lift does not depend on `(x, y)`. In `P°` it depends on which side of each real D-wall `x` and `y`
    lie.

**Theorem.**
1. **(Rank-2 X-flats lie in collision walls.)**
   - A flat `L_{1j}` lies in no D-wall.
   - The X-flats `L_{23}` (type `A_2`), `L_{24}` (type `A_1×A_1`) and `L_{34}` (type `I_2(5)`) lie in 9, 10 and 5
     D-walls respectively.
   - At a generic point of `L_{ij}` with `i, j ∈ X`, the local group of the base is `F_{n−1} × ℤ`, where
     `n = m_{ij} + k_{ij}` is 12, 12 or 10. This group is a retract of `B°`.
   - Inside it the local meridians of `H_{α_i}` and `H_{α_j}` generate a free group of rank 2. In particular the
     local lifts of `s_2^2` and `s_4^2` do not commute in `B°`, even though `A_{s_2} ⊥ A_{s_4}` in `A_X`.
2. **(Brieskorn lifts are not homomorphic on `A_X`.)**
   - At the generic base point, every rank-2 relation except `(1,3)` fails in `P°`, and also after `m` is forgotten.
   - Near `L_{1j}` the relations `(1,j)` hold. Near `L_{23}`, `L_{24}` and `L_{34}` the braid relation
     `Δ_{ij} = Δ_{ji}` fails.
   - Near the rank-3 flat `L_{124}`, which carries the orthogonality `A_{s_4} ⊥ A_{s_1s_2}` behind w15,
     `[s_4^2, a] = 1` fails.
   - All these inequalities are certified.
3. **(The w15 coincidence is exact in `F_45`.)**
   - At `x_0 = B^{-1}(3, .1, .2, 5)` and `y_0 = B^{-1}(1, 1.3, .7, 1.1)`, the Brieskorn lifts satisfy
     `[ũ, ã] = [ṽ, b̃] = k̃` in `P°`. Here `k̃ ≠ 1`, and `ã`, `b̃` and `k̃` are point-pushing, so they lie in `F_45`.
   - Each identity of w15's derivation also holds exactly: `[c̃,ã] = 1`, `[d̃,b̃] = 1`,
     `[w̃, b̃^{-1}ã] = 1` and `[w̃,ã] = [w̃,b̃]`.
   - The same holds at 7 of 10 base points within 10% of `(x_0, y_0)` (the first is `(x_0, y_0)` itself), in each
     case for all three `ε ∈ {.05, .37, 1}`.
   - The coincidence fails at 24 of 24 random chamber base points, and `[c̃, ã] = 1` fails at 22 of them.
   - In `A_4` and `B_4` all of this holds at every base point tested. Those arrangements have no D-walls, so their
     lifts are canonical.
4. **(The disc orbit is thin.)** The group `μ(B°) ⊂ PB_45` has infinite index. Its image in
   `H_1(PB_45) = ℤ^{990}` has rank at most 121.

**What it does to Case 1.**
- The w16 dichotomy asked whether a coincidence holds in `F_45` or only modulo `R`. For H_4 that question has to be
  read existentially: do *some* lifts satisfy it exactly? Part 2 shows that no choice of lifts is canonical, and
  part 1 is the reason.
- Read that way, the only known H_4 coincidence without a vertex centre, the w15 tuple, holds in `F_45` (part 3).
  So it is not an only-mod-`R` coincidence, and the w14 searches found no other H_4 candidate.
- The brief's next step is therefore the transport of the type-A arc Helly argument. Part 4 shows that the
  transport is not verbatim.
  - In type A every disc around `m` and the three F-punctures is a y-vertex.
  - In H_4 the y-vertices are the orbit `𝒟° = μ̂(P°)·Δ_F`, which is cut out by the invariants `ι`.
- What remains is **(Q1)**: the centre disc that the type-A Z/2 Helly lemma produces from three discs of `𝒟°` lies
  in `𝒟°`.
  - (Q1), together with an exact lift of the triple (which part 3 supplies for w15), gives (H″) for that triple.
  - A counterexample to (H″) whose coincidence lifts exactly must violate (Q1). It needs a hull disc that separates an F-puncture from the arcs of
    all but one pair.

**Files.** `experiments/h4-monodromy-2026-09-19/`
- `mono.py` is the closed-form braid monodromy.
- `test1.py`, `test2.py`, `test4.py`, `test5.py` and `test7.py` produce `tests.log`.
- `test8.py` produces `random-base.log`, `test9.py` produces `default-base.log`, and `dwalls.py` produces
  `dwalls.log`.

**Status.**
- Part 1 (all but the D-wall counts) and part 4 are proved.
- The D-wall counts in part 1 are computed in floating point, and they reproduce w16's exact totals of 106 walls and
  510 pairs.
- Parts 2 and 3 are computed from floating-point crossing words that are stable under changes of scale and `ε`.
  - Inequalities are certified by the faithful Artin action.
  - Equalities are randomized tests in three random `SL_2(𝔽_p)` images, with `p = 2^61 − 1`.
- (Q1) is open.
