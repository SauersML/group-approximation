---
rg: 2
id: h4-i25-shadow-centre-forms-hold-only-up-to-rotation-proof
kind: route
title: Certificate that the base-edge centre forms fail in the I_2(5) shadow class, and the evidence that they hold up to rotation
target: h4-i25-shadow-centre-forms-hold-only-up-to-rotation
requires:
  - h4-i25-fibred-shadows-are-rigid-cluster-braid-groups
---

Code and logs: `experiments/h4-shadow-a3-reduction-2026-09-17/`. Runs use curver 0.5.1 and realalg 0.3.7 with
`PYTHONPATH=.:<curver>:<realalg>`.

## 1. Arc models

**`A_6` model** (`B_7`, curver `load(0,10)`).
- The punctures are `e_1, 1, …, 7, e_0, ∞`, and `σ_i` is curver `s_i`.
- `A_{X''}`, with `X'' = {s_1..s_5}`, is the stabiliser of the arc `ξ_0 = s_7` from strand 7 to `e_0`.
- `A_{Y''}`, with `Y'' = {s_4,s_5,s_6}`, is the stabiliser of the spider `δ_0` with legs from `e_1` to 1, 2, 3
  (curver `s_0`, `s_1(s_0)`, `s_2s_1(s_0)`).
- Two cosets `gA_{X''}` and `hA_{Y''}` meet if and only if `g ξ_0` and `h δ_0` are disjoint, that is, every leg
  has geometric intersection 0 with the arc. This is the standard curve-system description of cosets of
  parabolic subgroups of braid groups.

**`A_3` model** (`B_4` on `q, a, b, t`, curver `load(0,7)`).
- `ξ_0` is the arc from `t` to `d_0`, and `δ_0` is the arc from `d_1` to `q`.
- `F = ⟨A_{24}, A_{34}⟩` and `N = ⟨A_{12}, A_{13}⟩`, where `A_{ij} = σ_{j-1}⋯σ_{i+1}σ_i^2σ_{i+1}^{-1}⋯σ_{j-1}^{-1}`.

**Exact tuples.**
- Setting `α_3 = (α_1α_2)^{-1}` and `β_2 = β_1^{-1}β_3^{-1}` leaves one condition,
  `β_3^{-1}(α_1α_2)β_3 = α_1β_1α_2β_1^{-1}`, written (*).
- (*) is solved by hashing the images of the full curver arc chain and then confirming mapping-class
  equality (`tuples.py`, `a6.py`, `findb3.py`).

## 2. The cabling embedding `ι : P_4 → P_7`

**Definition.**
- Cable strand `q` into strands 1, 2, 3, and send `a ↦ 4` (`p_c`), `b ↦ 5` (`p_a`), `t ↦ 7`. Strand 6 (`p_b`) is
  the extra fibre point, carried along trivially.
- Correct by `Δ_{123}^{2k(g)}`, where `k(g)` is the `A_{12}`-exponent of `g` in the abelianisation. Thus
  `ι(g) = cable(g)·Δ_{123}^{2k(g)}`.
- On generators, with `D = Δ_C^2 = (σ_1σ_2σ_3)^4` and `τ = σ_6σ_5σ_6^{-1}`:
  - `ι(A_{12}) = D`;
  - `ι(A_{13}) = σ_4 D Δ_{123}^{-2} σ_4^{-1}`;
  - `ι(A_{24}) = τσ_4^2τ^{-1}`;
  - `ι(A_{34}) = τ^2`.

**Properties.**
- **(a)** `ι(F) ⊂ F''`. `F'' = ⟨A_{47}, A_{57}, A_{67}⟩` is the group of pushes of strand 7 among 4, 5, 6.
  `ι(A_{24})` and `ι(A_{34})` are pair twists of `{4,7}` and `{5,7}` in that group.
- **(b)** `ι(N) ⊂ N_V`.
  - `D` restricts to `Δ_C^2` on `C = {1,2,3,4}` and is trivial on `456`.
  - `ι(A_{13})` pushes strand 5 around the cable `{1,2,3}` only. It is trivial after forgetting `{1,2,3}` or
    `7`, and it is trivial on `C` because of the `Δ_{123}^{-2}` correction.
  - Both lie in `N'' = ker(ρ_{Y''}|P_{X''})`, since they fix strand 7 and die when `1, 2, 3` are forgotten.
- **(c)** `ι` preserves and reflects adjacency.
  - **Reflects.** Forget strands 2, 3 and 6, keeping 1 as `q`, and identify `e_1` with `d_1`. This maps
    `ι(g)` to `g`, because the correction dies. It maps the `A_6` arc and spider to the `A_3` arcs, and
    disjointness survives forgetting punctures.
  - **Preserves.**
    - `Δ_{123}^{2k}` fixes `ξ_0`. It moves `δ_0` only inside a neighbourhood of `δ_0 ∪ c_{123}`, the cable disc
      with its leg band. Here `Δ_{123}^2 = T_{c_{123}}` is a point-push of `e_1` around the cable disc,
      composed with a twist fixing `δ_0`.
    - So `ι(h)δ_0` lies in the cabled neighbourhood of `hδ_0`, and `ι(g)ξ_0 = cable(g)ξ_0`.
    - Hence the two are disjoint if `hδ_0` and `gξ_0` are.

  In every certificate below, the `A_6` numbers are exactly 3 times the `A_3` numbers, one copy for each
  leg.
- **(d)** `ι` takes a normal-form tuple to a normal-form tuple of `𝓗_V`, and `ι(A_{12}^j) = D^j`. So the forms
  (Y2) and (TW) correspond.

## 3. Certificate for part (1) of the claim (`verify.py`, log `verify.log`)

The tuple is `α_1 = A_{24}`, `α_2 = A_{34}`, `β_1 = A_{12}A_{13}`, `β_3 = A_{12}A_{13}^{-1}A_{12}^{-1}` (found by
`findb3.py`), and in `A_6` its `ι`-image. Output of both models:

| check | `A_3` | `A_6 = ι(A_3)` |
|---|---|---|
| `α_1β_1α_2β_2α_3β_3 = 1`, `∏α = 1`, `∏β = 1` | True, True, True | True, True, True |
| `i` along the 6-cycle `x_1y_1x_2y_2x_3y_3` | `0,0,0,0,0,0` | `0,0,0,0,0,0` |
| `x_i` pairwise distinct, `y_i` pairwise distinct | True, True | True, True |
| `i(y_1,x_3), i(y_2,x_1), i(y_3,x_2)` | `2, 2, 0` | `6, 6, 0` |
| `i(D^j y_1, x_3)`, `j = −8..8` | `50,44,…,8,2,4,…,46` | `150,132,…,24,6,12,…,138` |

**Every `j ∈ ℤ` is excluded.**
- `D` (respectively `A_{12}`) is the Dehn twist `T_c` about the curve `c` around `C` (respectively
  around `{q,a}`).
- The twist inequality `| i(T_c^j δ, ξ) − |j|·K | ≤ i(δ, ξ)` holds with `K = Σ_legs i(δ,c)·i(c,ξ)`
  (Farb–Margalit Prop. 3.4, whose bigon-criterion proof applies verbatim to arcs).
- With `v_j = i(D^j y_1, x_3)` in `A_6`:
  - `v_8 = 138` gives `8K ∈ [132, 144]`, and `v_{−8} = 150` gives `8K ∈ [144, 156]`. So `K = 18`.
  - Hence `v_j ≥ 18|j| − 6 > 0` for `j ≠ 0`, and `v_0 = 6`.
- In `A_3` the same reasoning gives `K = 6` and `v_j ≥ 6|j| − 2`.

**Conclusion.**
- No `D^j A_{Y''}` is a centre, `y_2` is not adjacent to `x_1`, and odd powers of `s_4` have no `ρ_V`-image in
  the single-edge layer.
- `y_3` has intersection 0 with all of `x_1, x_2, x_3`, so it is a centre.

## 4. Rotation (part (2))

- For the hexagon read from the edge `(x_2, y_1)` in the order `x_2 y_1 x_1 y_3 x_3 y_2`, the transport is
  `α_1` with `α_1^{-1}x_2 = A_X`. Also `α_1^{-1}y_1 = A_Y`, because `α_1 ∈ F ⊂ P_Y`.
- The rotated normal form therefore has `y_2' = α_1^{-1}y_3` and `x_1' = α_1^{-1}x_2`.
- Its (Y2) says `i(α_1^{-1}y_3, α_1^{-1}x_2) = 0`, i.e. `y_3 ~ x_2`. Since `y_3 ~ x_1, x_3` along the cycle, this is
  the same as "`y_3` is a centre".

In general, "`y_k` is a centre" is (Y2) for one of the two orientations at a base edge next to it.

## 5. Evidence for (R)

All runs are certified: every adjacency is an exact curver intersection number, and every tuple is confirmed
by mapping-class equality.
- `tuples.py 2 2 6` (`tuples_L2.log`): 224 nondegenerate exact `A_3` tuples, 0 failing (Y2) or (TW) at
  `(x_1, y_1)`.
  - 32 have `y_2 ≁ x_1` with twist `j = 0` (`y_1` itself is a centre).
  - 32 have `y_2 ≁ x_1` with twist `j = −1`.
  - The remaining 160 satisfy (Y2).
- `a6.py 1 1 1 4` (`a6_L1.log`): the exact `A_6` tuples of `𝓗_V` at letter length 1, with `N`-letters `D`,
  `A_{j5}`, `A_{j6}`. There are 180 of them, and all satisfy (TW) for every `|j| ≤ 4`. 132 of them also satisfy
  (Y2). None fails the base-edge forms, since at this length `y_1` is always a centre.
- `spec.py` (`spec_L2a.log`, `spec_L2b.log`) lists the closing `A_3` hexagons with `|α_1|, |α_2|, |β_1| ≤ 2` that
  fail both base-edge forms. Closing is certified by the placement test, and `β_3` is then recovered exactly
  by `findb3`.
- `rot.py 6 5` (`rot.log`: "hexagons 32 with no rotation-invariant form 0") shows that each of the 32 has
  `y_3` as a centre. Transported twists
  `(α_1β_1)A_{12}^{-1}A_Y` and `(α_1β_1α_2)A_{12}^{-1}A_Y` are centres too.

## 6. The pair lemma and the dead cabling route (part (3))

- `pairlemma.py` (`pairlemma_s1.log`, `pairlemma_s2.log`) checks random families of 32 and 35 arcs `t → d_0`:
  - it tests 937 + 973 triples with a common pair-outer puncture;
  - 0 violate the lemma, and 163 are undetermined (the placement test was inconclusive).
- **Consequence.**
  - For a pure `A_3` hexagon, `q` lies in the `d_1`-region of each `x_i ∪ x_j`, because the pure vertex
    `y_{ij}` is disjoint from both.
  - So, under the lemma, `q` lies in the `d_1`-region of `x_1 ∪ x_2 ∪ x_3`, and a centre exists.
  - By 2(c) its `ι`-image is a centre of the image hexagon.
- **Dead route.** Cabling `A_3` hexagons through `ι` into `𝓗_V` cannot yield a centreless hexagon (conditional
  on the lemma).
- **Status.** The lemma is open. It is the `A_3` case of upward flagness at a single puncture, and a proof would
  be a disc-region (innermost bigon) argument.

## 7. Verdict and next step

- **The brief's literal question has answer NO**, proposed-established by the certificate of §3. The answer is
  about the base-point dependence of the forms, not about the existence of centres.
- **(R) is open**, with the evidence of §5.
- **The single `I_2(5)` flat is exhausted as a source of counterexamples**, conditional on the pair lemma.
- **Next step.** Formulate the Case 1 target as (R), or as "some `y_k` is a centre". Then test it on
  multi-flat shadows (two `I_2(5)` flats at once, where `N_V ∩ N_{V'}` constrains `β` further) or on non-fibred
  shadows, which are the only places a label-5 obstruction can appear.
