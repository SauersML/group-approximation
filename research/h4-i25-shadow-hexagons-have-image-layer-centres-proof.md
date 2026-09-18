---
rg: 2
id: h4-i25-shadow-hexagons-have-image-layer-centres-proof
kind: route
title: Ejection-arc proof that I_2(5) shadow hexagons have centres in the image layer G_V·A_{Y''}
target: h4-i25-shadow-hexagons-have-image-layer-centres
requires:
  - braid-pure-single-edge-hexagons-always-have-a-centre
  - h4-i25-fibred-shadows-are-rigid-cluster-braid-groups
---

Notation is as in the target. `D_C` is the disc `D` with only the punctures of `C = {1,2,3,c}` kept, and
`φ_*` is the forgetful map from arcs and spiders in `D` to arcs and spiders in `D_C`. Here `ξ_0^C`, `δ_0^C` are the
images of `ξ_0`, `δ_0`, and `ξ_0^C` runs from `c` to `d_0`, after an isotopy in `D_C` that slides its endpoint
from the forgotten puncture 7 to `c`. The equivariance is `φ_*(hδ_0) = f(h)δ_0^C` for `h ∈ P_7`.

"Disjoint" always means disjoint representatives. Adjacency in the `A_6` layer is disjointness: this is the
dictionary of `braid-pure-single-edge-hexagons-always-have-a-centre`.

## 0. Four facts about `D_C` (`B_4`, one arc, a 3-leg spider)

**(F1) `Stab(δ_0^C) = 1` in `P_C`.** `D_C` cut along the spider `δ_0^C` is a disc with one marked point `c`. Its
mapping class group rel boundary is trivial. So a mapping class fixing `δ_0^C` is trivial.
- Consequently the spider `f(h)δ_0^C` determines `f(h)`.
- In particular `y` is in the image layer iff `φ_*(y) = D^jδ_0^C` for some `j`.

**(F2) A spider has exactly one disjoint arc from `c` to `d_0`.**
- Let `δ` be a spider from `d_1` to `1,2,3` in `D_C`. Then `D_C ∖ δ` is an open disc containing the single
  puncture `c`, and `d_0` lies on its boundary.
- In a disc with one marked point, arcs from the marked point to a fixed boundary point form one isotopy class.
- So all arcs from `c` to `d_0` disjoint from `δ` are isotopic in `D_C ∖ δ`, hence in `D_C`.
- The standard `ξ_0^C` is disjoint from `δ_0^C`, so for `δ = gδ_0^C` the disjoint arc is `gξ_0^C`.

**(F3) `D^jξ_0^C` are pairwise distinct, and `D^j ∉ P_{123}` for `j ≠ 0`.** `Stab(ξ_0^C) ∩ P_C = P_{123}`, the
pure braids of strands `1,2,3`.
- In `P_4 = P_3 ⋉ F_3`, `D = Δ²_{123}·(A_{14}A_{24}A_{34})`.
- The `F_3`-coordinate of `D^j` is `(A_{14}A_{24}A_{34})^j`, which is `≠ 1` for `j ≠ 0`.
- `P_{123}` has trivial `F_3`-coordinate. So `D^j ∈ P_{123}` iff `j = 0`.

**(F4) Push-off.** Let `S` be a punctured disc and `K ⊂ S` a closed disc with no punctures, meeting `∂S` in
an arc `J`. Let `δ` be a spider whose boundary point is not in `J`. Then `δ` is isotopic, rel `∂S` and the
punctures, to a spider disjoint from `K`.
- Take a slightly larger unpunctured disc `K' ⊃ K` with `K' ∩ ∂S = J'`, and a collar `U` of `J'` that misses `δ`.
- Choose a homeomorphism `ψ` supported in `K'` and fixing `∂K'` with `ψ(K) ⊂ U`.
- By the Alexander trick `ψ` is isotopic to the identity rel `∂K'`. So `ψ^{-1}(δ)` is isotopic to `δ`, and it
  misses `K`.

## 1. The ejected region

Put `𝒳 = {x_1,x_2,x_3}`, `Ω = Ω(𝒳)` (the `d_1`-region), `R = R(𝒳)`, and `Ω_{ij}, R_{ij}` for pairs.

**`{1,2,3} ⊂ R_{ij}` and `{1,2,3} ⊂ R`.**
- Each leg of `y_{ij}` minus `d_1` is connected and disjoint from `x_i ∪ x_j`, and its closure meets
  `∂D ∖ {d_0}`. So it lies in `Ω_{ij}`, and `1,2,3 ∈ R_{ij}`.
- Part 1 (Helly) of `braid-pure-single-edge-hexagons-always-have-a-centre` gives `R = ⋂R_{ij} ⊇ {1,2,3}`.

**`Z = D ∖ Ω` is a cellular set at `d_0`.**
- `Z` is the connected graph `⋃x_i`, which contains `7` and `d_0`, together with its bounded faces.
- It is compact and connected, and meets `∂D` only in `d_0`. Its complement `Ω` is connected.
- Hence a thin regular neighbourhood `E` of `Z` is a closed disc with `E ∩ ∂D = J`, a short arc around
  `d_0`.
- The punctures in `E` are exactly the punctures outside `R`: the endpoint 7 and the ejected ones. Since
  `{1,2,3} ⊂ R`, the only `C`-puncture that `E` can contain is `c`.

The same holds for pairs: `Z_{ij} = D ∖ Ω_{ij} ⊆ Z`, because `Ω ⊆ Ω_{ij}`. So its neighbourhood `E_{ij}` can be
chosen inside `E`, with `E_{ij} ∩ ∂D ⊂ J`.

**Thinness.** Any compact set that lies in `Ω` together with `d_1` and punctures of `R`, for example a centre,
misses `Z`. So it misses `E` once `E` is thin enough. Likewise `y_{ij}` misses a thin `E_{ij}`.

**From `Ω` back to a centre.**
- Let `δ'` be a spider in `D_C` from `d_1` to `1,2,3` that lies in `D ∖ E ⊂ Ω`.
- Perturb its legs slightly, inside the open set `Ω`, off the finitely many forgotten punctures of `R` that
  they pass through. This gives a spider `y` in `D` that is disjoint from `⋃x_i`, i.e. a centre.
- The perturbation is an isotopy in `D_C`, so `φ_*(y) = δ'`.
- Write `y = hδ_0` with `h ∈ P_7`. Such an `h` exists: by change of coordinates some `h ∈ B_7` takes `δ_0` to
  `y` leg by leg, so `h` fixes `1,2,3`, and correcting by an element of `A_{Y''}` (which realises every
  permutation of `{4,…,7}`) makes `h` pure.
- By (F1), `f(h)` is the class with `f(h)δ_0^C = δ'`.

## 2. Case A: `c ∈ R`

In `D_C`, `E` is an unpunctured disc meeting `∂D` in `J ∌ d_1`.
- For any `j`, apply (F4) to `D^jδ_0^C`. This gives `δ' ≃ D^jδ_0^C` disjoint from `E`.
- §1 turns `δ'` into a centre `y = hδ_0` with `f(h) = D^j`. This proves (1) for every `j`.

## 3. Case B: `c ∉ R`

**The ejection arc.**
- `c ∉ R = ⋂R_{ij}`, so `O ≠ ∅`.
- In `D_C`, `E` is a disc containing the one puncture `c`, and `d_0 ∈ J ⊂ ∂E`. A once-marked disc has one class
  of arc from its marked point to `d_0`. Let `ε` be that arc, in `E`.
- For `ij ∈ O`, `E_{ij} ⊂ E` also contains `c` and no other `C`-puncture. Its arc `ε_{ij}` from `c` to `d_0`
  lies in `E`, so `ε_{ij} ≃ ε`. From now on choose the representative `ε := ε_{ij}` for one fixed `ij ∈ O`.

**(P1).**
- For `ij ∈ O`, the forgotten spider `φ_*(y_{ij}) = D^{m_{ij}}δ_0^C` misses the thin `E_{ij} ⊇ ε_{ij}`.
- By (F2), `ε ≃ ε_{ij} = D^{m_{ij}}ξ_0^C`.
- By (F3), the value `m_{ij}` is determined by `ε`. So all `m_{ij}`, `ij ∈ O`, equal one value `m`.

**(1) in Case B.**
- Take `δ := φ_*(y_{ij})` for the fixed `ij ∈ O`, as a set. It misses `ε` and `J`.
- Cut `D_C` along `ε`. The result `D_C^ε` is a disc with punctures `1,2,3`, and the two sides of `ε` join `J` to
  form an arc `J^ε` of its boundary.
- `E ∖ ε` becomes a closed disc `K` in `D_C^ε` with no punctures, meeting `∂D_C^ε` in `J^ε`. (A disc cut along
  an arc from an interior point to a boundary point is a disc.)
- `δ` lies in `D_C^ε`, and its boundary point `d_1` is not in `J^ε`. By (F4) in `D_C^ε`, `δ` is isotopic rel
  `∂D_C^ε` to a spider `δ'` missing `K`.
- Isotopies of `D_C^ε` fixing its boundary glue to isotopies of `D_C` fixing `ε`. So `δ' ≃ δ = D^mδ_0^C` in
  `D_C`, and `δ' ⊂ D ∖ E`.
- §1 gives a centre `y = hδ_0` with `f(h) = D^m`.

**(P2).**
- Let `y = hδ_0` be any centre (pure, in `Ω`). By thinness it misses a thin `E`. Choose the ejection
  arc `ε` inside that `E`; it is still in the unique class.
- Then `φ_*(y) = f(h)δ_0^C` misses `ε`. So `f(h)ξ_0^C = ε = D^mξ_0^C` by (F2), and `D^{-m}f(h) ∈ P_{123}` by (F3).
- If moreover `f(h) = D^j`, then `D^{j-m} ∈ P_{123}` and so `j = m` (F3).
- The special cases `y = D^jδ_0` and `y = y_{ij}` (with `f = D^{m_{ij}}`) follow.

This proves the theorem. ∎

## 4. Consequences (a) and (b) of the target

**(a).** By `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups` (3)–(4), `ρ_V` maps the Case 1 hexagon
`x_1 y_{12} x_2 y_{23} x_3 y_{31}` to a closed walk of the `A_6` layer. Its `x`-vertices are arcs from 7 to `d_0`,
and its `y`-vertices are `ρ_V(u)δ_0` with `ρ_V(u) ∈ G_V`. The theorem applies.

**(b).**
- Let `u = ab ∈ P_7` with `a ∈ A_{X''}` and `b ∈ A_{Y''}`. Their permutations are inverse, so they lie in
  `Sym{1..6} ∩ Sym{4..7} = Sym{4,5,6}`, which is realised by `A_{Z''} ⊂ A_{X''} ∩ A_{Y''}`. Correcting by an
  element of `A_{Z''}` gives `A_{X''}A_{Y''} ∩ P_7 = P_{X''}P_{Y''}`.
- If moreover `u ∈ G_V`: `f(b) = 1`, because `b` is a pure braid on strands `4..7` and only `c` of them is in `C`.
  So `f(a) = f(u) ∈ ⟨D⟩`, i.e. `a ∈ G^X_V`. Hence `G_V ∩ P_{X''}P_{Y''} = G^X_V·P_{4567} = ρ_V(P_X)ρ_V(P_Y)`.
- So for `h ∈ G_V`, the spider `hδ_0` meets `ρ_V(p_i)A_{X''}` iff `h ∈ ρ_V(p_i)ρ_V(P_XP_Y)`.
- Hence (a) is `⋂_i ρ_V(p_iP_XP_Y) ≠ ∅`. Case 1 is the same statement in `P` (the adjacency criterion of
  `h4-case1-pure-normal-form-and-fibred-obstruction`), and `ρ_V(⋂) ⊆ ⋂ρ_V`, with equality iff the fibres of
  `ker ρ_V` can be absorbed.

So the brief's step (L_V)(b), lifting the image-layer centre to an `H_4`-adjacent vertex, is not a
consequence of any single-shadow statement. It is Case 1.

## 5. Machine check

`experiments/h4-i25-image-layer-centres-2026-09-17/imglayer.py` (log `imglayer_L111.log`). It uses curver 0.5.1
and realalg 0.3.7, with `a6.py`, `arcs.py` and `search.py` copied from the cited experiment folders.
- Cluster `C = {1,2,3,4}` (`p_c` = strand 4).
- `N`-letters `D, A_{j5}, A_{j6}`, and `F''`-letters `A_{47}, A_{57}, A_{67}`.
- Twist exponents: `m_{12} = 0`, `m_{23} = #_D(β_1)`, `m_{31} = −#_D(β_3)`.
- Per exact tuple it tests:
  - (H) `{1,2,3} ⊂ R_{ij}, R`;
  - (P1);
  - (P2) on the twist centres `D^jδ_0` (`|j| ≤ 4`) and the vertex centres `y_{ij}`;
  - (P3), an explicit image-layer centre, searched among `y_{ij}`, `D^jδ_0` and `h_{ij}gD^kδ_0`.
- `R_{ij}` and `R` come from the combinatorial placement test. Undetermined tuples are counted, not used.

**Results.**
- **Ejected case, certified** (`cert.py`, `cert.log`). This is w7-042's cabled certificate hexagon, the one with
  no twist centre `D^jδ_0` (`|j| ≤ 6`) and with `y_{31}` as a centre. Its data:
  - `m = (m_{12}, m_{23}, m_{31}) = (0, 1, 0)`;
  - `R_{12} = {1,2,3,5,6}`, `R_{23} = {1,2,3,4,6}`, `R_{31} = {1,2,3,6}` and `R = {1,2,3,6} = ⋂R_{ij}`, in strand
    labels (Helly);
  - `p_c` = strand 4 is ejected from `R`, by the pairs `12` and `31`.

  The predictions are exact:
  - both ejecting pairs have `m = 0` (P1);
  - the one vertex centre `y_{31}` has `m_{31} = 0 = m` (P2);
  - the pair `23`, with `m_{23} = 1 ≠ m`, does *not* eject `p_c`. If it did, (P1) would fail.
- **Length-1 class** (`imglayer.py 1 1 1 4`, `imglayer_L111.log`). A 1200 s cap, under machine load, stopped the
  run after the first 20 of the 180 exact tuples. On those 20:
  - all are determined;
  - all have `p_c ∈ R` (Case A);
  - an explicit image-layer centre is found every time;
  - there are 0 failures of (H), (P1), (P2) or (P3).

  At this length `y_{12}` is always a centre (see `h4-i25-shadow-centre-forms-hold-only-up-to-rotation-proof`
  §5), so Case A is expected.

Verification tier: the theorem is a direct topological proof. The machine check is a consistency check of its
sharp predictions (P1) and (P2) on the one known ejected example, plus a partial sweep. It is not an exhaustive
test.

## 6. Two flats do not form a fibred picture

`twoflat.py` (`twoflat.log`) reuses `fibred.py` from `experiments/h4-case1-fibred-quotient-2026-09-17/` and the
modularity criterion of `i25probe.py`: every pair of fibre points must collide on a wall of `𝒜_x`.
- For each of the three pairs of good `I_2(5)` flats, `ℬ_V ∪ ℬ_{V'}` has 23 walls and 8 fibre points.
- Exactly 2 fibre pairs, both of the form (new cluster point of `V`, new cluster point of `V'`), collide on
  hyperplanes that are not walls of `H_4`. All three flats together give 6 bad pairs.
- So `ℓ_x` is not modular, and the joint shadow `π_1M(ℬ_V ∪ ℬ_{V'})` is not a fibre-type braid group with two
  rigid clusters.
- The "two ejection arcs twisting around each other" picture has no braid-group realisation in this family.

A joint (multi-flat) certificate therefore has to be computed in a non-fibre-type arrangement group, or in a
non-fibred shadow.
