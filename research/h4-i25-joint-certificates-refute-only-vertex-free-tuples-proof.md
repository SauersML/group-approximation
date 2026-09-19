---
rg: 2
id: h4-i25-joint-certificates-refute-only-vertex-free-tuples-proof
kind: route
title: Coset bookkeeping at the three hexagon vertices, the semidirect fibre in each shadow, and an exact Burau-hashed Garside search give the vertex reduction of joint certificates
target: h4-i25-joint-certificates-refute-only-vertex-free-tuples
requires:
  - h4-i25-two-flat-joint-centres-reduce-to-pencil-loops
  - h4-case1-pure-normal-form-and-fibred-obstruction
  - h4-i25-shadow-hexagons-have-image-layer-centres
artifacts:
  - experiments/h4-two-flat-pencil-matching-2026-09-17/vsearch.py
  - experiments/h4-two-flat-pencil-matching-2026-09-17/nsearch.py
  - experiments/h4-two-flat-pencil-matching-2026-09-17/purecent.py
  - experiments/h4-two-flat-pencil-matching-2026-09-17/joint.py
  - experiments/h4-two-flat-pencil-matching-2026-09-17/ejection.py
  - experiments/h4-two-flat-pencil-matching-2026-09-17/vcent.py
---

Notation as in the claim. Throughout, `P_Y = F ⋊ P_Z` with `P_Z ≤ P_X`, so `P_YP_X = F·P_X` and
`P_XP_Y = P_X·F`. Also `u ∈ gP_XP_Y ⟺ g^{-1}u ∈ P_XP_Y ⟺ u^{-1}g ∈ P_YP_X`
(`h4-case1-pure-normal-form-and-fibred-obstruction`).

## 1. Vertex criterion (V)

- **`u_01 = 1`.**
  - `i = 1` is trivial, and `i = 2` holds because `α_1^{-1} ∈ F ⊂ P_Y`.
  - `i = 3` asks for `g_3 = α_1β_1α_2 ∈ P_YP_X`. Since `α_1 ∈ P_Y` and `β_1 ∈ P_X`, this holds iff
    `β_1α_2β_1^{-1} = c_01 ∈ P_YP_X`.
- **`u_20 = β_3^{-1}`.**
  - `i = 1`: `β_3^{-1} ∈ P_X`.
  - `i = 2`: `u^{-1}g_2 = β_3α_1 ∈ P_YP_X` iff `c_20 = β_3α_1β_3^{-1} ∈ P_YP_X`.
  - `i = 3`: `u^{-1}g_3 = β_3α_1β_1α_2 = β_3(α_1β_1α_2β_1^{-1})β_1 = (α_1α_2)β_3β_1 ∈ P_YP_X`, by `(*)`.
- **`u_12 = α_1β_1`.**
  - `i = 2`: `g_2^{-1}u = β_1 ∈ P_X`.
  - `i = 3`: `g_3^{-1}u = α_2^{-1} ∈ P_Y`.
  - `i = 1`: `u = β_1c_12 ∈ P_XP_Y` iff `c_12 ∈ P_XP_Y`.
- **When `c_P ∈ F ⊂ P_Y`.** `u_12A_Y = β_1c_12A_Y = β_1A_Y` and `u_20 = b_20`, so `u_PA_Y = b_PA_Y` in every case.

## 2. Shadow form

In `G_a = F_6 ⋊ B_a` we have `ρ_a(F) = F^{(a)}_Y ≤ F_6` and `ρ_a(P_X) = B_a`, so every `ρ_a(c_P)` is a
conjugate of an element of `F_6` and lies in the normal subgroup `F_6`. Uniqueness of the semidirect
decomposition gives `F_6 ∩ F^{(a)}_Y B_a = F^{(a)}_Y`.

By w10's `(★)`, `c ∈ B_a` lies in `Sol_a` iff `ρ(α_1)` and `ρ(c_01)` lie in `cF_Yc^{-1}` (write `ρ = ρ_a`,
`F_Y = F^{(a)}_Y`). Check the three `b_P`:
- **`b_01 = 1`.** The conditions are `ρ(α_1) ∈ F_Y`, which always holds, and `ρ(c_01) ∈ F_Y`.
- **`b_12 = ρ(β_1)`.** Conjugating by `ρ(β_1)^{-1}`, the conditions become `ρ(c_12) ∈ F_Y` and
  `ρ(α_2) ∈ F_Y`, which always holds.
- **`b_20 = ρ(β_3)^{-1}`.** Conjugating by `ρ(β_3)`, the conditions become `ρ(c_20) ∈ F_Y` and
  `ρ(β_3c_01β_3^{-1}) ∈ F_Y`. By `(*)`, `c_01 = α_1^{-1}β_3^{-1}α_1α_2β_3`, so
  `β_3c_01β_3^{-1} = c_20^{-1}·(α_1α_2)`. The second condition therefore follows from the first.

So in each case `ρ_a(b_P) ∈ Sol_a` iff `ρ_a(c_P) ∈ F^{(a)}_Y`.

## 3. Reduction (R)

Suppose `ρ_a(c_P) ∈ F^{(a)}_Y` for every `V_a ∈ 𝒱`. Then, by §2, the single element `b_P ∈ P_X` has
`ρ_a(b_P) ∈ Sol_a` for all of them. That is the definition of a joint centre in w10's (J). In particular
`ι_a(ρ_a(b_P)) = ρ_{ab}(b_P) = ι_b(ρ_b(b_P))` lies in `ι_a(Sol_a) ∩ ι_b(Sol_b)`, so the Corollary's
conditions (i) and (ii) hold with `c = ρ_a(b_P)` and `c' = ρ_b(b_P)`.

Contrapositive: a `𝒱`-certificate needs every `P` to fail in some `V_a ∈ 𝒱`. By §1, `c_P ∈ F` gives
`ρ_a(c_P) ∈ F^{(a)}_Y` in all shadows, so such a tuple has `c_P ∉ F` for all `P`. ∎

## 4. Computation

The computation lives in `experiments/h4-two-flat-pencil-matching-2026-09-17/`. Most runs need
`PYTHONPATH` set to curver 0.5.1 and realalg 0.3.7, and a `../../lib` folder holding:
- `garside.py` from `experiments/h4-artin-complex-6cycles-2026-09-17`;
- `a6.py`, `arcs.py` and `search.py` from `experiments/h4-i25-image-layer-centres-2026-09-17`.

The letters are:
- **F-meridians** `p1, p2, p3`.
- **N-letters** `x0 … x11`, the non-`Z` meridians of `A_x`, as built in `gens.py`.
- **`EFF3`**, the 9 N-letters that act non-trivially in some shadow. The shadow searches take `β` over words
  in `EFF3` only. The other N-letters are invisible to every shadow, so no shadow certificate can use them,
  but tuples containing them are outside the searched set.

The scripts are:
- **`joint.py LF LN`.** Exact tuples: a Garside hash join on left normal forms, with the ejection pattern in
  `V_0, V_1, V_2` from `arcs.py`. Logs `L12.log`, `L21.log`.
- **`zsearch3.py` → `gfilter.py` → `ejection.py`.** Zero-winding commutator tuples, with the Garside verdict
  and ejection sets `O_a`. Logs `E111.log`, `E211.log`, `EGY211.log`.
- **`vcent.py`.** Vertex centres per shadow, by curver disjointness. Log `VIN.log`.
- **`nsearch.py LA LB`.** Solutions of `(*)` in the Artin action on `F_7` in all three shadows, split into
  commuting and non-commuting. Logs `N21.log`, `N12.log`, `NC12.jsonl`.
- **`purecent.py`.** The Garside test `c_P ∈ F`, with F-words of length at most 5.
- **`vsearch.py LA LB LF K r`.** The vertex-free search.
  - **Stage 1.** Burau hash of both sides of `(*)` in all three shadows. It uses 7 strands, prime
    `Q = 268435399` and `t = 91138233`, with exact integer matrices mod `Q`. A true solution always hashes
    equal.
  - **Stage 2.** An exact check in `Aut(F_7)` for each shadow, then Garside in `H_4`.
  - **Stage 3.** The Garside test `c_P ∈ F`.
  - Logs `VS12.log`, `VS22_{0,1,2}.log`, `VS31_{0,1}.log` and `VS13_{1,2}.log`, where the `K` chunks split
    by the index of `α_1`. The `VS13` run (`K = 3`) is partial: chunk `r = 0` timed out and is not included.

**Completeness.**
- If `(*)` holds in `P`, it holds in every shadow, and so its Burau hashes agree. Each search is therefore
  complete for its word lengths (with `β` in `EFF3`). The one exception is stage 3, which could report a vertex-free *candidate*
  whose `c_P` lies in `F·P_X ∖ F`, or in `F` but only as a longer word.
- No candidate arose, so the result "0 vertex-free tuples" does not depend on this exception.
