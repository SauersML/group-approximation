---
rg: 2
id: negative-base-pisot-stein-groups-are-finitely-presented
kind: claim
title: If β > 2 is a Pisot unit whose map y ↦ {−βy} reaches 0 from every point of Z[β] ∩ [0,1), then V(Z[β],⟨β⟩,ℓ) is finitely presented, through the orientation-preserving square of that coding; in degree ≥ 3 its derived subgroup is a finite-index finitely presented simple group, and every real field of degree ≥ 3 has such slopes
distinct_from:
  negative-base-pisot-stein-groups-are-contracting-rsgs: that makes the flip group G^±_β a full contracting RSG; the Stein group V itself is not an RSG in that coding, because canonical similarities there have slopes (−β)^n. Here the coding is replaced by its square, whose canonical similarities have positive slopes β^{2n}.
  stein-v-groups-act-with-type-a-on-breakpoints: that listed finite presentation for norm +1 quadratic slopes as open; this settles it.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed).

`pisot-unit-slope-stein-groups-are-finitely-presented` needs property (F), which forces an isolated-sign unit
and so misses fields such as `Q(√3)`. This node needs only the negative-base finiteness (F−₀), available in every
real field. The inputs are the same:
- BBMZ Theorem A (`contracting-rsgs-embed-in-fp-simple-groups`, item 4);
- Tanner's simplicity theorem for `D(V)`;
- the AH exact sequence as stated by Tanner.

## Statement

Let `β > 2` be a Pisot unit of degree `d ≥ 2` satisfying (F−₀): `T'(y) = {−βy}` sends every point of
`Z[β] ∩ [0,1)` to `0` in finitely many steps. Let `ℓ ∈ Z[β]`, `ℓ > 0`.

1. `V(Z[β],⟨β⟩,ℓ)` is finitely presented.
2. If `d ≥ 3`, then `D(V)` has finite index, so it is a finitely presented simple group.
3. If `d = 2`, then `N(β) = +1`, and `V^ab` surjects onto `Z`. So `D(V)` has infinite index, and its
   finite presentation is not decided here.
4. **Every real number field `K` of degree `≥ 3` is `Q(β)` for such a `β`.** So `K` carries a finitely
   presented simple irrational-slope Thompson group `D(V(Z[β],⟨β⟩,1))`, whether or not `K` has an (F) unit.
   This includes the totally real fields with no isolated-sign unit, which have no (F) unit at all
   (`f-unit-fields-are-characterized-by-isolated-sign-units`).
5. **Quadratic.** `V(Z[ε],⟨ε⟩,ℓ)` is finitely presented for every norm `+1` quadratic unit `ε > 1`, including
   `ε = 2+√3`. With the norm `−1` case, it is finitely presented for every quadratic unit `ε > 1`.

## Proof

1. **The squared coding.**
   - `S := T'^2` is piecewise `y ↦ β²y + c`, which is orientation preserving.
   - Its cylinders are the even-level cylinders of `T'`, so its boundary set is again `Z[β] ∩ [0,1)`.
   - Its follower intervals are finitely many, since they are among those of `T'` and their images.
   - Its graph `Γ_2` is strongly connected. A subinterval containing no full `S`-branch meets at most two
     branches, and `β²/2 > 1`.
   - The canonical similarities of `Γ_2` are `y ↦ a' + β^{2(|α|−|α'|)}(y − a)`, which lie in
     `V_β := V(Z[β],⟨β⟩,1)`. So `V_{Γ_2,C_{v_0}} ≤ V_β`.
2. **Finite nucleus.**
   - This is step 3 of `negative-base-pisot-stein-groups-are-contracting-rsgs-proof`, with the level
     function `λ_2 = ⌈λ/2⌉` and slopes `β^k` for any `k ∈ Z`.
   - The local action at a deep cone is `x ↦ d + β^{k+2(|ō|−|w|)}x`. Its exponent lies in a window
     independent of `f`, and `d` has bounded conjugates. So the nucleus is finite.
3. **Full.**
   - A homeomorphism that locally agrees with `V_β` is a finite patchwork of pieces `y ↦ β^k y + c`.
   - Those pieces are clopen, hence intervals with endpoints in `Z[β]`. So the homeomorphism lies in `V_β`.
   - Hence `V_β` is a full contracting RSG, and BBMZ Theorem A gives finite presentation.
   - General `ℓ` follows as in step 1 of `pisot-unit-slope-stein-groups-are-finitely-presented`.
4. **Abelianization.**
   - `H_0 = Z[β]/(1−β)` is finite.
   - `H_1 = H_2(Z[β] ⋊ Z)` contains `coker(1 − Λ²A)`, with eigenvalues the products `β_iβ_j`.
     - In degree `≥ 3` no such product is 1, as in that node, so `H_1` and `V^ab` are finite.
     - In degree 2, (F−₀) forces `r_0 = β' ∈ (0,1)` (`D^0_1 = [0,1)`), so `N(β) = +1`. Then `H_1 = Z`, and
       `V^ab ↠ H_1` by the AH sequence.
5. **Fields.** By item 1 of `algebraic-interval-exchange-groups-satisfy-boone-higman`, every real `K` is
   `Q(β)` for a unit `β ≥ 4` with (F−₀). Items 1 and 2 apply.
6. **Quadratic.** A norm `+1` unit `ε > 1` has `ε' = 1/ε ∈ (0,1)`, so (F−₀) holds by the witness lemma, and
   `ε ≥ (3+√5)/2 > 2`. Norm `−1` units have (F) and are covered by
   `pisot-unit-slope-stein-groups-are-finitely-presented`. ∎

## Lesson for general BH

A coding that fails to contain the Thompson group of a target group can be replaced by a power of itself.
- Powers keep the boundary set and the finite nucleus, and change the orientation class of the canonical
  similarities.
- So the only real input to finite presentation here is the digit-system finiteness. Orientation is bookkeeping.

The same move applies to any coding host whose canonical similarities carry a sign, a character or a
finite-order twist. Pass to the power that kills the twist before looking for a new theorem.
