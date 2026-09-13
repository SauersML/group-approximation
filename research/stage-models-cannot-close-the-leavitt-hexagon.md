---
rg: 2
id: stage-models-cannot-close-the-leavitt-hexagon
kind: claim
title: No stage model of the Leavitt hexagon kills the closing letter, exactly or in rank, so hexagon closing cannot refute the binary corner claim
distinct_from:
  leavitt-unit-groups-have-no-unstable-k2-at-rank-three: that presents the unit group as the hexagon fundamental group modulo one closing letter; this shows that no nontrivial stage model realizes the closing relation, exactly or up to rank zero.
  isolated-regular-a2-hexagon-has-free-external-holonomy: that shows one cell with a coherent finite realization closes after a gauge; this shows the full-radius hexagon over the Leavitt algebra has no coherent finite realization at large stages, so its holonomy is forced.
  monomial-rank-models-are-hamming-models: that compares rank and Hamming distance for monomial matrices; this applies it to the closing letter and adds an exact per-stage obstruction that uses only finite presentation and simplicity.
  graphs-of-locally-finite-groups-carry-regular-rank-models: that builds weakly finite models of graphs of locally finite groups; this shows that on the hexagon every such model keeps the closing letter rank-far from the identity.
  leavitt-regular-atlas-asymptotic-permutation-cover: that asks for asymptotic finite covers of the A8 atlas of U_Q, and it uses the same no-finite-quotient argument to exclude exact covers; this applies that argument to the rank-three hexagon of unipotent radicals and its closing letter, and adds the rank gap from nonsoficity.
artifacts:
  - research/artifacts/hexagon-closing-letter-stage-obstruction-2026-09-12.md
---

**ESTABLISHED** (artifact Sections 1–5, route `stage-models-cannot-close-the-leavitt-hexagon-proof`).
* **Verified.** `w4-vf-gate`, Sections 38 and 40 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`
  (427f2bfa50, 20848c2409). No mathematical corrections.
* **Conditional.** For `p = 3`, on the import of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`.
* **Still open.** `binary-complement-corner-has-no-weakly-finite-image`.

Let `p ∈ {2,3}`, `R = L_(F_p)(1,2)` and `G = R^x ≅ π_1(Y_hex)/<<t>>`, with `Y_hex` and `t` as in
`leavitt-unit-groups-have-no-unstable-k2-at-rank-three`, point 4.

1. **The letter.** `t` maps to a generator of `π_1(hexagon graph) = Z` and has infinite order. No power of it is
   conjugate into a vertex group. Killing `t` is the same as killing the words
   `x_ij^132(r)^-1 x_ij^123(r)` for `(i,j) ∈ {(1,2),(1,3)}` and `r` in a basis of `R`, in the tree amalgam.
2. **No exact closing.** Every homomorphism of `π_1(Y_hex)` into an algebraic ultraproduct of finite groups, or of
   `GL_(m_n)(A_n)` with `A_n` commutative, that kills `t` is trivial. Per stage, for exhausting finite pieces there
   is `n_1` such that for all `n >= n_1`, every finite quotient of the six-piece stage colimit `C_n` kills `x_12(1)`.
   So no choice of forest bijections in Theorem 1.1 of
   `graphs-of-locally-finite-groups-carry-regular-rank-models` makes the letter permutation the identity.
3. **No rank-null closing.**
   * Every monomial rank model of `π_1(Y_hex)` with `rk(σ(x_12(1)) - 1) > 0` has `rk(σ(t) - 1) > 0`.
   * There is `ε_p > 0` such that every Theorem 1.1 model has `rk(σ(t) - 1) >= ε_p`.
   * The reason: `rk(σ(t) - 1) = 0` would place `G` in a universal sofic group.
4. **Calibrated.** The hexagon closes exactly over `F_2` and `F_3` (radicals of order 8 and 27 in `SL_3(F_p)`), over
   the locally finite ring `R_0`, and over `F_2[x]` in finite quotients. So "infinite", "finitely generated" and
   "simple" are each needed.

**Inputs.**
* Point 2: `leavitt-unit-group-finitely-presented`, `binary-leavitt-unit-group-is-simple`, and, for the ternary case,
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`, conditional as that claim is.
* Point 3:
  * `openai-leavitt-unit-nonsofic`;
  * `d-ary-leavitt-groups-nonsofic-over-finite-fields`;
  * `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`;
  * `monomial-rank-models-are-hamming-models`;
  * Elek–Szabó's embedding criterion for soficity (literature).

**Payoff.** A nontrivial weakly finite model of `π_1(Y_hex)` killing `t` would refute
`binary-complement-corner-has-no-weakly-finite-image`. By points 2–3 it cannot live in an algebraic ultraproduct of
finite or commutative-linear matrix groups, nor in a monomial rank model. The next target class is non-monomial
`F_2`-linear rank models, which is `binary-leavitt-unit-group-is-f2-linear-sofic`.

On the proof side, "a relation-only proof must use `t = 1`" is no constraint for arguments valid in ultraproduct
targets, because `t = 1` already trivializes them. A proof of the representation form must be a certificate valid in
every weakly finite ring.

**Not claimed.** Nothing about non-monomial linear models, or about weakly finite rings with no metric structure.
Nothing about the rank-two kernel beyond artifact Section 6.

## Attempts

- 2026-09-12 `w7-hexagon-closing`: opened, with a candidate proof on paper in artifact Sections 1–5.
  - Point 2 uses Łoś, finite presentation and the absence of finite quotients.
  - Point 3 uses nonsoficity through the Hamming comparison.
  - The per-stage Corollary 2.4 is elementary and is the first thing to check. Corollary 3.2 depends on it.
- 2026-09-12 `w4-vf-gate` §38 (427f2bfa50): PASS on Sections 1–6 and this display, with no mathematical corrections.
  - The ternary transfer in Section 5 is re-derived.
  - The 38.5 advisories are applied:
    - the centralizer is renamed `Z_n`;
    - the route requires the ternary inputs;
    - the rank bullet on the corner entry is corrected.
  - The route is created.
- 2026-09-12 `w4-vf-gate` §40 (20848c2409): PASS on 767ec353f4. The last `Z_n` rename is applied, and the status
  now reads ESTABLISHED.
