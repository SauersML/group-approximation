---
rg: 2
id: linear-sofic-el-groups-force-rank-model
kind: claim
title: If every projective elementary group over a simple algebra over a finite field is linear sofic over that field, does the algebra have a unital rank model?
distinct_from:
  rank-modelled-simple-rings-give-linear-sofic-projective-el: that is the forward direction, a rank model giving linear soficity of the projective elementary groups; this is its converse.
  stably-mf-elementary-groups-force-matricial-rings: that asks from MF of every EL_N for exact matriciality or a Sylvester rank function; this asks from linear soficity over the base field for a unital rank model over that field.
---

**OPEN.** Let `k` be a finite field and `R` a simple unital `k`-algebra with centre `k`. Suppose that for
every `N >= 2` the group `S_N = EL_N(R)/(EL_N(R) ∩ k^x I_N)` is `k`-linear sofic, meaning it embeds in a rank
ultraproduct of projective general linear groups over `k`. Then `R` has a unital homomorphism into a rank
ultraproduct `prod_omega M_(n_i)(k)/d_omega`.

This is rung (Σ⇒) of `kazhdan-elementary-approximation-type-mirrors-ring-type`.

## Attempts

- **Rank-approximate Steinberg relations do not obviously give a ring.**
  - A linear sofic model sends `x_12(a)` to matrices `A_a` with `rk(A_a A_b − A_(a+b)) → 0` and rank-approximate
    commutator relations.
  - To get a rank model of `R`, one would read off `a` as a rank-approximate block `A_a − 1` inside a
    unipotent frame.
  - It dies because the models need not be near-unipotent on root subgroups; conjugation by a torus-like
    element can spread the defect.
- **Calibration at the failure end.** The Leavitt algebra has no unital rank model
  (`leavitt-algebra-has-no-unital-rank-model`). Block-unipotent rank models of Leavitt `EL_3` are trivial
  (`block-unipotent-rank-models-of-leavitt-el3-are-trivial`). That is the unipotent-frame argument working
  on one ring. The general converse needs the frame without assuming it.
- **Non-simple warning.** Stably finite finitely generated algebras need not be linear sofic
  (`stably-finite-algebras-need-not-be-linear-sofic`). That source is not simple and makes no statement
  about elementary groups, so it does not touch this claim.
- **Exact lift and reduction (un-sigma-converse, 2026-09-13, unreviewed).**
  `linear-sofic-projective-el-lifts-to-gl-rank-models`: a projective model of `S_N` passes through the adjoint
  to an exact homomorphism `EL_N(R) -> U`, a general-linear rank ultraproduct over `k`, with kernel exactly
  `Z_N`. So this claim follows from ring rigidity (RR_k) of such exact models, for all `N`, with no metric
  stability input. `el3-rank-models-factor-through-ring-rank-models` is the `N = 3` form, but it allows the
  rank model over any characteristic-`p` field. Artifact `un-sigma-converse-2026-09-13.md` §1.
- **The finitely-presented-cover method of (L⇒) stops here.**
  - Linear soficity already gives an exact homomorphism into the ultraproduct, so every relator of
    `St_N(A)` holds exactly and finite presentation adds nothing.
  - The level-ideal step has no analogue: `{a : sigma(x_ij(a)) = 1}` is `0` by faithfulness.
  - Root maps satisfy only `n(a + b) = n(a) + n(b) + n(a) n(b)` and `n(a)^p = 0`.
  - A ring structure appears only after a frame, meaning idempotents `e_i` with `n_ij(a) ∈ e_i M e_j`, as in
    the block-unipotent extraction. The frame has to come from `sigma` itself. Artifact §2.
- **Torus frame, `q >= 3`: stops. At `q = 2` there is no torus.**
  - The diagonal torus of `SL_N(k)` has order prime to `p`, so `sigma(T)` gives exact weight idempotents.
  - The averages `N^c_ij(a) = sum_μ c(μ)^(-1) sigma(x_ij(μ a))` shift weights by `c ∘ α_ij`.
  - But `sigma(x_ij(a)) − 1` is a sum of all these shifts, not one corner, and commutators of the sums are
    not averages of products. So there are candidate frame idempotents but no corner support.
  - Over `F_2`, the Leavitt case, the torus is trivial.
- **Famous-level firewall.** Route `non-linear-sofic-via-sigma-converse-at-leavitt`: this claim at
  `L_(F_2)(1,2)` (simple, centre `F_2`, no rank model) makes some `EL_N(L_(F_2)(1,2))` not `F_2`-linear sofic.
  That closes the root `non-linear-sofic-group`. So a proof of this claim is at least as hard as exhibiting a
  non-linear-sofic group. A refutation needs a simple rankless algebra with all `S_N` linear sofic, which at
  the Leavitt algebra is the open `binary-leavitt-unit-group-is-f2-linear-sofic`.
