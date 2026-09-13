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
