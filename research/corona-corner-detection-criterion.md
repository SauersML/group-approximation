---
rg: 2
id: corona-corner-detection-criterion
kind: claim
title: Corner-detection criterion for a central defect square of any order
distinct_from:
  central-sign-corona-obstruction: that claim is the order-two case and concludes that the mark dies; this one drops the order hypothesis, concludes only a corner-detection dichotomy, and isolates the single step where finite order was used.
  finite-normal-compression-obstruction: that claim averages over a finite normal subgroup; this one keeps a single central element and replaces finiteness by a spectral-gap request.
  thom-central-corner-criterion: that is a published positive criterion characterising hyperlinearity by embeddability of every twisted central corner; this one is a negative criterion about corona corners of a compression defect square and says nothing about traces being faithful.
  normal-kazhdan-defect-non-mf: that claim gets its corner from the Kazhdan projection of a normal subgroup and concludes non-MF outright; this one analyses what corners the mark itself can supply and stops at a dichotomy.
artifacts:
  - non_mf_groups_exist.tex
---

Let `Gamma` have property (T), let `iota: Gamma -> H`, let
`t iota(Gamma) t^-1 <= iota(Gamma)` and `[c, iota(Gamma)] = 1`, put
`d = t c t^-1`, `u = [d, iota(a)]` for `a in Gamma`, and let `eps = u^2`
lie in `Z(H)`.  **No order hypothesis on `eps`.**  Let
`Theta: H -> U(Q)` be any corona representation and let
`B = Theta(H)' cap Q` be the relative commutant.  Then:

1. for every nonzero projection `q in B`, the corner representation
   satisfies `‖q Theta(x) q - q‖_2 = 0` in the corner's own normalized
   trace, for every `x` in the normal closure of `u` — in particular for
   `x = eps`;
2. hence `sp(Theta(eps))` is a connected closed subset of the circle
   containing `1` — a closed arc through `1`, or the whole circle, or
   `{1}`;
3. hence `Theta(eps) = 1` as soon as there are a nonzero projection
   `q in B` and a scalar `lambda` with
   `‖(Theta(eps) - lambda) q‖ < |lambda - 1|`.

Clause 3 with `eps` of finite order is the central-sign criterion: a
finite-order unitary has finite spectrum, so the required `q` is the
spectral projection of `Theta(eps)` at any `lambda != 1` in its spectrum,
and it lies in `C*(Theta(eps)) <= B`.

**This is the exact place, and the only place, where torsion enters the
mechanism.**  Everything preceding clause 3 — the presentation, property
(T), one-sided compression, Kazhdan transport, the corner reduction — is
insensitive to the order of `eps`.  Finite order is consumed solely as a
supply of projections in `B` that separate `Theta(eps)` from `1`; see
`commutant-projection-extraction` for the residual question, and
`hs-invisibility-inflation-no-go` for why some corner is mandatory.
