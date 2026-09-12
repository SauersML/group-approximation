---
rg: 2
id: binary-jacobson-el3-rank-radical-is-the-finitary-kernel
kind: claim
title: Every characteristic-two rank model of the binary Jacobson elementary group EL_3 kills its finitary kernel
distinct_from:
  binary-jacobson-mf-radical-dichotomy: that is about MF approximations (unitaries in operator norm); this is about characteristic-two rank models (matrices over F_2 in normalized rank), whose radical has the same two possible values by the same symbol-sequence argument.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that shows every finite quotient kills the head root; this asks the same of every rank model, where relations need only hold up to normalized rank o(1).
artifacts:
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

**OPEN.**

**Setting.**
* `J = F_2<S,T | TS = 1>`, `Q = 1 − ST`, `E = EL_3(J)`.
* The symbol sequence `1 -> L -> E -> EL_3(F_2[z,z^(−1)]) -> 1` has
  `L = GL_fin(N x {1,2,3}, F_2)` (`binary-jacobson-mark-dichotomy-holds-from-rank-two`).
* A *rank model* is a homomorphism into a characteristic-two rank ultraproduct.

**Claim.** Every rank model of `E` kills `x_13(Q)`. Equivalently, the rank radical of `E` (the
intersection of the kernels of all rank models) is `L`.

**Dichotomy (established).** The rank radical is `1` or `L`.
* The quotient is residually finite (`laurent-elementary-groups-are-residually-finite`). Regular
  representations of its finite quotients are rank models that separate its points, so the radical
  lies in `L`.
* `L` is simple, so a normal subgroup of `E` inside `L` is `1` or `L`.
* The radical is `L` iff every model kills the head `x_13(Q)`.

**Payoff.**
* `J` embeds in `R = L_(F_2)(1,2)` (`prime-characteristic-defect-embeds-the-jacobson-algebra`), so
  `E` embeds in `R^x = EL_3(R)`.
* A nontrivial rank model of `R^x` is injective (`binary-leavitt-unit-group-is-simple`), so it
  retains the head.
* So this claim would give: `R^x` has no nontrivial characteristic-two rank model. That means
  `binary-leavitt-unit-group-is-f2-linear-sofic` fails, and
  `leavitt-el3-rank-models-over-finite-fields-are-trivial` holds for the binary algebra over `F_2`.

## Attempts

* **Necessary conditions.**
  * `E` is not LEF and not sofic, since a sofic approximation linearizes to a rank model that retains
    the head.
  * The obstruction must use more than the Whitehead shift: `L ⋊ Z` is LEF and retains the head
    (`binary-jacobson-finitary-whitehead-shift-is-marked-lef`).
* **Dies: algebra-like models.** Root maps `x_ij(a) -> 1 + ρ(a)`, with `ρ` an almost-representation
  of `J`, force `ρ(Q) = 0`, because rank ultraproducts are directly finite. This is (C3) of
  `research/artifacts/el3-rank-model-toeplitz-assembly-2026-09-12.md`.
* **Dies: finite images and Laurent pullbacks.** They kill the head
  (`binary-jacobson-elementary-mark-is-finite-quotient-invisible`).
* **Dies if `E` is not LEF: level-factoring models.**
  * The model factors through representations of `GL_m(F_2)` with positive transvection
    displacement, for instance natural level assignments, or a positive projective share.
  * `transvection-displacement-forces-exact-local-embedding` makes such a head-retaining model an
    exact local embedding, so `E` would be LEF.
* **Normal form (w3-gate-construct, 2026-09-12).** A head-retaining model is:
  * an exact representation of `GL_(3N_k)(F_2)` at a moving level, with uniform displacement
    `>= c_0/4`;
  * with compressor images `x_12(T)`, `x_23(S)` locally inner through truncated shifts, with
    corrections that cannot all be negligible at any level (Section 4 of the artifact).

  Part (b) of that normal form needs `E` not LEF.
* **Next attempts.**
  * Decide whether `E` is finitely presented. If it is, it is not LEF, because finite quotients kill
    the head, and the normal form applies verbatim.
  * Construct the level corrections coherently in `M`, or show the coherence equations force the
    transvection `ρ_k(u_13(M,M))` into the corrections at a rank cost `c_0`.
