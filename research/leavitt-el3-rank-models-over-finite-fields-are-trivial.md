---
rg: 2
id: leavitt-el3-rank-models-over-finite-fields-are-trivial
kind: claim
title: Rank models of EL_3 over a Leavitt algebra over a finite field are trivial in the field's characteristic
distinct_from:
  el3-rank-models-factor-through-ring-rank-models: that is the class statement over every simple characteristic-p ring without a ring rank model, which one linear sofic EL_3 over any such ring would refute; this is the single Leavitt instance over a finite field, where self-similarity R ~= R^n and known nonsoficity are available.
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that kills only the characteristic-two models whose unit root elements are block supported; this asserts that every model of the Leavitt instance is trivial.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the open positive gate for the binary unit group; this instance with K = F_2 and n = 2 would refute it, since EL_3(R) is an infinite subgroup of R^x.
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**OPEN.** Let `K` be a finite field of characteristic `p`, `n >= 2` and `R = L_K(1,n)`. Every
homomorphism

```text
sigma : EL_3(R) -> M^x,     M = prod_omega M_(n_i)(k) / d_omega,  char k = p,
```

is trivial.

**Payoff.**
* `EL_3(R)` is infinite, so it is not linear sofic over any field of characteristic `p`. With
  `K = F_2` and `n = 2` this settles `non-linear-sofic-group`
  (`non-linear-sofic-via-leavitt-el3-rank-triviality`).
* For `n = 2`, `R ~= M_3(R)` gives `EL_3(R) <= GL_3(R) ~= R^x`. So `R^x` is not `F_p`-linear
  sofic, and neither is `PG` when `K = F_3` (through
  `leavitt-units-embed-in-their-scalar-quotient`).
* This instance is the payoff carrier. The class statement
  `el3-rank-models-factor-through-ring-rank-models` implies it
  (`leavitt-el3-rank-triviality-from-ring-rank-rigidity`), but a counterexample to the class
  statement over some other ring leaves this claim untouched.

## Attempts

- **Excluded in every characteristic (established).**
  - Block support of the six unit root elements on orthogonal idempotents:
    `matrix-unit-root-rank-models-of-simple-el3-are-trivial` (char 2) and
    `matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial` (odd), with
    `gk-vf-linear`'s scope note. This is `(natural (x) W) (+) trivial` on `SL_3(F_p)`.
  - `(dual natural (x) W) (+) trivial`, through transpose-inverse
    `EL_3(R) ~= EL_3(R^op)` (`gk-vf-linear`, verification artifact Section 29, eda113e5ce).
  - Monomial models: `monomial-rank-models-are-hamming-models` together with
    `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
- **Free content is not reached by propagation.** `free-rank-models-on-sl3-admit-no-block-support`:
  - a model with positive free content on `SL_3(F_p)` has
    `rk((sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1)) > 0`, so it never meets the matrix-unit
    hypothesis;
  - such models exist for `EL_3` of the locally matricial algebra `lim M_(p^k)(F_p)`, which
    has a ring rank model;
  - so the Leavitt structure has to enter any proof here.
- **Instance-specific tools (artifact Sections 4 and 4b).**
  - The level subgroups `SL_(3 n^k)(K)`.
  - The doubling identity `g = g (x) I_n` and the compressor corner `g ~ g (+) I`, which give
    `f(2r) = f(r)` on involution types for `n = 2`.
  - Conjugacy `x_12(e) ~ x_12(1)` for nonzero sums `e` of level idempotents, and
    `x_12(1)` as a product of `n^k` commuting conjugates of itself.
- **Surviving shapes to cover.** Nontrivial complements. Natural and dual pieces together.
  Other composition factors (adjoint, Steinberg, projectives). Non-split extensions. Free or
  projective content on finite subgroups, glued through level-changing units such as `s_0`
  and Thompson `V`.
