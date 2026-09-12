---
rg: 2
id: el3-rank-models-factor-through-ring-rank-models
kind: claim
title: Rank models of EL_3 over a simple characteristic-p ring with no rank model of its own are trivial
distinct_from:
  block-unipotent-rank-models-of-leavitt-el3-are-trivial: that excludes one family of models, those acting on root subgroups by block unipotents, for the Leavitt algebra; this asserts that every model of EL_3 over every simple characteristic-p ring without a ring rank model is trivial, with no additivity or block hypothesis.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the rank row of the compression mechanism, which needs property (T) of the compressor group; this uses only the Steinberg relations and the ring structure, with no property (T) and no compression.
  leavitt-algebra-has-no-unital-rank-model: that is the ring-level non-embedding of one algebra; this transfers any such ring-level non-embedding to the elementary group EL_3.
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**OPEN.** Let `p` be a prime and `R` a simple unital algebra over a field of characteristic
`p`. Suppose `R` has no unital ring homomorphism into any rank ultraproduct of matrix
algebras over a field of characteristic `p`. Then every homomorphism

```text
sigma : EL_3(R) -> M^x,     M = prod_omega M_(n_i)(k) / d_omega,  char k = p,
```

is trivial.

Payoff: `R = L_(F_2)(1,2)` meets the hypothesis, so its unit group `R^x = EL_3(R)` has no
nontrivial rank model in characteristic two and is not `F_2`-linear sofic
(`non-linear-sofic-via-el3-ring-rank-rigidity`).

## Attempts

- **Additive case: established.** If root elements act by block unipotents
  `1 + psi_ij(a)` in corners `e_i M e_j`, the Steinberg relations give matrix units and a
  unital ring homomorphism into a corner
  (`block-unipotent-rank-models-of-leavitt-el3-are-trivial`). The claim is the same
  extraction with no block hypothesis.
- **Exact unipotence: proved.** In characteristic `p`, `sigma(x_ij(a)) = 1 + n_ij(a)` with
  `n_ij(a)^p = 0` exactly in `M`, commuting within each root subgroup. The only non-linear
  term is `n_ij(a) n_ij(b)` in `n_ij(a+b)` (artifact Section 1).
- **Associated-graded linearization: stops at composition.** Filtering by powers of the
  augmentation ideal of a finite unitriangular `p`-subgroup makes root actions additive.
  The commutator relation becomes a Heisenberg Lie ring representation
  `[X(a), Y(b)] = Z(ab)`. It stops at three points:
  - ring multiplication is not realized as composition of degree-raising nilpotent
    operators;
  - Weyl elements do not preserve the filtration;
  - graded objects for growing finite subgroups are incompatible.
  (Artifact Section 3.)
- **Counting on finite level subgroups: cannot finish.** In every rank model of the Leavitt
  unit group, involution types in `SL_(3·2^k)(F_2)` satisfy `f(2r) = f(r)`. That uses the
  exact doubling identity `g = g (x) I_2` and the compressor corner `g ~ g (+) I`. Regular
  modules satisfy it, so finite-subgroup counting is consistent with free models and gives
  no contradiction (artifact Section 4, Proposition 2).
- **Uniform displacement and root self-similarity: proved, not enough.**
  - The commutator expansion gives `Im n_13(a) <= Im n_23(1) + n_12(a) Im n_23(1)`. So every
    root element has displacement rank at most `2 rho`, with `rho = rk(n_12(1))`.
  - Over `L_(F_2)(1,2)`, `x_12(1)` is a product of `2^k` commuting conjugates of itself.
    Additive models then give `rho = 2^k rho = 0`, recovering the block-unipotent theorem.
  - Free modules and hyperplane-uniform modules over `(Z/2)^(2^k)` meet every such count, so
    the extraction must use Steinberg relations across root subgroups.
  - Artifact Section 4b.
- **Monomial models.** They are sofic approximations
  (`monomial-rank-models-are-hamming-models`). So a counterexample to this claim could be a
  sofic `EL_3` over a simple characteristic-`p` ring with no ring rank model. None is known.
  Finitely generated purely infinite simple rings carry the nonsoficity mechanism; rings
  that are not finitely generated are the risk.
- **Calibrations from lane `gk-l-gate-pos` (2026-09-12).**
  - *Scope.* Every simple ring that is not directly finite meets the hypothesis
    (`leavitt-algebra-has-no-unital-rank-model`'s argument needs only simplicity and
    `ts = 1 != st`). So the claim says `EL_3(S)` is never linear sofic in characteristic `p`
    for such `S`, whenever `EL_3(S)` is infinite. One such `S` with a sofic `EL_3(S)` refutes
    the claim. Over infinite fields the Leavitt unit group contains Thompson's `V`, whose
    soficity is open, so those are the riskiest instances.
  - *Not a counterexample.* A locally finite simple ring always has a rank model (left
    multiplication on finite unital subrings), so it cannot violate the hypothesis.
  - *Shape the extraction must handle.* The hybrid of
    `research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md`
    Section 7: block unipotent on the root subgroups of a polynomial subring, non-additive on
    the rest. The matrix units `u_ij = n_ij(1)` and equal-rank corners `p_i` still exist
    there. The open step is propagating block support from `x_ij(1)` to every `x_ij(a)`. The
    two expansions `x_13(a) = [x_12(a), x_23(1)] = [x_12(1), x_23(a)]` constrain the images
    of `n_13(a)` from both sides (artifact Lemma 3).
- **The hybrid shape: killed (2026-09-12).**
  - `matrix-unit-root-rank-models-of-simple-el3-are-trivial`: if the six unit root elements
    act by matrix units on orthogonal idempotents with trivial complement, the Steinberg
    relations propagate block support to every `x_ij(a)`, and the model is trivial.
  - So the extraction is proved whenever `sigma` restricted to `SL_3(F_2)` is
    `(natural (x) W) (+) trivial`.
  - The open case is complements carrying a nontrivial `SL_3(F_2)`-action, or composition
    factors other than the natural module: dual natural, Steinberg, projective.
  - Artifact Section 4c.
- **Odd characteristic, same shape: killed (2026-09-12).**
  - `matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial`: the torus elements
    `diag(-1,-1,1)` and `diag(1,-1,-1)` invert `x_13(a)`. Together with `n^p = 0` and the
    invertibility of `2`, they propagate block support; the corner collapse then applies.
  - This covers the `F_3` gate, through `EL_3(L_(F_3)(1,2)) <= G_3 <= PG`.
  - The char-2 propagation was independently re-derived by `gk-l-gate-pos`.
  - Open tool for general complements in odd characteristic: `log sigma(x_ij(a))` is exact
    and a torus weight vector of weight `eps_i - eps_j`. It is not additive in `a`, and for
    `p = 3` root weights coincide with natural weights, so this alone does not extract matrix
    units (artifact Section 4d).
- **Hamming analogue: open.** That a sofic approximation of `EL_3(R)` yields a rank model
  of `R` would reprove nonsoficity of `R^x` with no property (T).
