---
rg: 2
id: el3-rank-models-factor-through-ring-rank-models
kind: claim
title: Rank models of EL_3 over a simple characteristic-p ring with no rank model of its own are trivial
distinct_from:
  block-unipotent-rank-models-of-leavitt-el3-are-trivial: that excludes one family of models, those acting on root subgroups by block unipotents, for the Leavitt algebra; this asserts that every model of EL_3 over every simple characteristic-p ring without a ring rank model is trivial, with no additivity or block hypothesis.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the rank row of the compression mechanism, which needs property (T) of the compressor group; this uses only the Steinberg relations and the ring structure, with no property (T) and no compression.
  leavitt-algebra-has-no-unital-rank-model: that is the ring-level non-embedding of one algebra; this transfers any such ring-level non-embedding to the elementary group EL_3.
  leavitt-el3-rank-models-over-finite-fields-are-trivial: that is the Leavitt instance over finite fields, which carries the payoff on its own route; this is the class statement over every simple characteristic-p ring without a ring rank model, which one linear sofic EL_3 over any such ring would refute.
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
- **Finite triangular extensions: killed (2026-09-12, lane `gk-rk-extensions`).**
  - `filtered-matrix-unit-rank-models-of-simple-el3-are-trivial`: suppose `sigma` preserves
    a finite flag split by idempotents, and each graded piece is a matrix-unit piece, a
    transposed piece (such as the dual natural module) or a trivial piece. Then `sigma` is
    trivial.
    - The graded pieces die by the two matrix-unit corollaries; transposed pieces go through
      `R^op`.
    - `perfect-groups-have-no-triangular-models-with-trivial-diagonal` kills the extension
      terms: a perfect group acting upper triangularly with trivial diagonal lies in a
      nilpotent unipotent group.
  - Covered: the non-split extensions `0 -> trivial -> W -> natural -> 0` and
    `0 -> natural -> W -> trivial -> 0`, finite towers, and complements whose extension terms
    run in one direction.
  - In coordinates each extension term is a product with a block term,
    `d_ik(ab) = d_ij(a) v_jk(b)`.
  - Surviving shapes (artifact `research/artifacts/el3-rank-model-extensions-2026-09-12.md`,
    Section 3):
    - two-sided mixing with no finite triangular ordering;
    - composition factors of Steinberg, projective or regular type, or pieces with no block
      form;
    - diffuse flags of unbounded length at finite stages, where the nilpotency bound fails.
  - Not landed as a route: "every model admits such a flag" is equivalent to triviality
    given the theorem.
- **Flags of any length: the triangular part carries nothing (2026-09-12, lane `gk-rk-extensions`).**
  - `unipotent-valued-rank-models-of-el3-are-trivial`: over any field `k` and any ring `R` with
    `p 1 = 0`, a model with unipotent values is trivial.
    - The lever is the exact identity `rk(x^m - 1) = rk(x - 1)` for unipotent `x` and `m`
      invertible in `k`, at every finite stage and with no bound on nilpotency index.
    - One torsion element normally generates `EL_3(R)` through `SL_3(F_p)`: `x_12(1)` if
      `char k != p`, the 3-cycle if `p = 2`, `diag(-1,-1,1)` if `p` is odd.
    - Filter: in a nontrivial characteristic-`p` model that element's image is not unipotent.
  - `flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`: for flags of unbounded length
    at finite stages, diagonal compression is a well-defined homomorphism, because
    `rk(D(x)) <= rk(x)` for block triangular `x`. A flag-preserving model is trivial exactly
    when its diagonal model is.
    - Unitriangular models (the diffuse-flag question) die.
    - Triangularizable models die.
    - Models with bounded block dimensions die whenever `EL_3(R)` has no nontrivial
      finite-dimensional representation.
  - What survives: diagonal models with blocks of unbounded dimension and normalized rank tending
    to 0. These are general rank models on smaller blocks, so the diffuse-flag case reduces to
    this claim itself (artifact `research/artifacts/el3-rank-model-extensions-2026-09-12.md`,
    Section 4.3).
- **Overreach guard (2026-09-12).** The payoff is now also carried by the instance claim
  `leavitt-el3-rank-models-over-finite-fields-are-trivial`, which has its own route into
  `non-linear-sofic-group`. This class statement implies it
  (`leavitt-el3-rank-triviality-from-ring-rank-rigidity`).
- **Dual natural shapes: killed** (`gk-vf-linear`, Section 29): transpose-inverse
  `EL_3(R) ~= EL_3(R^op)` reduces them to the matrix-unit theorems over `R^op`.
- **Free content: a calibration, not a kill.** `free-rank-models-on-sl3-admit-no-block-support`:
  - positive free content on `SL_3(F_p)` makes `rk(N_23 N_12) > 0`, so block support never
    applies;
  - free models exist for `EL_3(lim M_(p^k)(F_p))`, whose ring has a rank model;
  - so summand-level block support is not the general mechanism.
  - For a nonsofic host, free-like survivors are monomial on each finite subgroup in their own
    bases and glue those bases non-monomially along level-changing units (artifact Section 4e).
- **Hamming analogue: open.** That a sofic approximation of `EL_3(R)` yields a rank model
  of `R` would reprove nonsoficity of `R^x` with no property (T).
- **Two root identities are equivalent to this claim (gk-rk-unipotent, 2026-09-12, 685d99751a).**
  - `el3-unit-root-matrix-units-iff-two-root-identities` (established): for any rings, the six
    unit root elements act by matrix units iff `N_12^2 = 0` and `N_23 N_12 = 0`, where
    `N_ab = sigma(x_ab(1)) - 1`. The idempotents are forced, `p_i = N_ij N_ji`. In
    characteristic two the single identity `N_23 N_12 = 0` decides.
  - `matrix-unit-rank-models-extract-ring-rank-models` (established): matrix-unit models extract
    a unital ring homomorphism into a rank-ultraproduct corner, or are trivial. Simplicity is
    not used.
  - So this claim is equivalent to `rank-models-of-el3-satisfy-the-two-root-identities`, through
    routes `two-root-identities-give-el3-ring-rigidity` and
    `el3-ring-rigidity-gives-the-two-root-identities` (intended cycle).
  - Calibration `fd-represented-coefficients-violate-two-root-identities`: the identity fails in
    regular-representation models over any finitely represented coefficient ring. Even the
    Toeplitz subring doesn't suffice. A proof must use a coefficient family with no
    finite-dimensional representation, or the no-rank-model hypothesis beyond relations.
  - Artifact `research/artifacts/el3-two-root-identities-2026-09-12.md`.
