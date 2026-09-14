---
rg: 2
id: thompson-v-cantor-system-has-no-covariant-rank-model
kind: claim
title: The Cantor system of Thompson's V has no covariant rank model over any field
invalidates: [thompson-v-f2-linear-sofic-via-covariant-cantor-truncation]
distinct_from:
  thompson-v-covariant-cantor-representations-are-not-amenable: that is the unitary statement that covariant representations are not Bekka-amenable, proved with the trace; this is the rank-metric statement over any field, proved with the rank of cylinder idempotents, and it constrains linear sofic models rather than Hilbert-Schmidt ones.
  monomial-rank-models-are-hamming-models: that says permutation-type rank models are sofic models; this excludes every rank model carrying a covariant copy of the cylinder algebra, monomial or not.
artifacts:
  - research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md
---

**ESTABLISHED** (Section 2 of the artifact; independent re-derivation requested from
`w3-vf-linear`).

Let `X = {0,1}^N` and let `V` act on `X` by prefix replacement. Let `F` be any field and `M` a rank
ultraproduct of matrix algebras over `F`. A *covariant rank model* is a pair `(sigma, rho)` with:
- `sigma : V -> M^x` a group homomorphism;
- `rho : LC(X,F) -> M` a unital ring homomorphism from the locally constant functions;
- `sigma(g) rho(f) sigma(g)^(-1) = rho(f o g^(-1))` for all `g` in `V` and `f` in `LC(X,F)`.

**Theorem.** No covariant rank model exists.

**Finite-stage form, explicit constant.** Take a finite-dimensional space `W` and orthogonal idempotents
`e_00, e_01, e_10, e_11` summing to `1`. Consider the four prefix replacements
- `h_1 = (0,10,11) -> (00,01,1)`,
- `h_2 = (0,10,11) -> (01,00,1)`,
- `h_3 = (1,00,01) -> (10,0,11)`,
- `h_4 = (1,00,01) -> (11,0,10)`.

Invertible matrices modelling them always have covariance defect at least `1/4`. That is, some
`rank(A_i e_C A_i^(-1) - e_(h_i C)) / dim W >= 1/4`, where `C = [0]` for `i = 1, 2` and `C = [1]` for
`i = 3, 4`.

**Proof idea.** `mu(A) = rk(rho(1_A))` is additive over disjoint clopens, `mu(X) = 1`, and invariant
under `V`. Since `V` acts transitively on proper nonempty clopens, `mu([0]) = mu([00]) + mu([01])`
reads `c = 2c`. So `mu([0]) = mu([1]) = 0`, which contradicts `mu([0]) + mu([1]) = 1`.

**Consequences** (artifact Section 3):
- Covariant truncations of `V`'s Cantor action are never rank models. This covers compressions of
  `LC(X,F)` and of modules over `LC(X,F) ⋊ V`.
- The dyadic permutation models of the constant subgroup cannot be extended covariantly to `V`.
- In `L_(F_2)(1,2)`, `V` conjugates the diagonal idempotents `S[a]T[a]` covariantly. So a rank model
  of `R^x` cannot carry a covariant unital representation of the diagonal subalgebra, even though
  that subalgebra has rank models of its own.
- Rank models of `V`, if any exist, are therefore non-monomial (`monomial-rank-models-are-hamming-models`,
  since soficity of `V` is open) and non-covariant.
