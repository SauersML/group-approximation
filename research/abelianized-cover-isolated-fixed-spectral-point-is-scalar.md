---
rg: 2
id: abelianized-cover-isolated-fixed-spectral-point-is-scalar
kind: claim
title: In any corona model of the abelianized cover of a full-MF-radical group, an isolated liftable fixed point of the kernel spectrum carries only a character, and regular spectra have no isolated points
distinct_from:
  abelianized-cover-injective-corona-model-carries-nonzero-twist: that kills [E,M] in a whole model whose pushed relation-module class vanishes; this localizes a model at one clopen G-fixed point of the joint spectrum of M, where the class vanishes automatically for liftable points, and concludes the stronger statement that the whole cover acts by one character there; it also records that the localization is unavailable on connected spectra.
  abelianized-cover-twist-vanishes-iff-equivariant-fox-section: that characterizes zero twist by a section over the whole joint spectrum and notes which fixed points lift; this uses the fixed-point lifting criterion (reproved here in one line) to strip scalar blocks from a model, and says nothing about sections over non-fixed points.
  commutant-projection-extraction: that asks for commutant projections of a central unitary with connected spectrum in general; this is the special case of the kernel algebra C*(W(M)) of the cover, where disconnection at a fixed point gives a scalar corner, and records that the regular models are exactly the connected case.
  dummy-abelianized-cover-df-splits-regular-trace-and-shadow: that splits DF into (REG) and (SH) and computes the regular spectrum; this uses its item 3 (full spectrum hat M) together with connectedness of hat M to kill fixed-point localization against (REG), and gives one stripping lemma for (SH).
  full-mf-radical-abelianized-cover-is-not-mf: that is the open target DF; this is a class kill and a stripping lemma, not DF.
artifacts:
  - research/abelianized-cover-isolated-fixed-spectral-point-proof.md
  - research/dummy-abelianized-cover-df-splits-regular-trace-and-shadow.md
  - research/abelianized-cover-twist-vanishes-iff-equivariant-fox-section.md
  - research/full-mf-radical-abelianized-cover-is-not-mf.md
---

**ESTABLISHED (written proof; not Lean-verified).**

## Setting

- `F = F(x_1,...,x_n)`, `R` normal in `F`, `G = F/R` with `Rad_MF(G) = G`.
  No finite presentation is needed.
- `E = F/[R,R]`, `M = R/[R,R]`, a `ZG`-module; `M_G = R/[F,R]`.
- `eps : M_G -> Z^n` is the exponent-sum map, induced by `R <= F -> F^ab`.
- A *model* is a homomorphism `W : E -> U(Q)` into a norm matrix corona
  `Q = prod_k M_(d_k) / (+)_k M_(d_k)`.
- `A = C*(W(M)) = C(X)`, where `X`, the *kernel spectrum*, is a closed
  subset of the compact group `hat M = Hom(M, T)`.  Each `W(e)` normalizes
  `A`, and `X` is invariant under the dual of the module action of `G`.
- A point `chi in X` is *liftable* if it is `G`-fixed and factors through
  `eps`.

## Statement

1. **Scalar corners.**  Let `chi in X` be an isolated, liftable point, and
   let `p in A` be the indicator of `{chi}`.  Then `p` commutes with
   `W(E)`, and there is a homomorphism `lambda : E -> T`, factoring through
   `E^ab = Z^n`, with
   ```text
   W(e) p = lambda(e) p   for all e in E.
   ```
   In particular `W(w) p = p` for every `w in E' = [E,E]`.
2. **Stripping.**  If `Y` is any finite set of isolated liftable points of
   `X`, and `p_Y = sum_(chi in Y) p_chi`, then `W = W_0 (+) (+)_(chi in Y) lambda_chi p_chi`,
   where `W_0` is the model on `(1 - p_Y) Q (1 - p_Y)`.  `W_0` has kernel
   spectrum `X \ Y`, and `W_0(w) = W(w)(1 - p_Y)` for every `w`.  So an
   element of `E'` is killed by `W` if and only if it is killed by `W_0`.
   Scalar padding at a liftable fixed point, such as `rho (+) 1_(N_k)`
   whose trivial character is isolated, can be removed without changing
   which elements of `E'` the model detects.
3. **Finite orbits.**  If `G` has no proper finite-index subgroup, every
   finite `G`-orbit in `X` is a fixed point.  So every finite clopen
   `G`-invariant subset of `X` is a finite set of isolated fixed points.
4. **Superperfect bases.**  If `G` is perfect and `H_2(G) = 0`, every
   `G`-fixed point of `hat M` is liftable.  This holds, for example, for the
   superperfect Leavitt-Steinberg bases of the route.
5. **Connected spectra.**  `hat M` is connected, because `M` is
   torsion-free.  A regular model (item 3 of
   `dummy-abelianized-cover-df-splits-regular-trace-and-shadow`) has
   `X = hat M`.  Hence it has no isolated points and no nontrivial clopen
   `G`-invariant subsets, and items 1-2 say nothing about it.

## What this kills

**Class.**  Arguments for `(DF)`, or for `(REG)`, that localize a model at a
`G`-fixed point of the kernel spectrum by a projection in `C*(W(M))` and then
use the full MF radical of `G` on the localized corner.

**Where every member dies.**  There are two possible outcomes, and neither
gives a contradiction.
- **At an isolated liftable point**, the localization succeeds and the
  full radical of `G` forces the corner to be a character of `E`
  (item 1).  That is consistent with `E` being MF: a character kills `E'`
  and detects nothing.
- **At a non-isolated fixed point** there is no nonzero projection of `A`
  supported at the point.  Any spectral projection of a neighborhood `U`
  is `G`-invariant only if `U` is.  Producing a norm-level invariant
  projection there is the spectral-gap problem of
  `commutant-projection-extraction`.

In the regular case, which `(REG)` must defeat, the spectrum `hat M` is
connected, so only the second outcome occurs.  So a proof of `(REG)`
cannot run through fixed-point localization in `C*(W(M))`.  It must use
either the Hilbert-Schmidt closure, where the regular-trace kill recorded
on `full-mf-radical-abelianized-cover-is-not-mf` applies, or
finite-dimensional lifts of non-invariant neighborhoods.

## What survives

- **Non-liftable isolated fixed points.**  Take `chi` isolated and fixed,
  with `chi` not trivial on `ker eps = H_2(G)` (for perfect `G`).  Then
  the corner is a projective corona representation of `G` with scalar
  cocycle class `chi|H_2(G)`.  Equivalently it is a corona model of the
  universal central extension on which `H_2(G)` acts by a nontrivial
  character.  Whether a full-radical `G` admits such a model is not
  decided here.
- `(DF)` itself stays OPEN.

DERIVATION
abelianized-cover-isolated-fixed-spectral-point-proof
