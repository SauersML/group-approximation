# 2026-08-20 — Self-similar dimension pressure and the same-model gap

**Status:** literature integration plus one new open compiler target.  No
nonhyperlinear group is claimed.

## 1. The exact profile boundary

Slofstra's arXiv:1806.05267 supplies the closest established group
construction to a dimension-triggered adversary.  A shift compresses an
infinite Clifford family into finitely many generators, the HNN relation
`tzt^-1=z^2` gives self-similar addressing, and a quantitative BORS Higman
embedding transports short recursive consequences into a finite
presentation.  The result is a lower bound

```text
hlp(w;delta,epsilon) >= C' exp(C(delta/epsilon)^alpha),  alpha<1/2.
```

This is dimension pressure, not exclusion.  Hyperlinearity permits every
finite value of the profile, however large.  The nonhyperlinear endpoint is
`hlp=+infinity` at fixed positive separation for all sufficiently small
defect.

Slofstra's Lemma 3.1 already gives the terminal robust capacity estimate: an
`epsilon`-homomorphism on the entire finite Clifford group retaining the
central sign has dimension at least `2^(floor(n/2)-1)`.  But Lemma 3.4 loses a
factor `(n+1)^2` when it constructs that global map from the standard local
relators.  The new trigger must eliminate precisely this growing local-to-
global loss.

## 2. The diagonal splice

The needed upgrade is not

```text
an epsilon-model of dimension d implies a later model needs dimension F(d).
```

It is

```text
the same d-dimensional model contains a certified subsystem requiring
dimension F(d)>d.
```

This is recorded as `same-model-supercritical-clifford-trigger`.  The
Amitsur--Levitzki multiplicity tape is a possible endogenous dimension sensor;
Slofstra's approximate Clifford estimates are a possible capacity
contradiction.  The missing theorem is the constant normalized-HS semantic
transport joining them.  Any bound growing with detected dimension or
runtime merely recreates a finite hyperlinear profile.

## 3. Program-to-group compilation: two different tools

Mikaelian arXiv:2507.04347v8 gives an explicit algorithm from an effectively
enumerated recursive presentation to explicit words in a finite presentation,
optionally with a two-generator host.  This is valuable for materializing a
self-referential construction, but it does not state the area bound needed to
prevent HS error from accumulating with runtime.

The quantitative role remains with BORS and its Chornomaz--Wagner refinement,
already recorded as `quantitative-higman-embedding-with-dehn-control`.

## 4. Rigidity is compatible with arbitrary computation—but normalization is decisive

Fournier-Facio arXiv:2512.09180v2, Theorem A, embeds every countable group in a
property-(T), Frobenius-stable group, with a finitely presented host for a
recursively presented input.  The result demonstrates that arbitrary
computation, finite presentation, and strong-looking rigidity can coexist.

It does not solve the hyperlinear problem: the metric is the unnormalized
Frobenius norm, and stability is obtained from having no nontrivial
Frobenius-approximable quotient.  Normalized Hilbert--Schmidt models can hide
low-rank errors at vanishing cost.  The factor which turns local failure into
positive trace density is still the missing resource.

## 5. Deduplication against Cairn

- MIP* recursive compression, TailoredMIP, Manzoor's non-co-hyperlinear IRS,
  and Lin's `MIP^co=coRE` are already integrated.
- Dinur's classical gap amplification is integrated, together with the
  explicit warning that CSP unsatisfaction still needs an HS/group compiler.
- Dogon--Vigdorovich's normalized-HS stability-to-nonhyperlinear-extension
  theorem is already established by citation.
- Kun--Thom and Alekseev--Thom are already represented by the wreath and
  centralizer/commutant lanes.  Their spatial support recovery is
  permutation-specific; the unitary analogue remains the published
  Alekseev--Thom commutant-coordinate problem and Cairn's downstream
  `kt-centralizer-normalization-hs` target.

The new graph contribution is therefore narrow: the exact Slofstra profile
theorem, the effectivity-versus-quantitative Higman fence, the
unnormalized-versus-normalized stability fence, and the explicit same-model
supercritical trigger route into `hs-pcp-boone-compiler`.
