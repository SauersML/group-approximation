---
rg: 2
id: jones-index-blind-on-unbounded-defect-sector
kind: claim
title: A quantized Jones-type relative index cannot both be defined and detect the compressor defect on the unbounded-multiplicity Kazhdan sector
distinct_from:
  bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect: that shows Kazhdan-projection sizes are blind on the bounded-multiplicity sector H_b, where sigma(G) lies in the closure of T.sigma(N); this treats the complementary sector H_inf and shows the one surviving-shape candidate there, a Jones-type quantized relative index, is either undefined or unquantized.
  finite-orbit-indices-miss-twists-without-finite-quotients: that shows finite-orbit (integer) indices are blind because the defect witness has no finite quotients; this shows the infinite-orbit replacement proposed for H_inf, a Jones subfactor index, has no quantization to exploit.
artifacts:
  - research/artifacts/rnorm-jones-index-2026-09-12.md
---

**ESTABLISHED** (route `jones-index-blind-on-unbounded-defect-sector-proof`).
Not independently reviewed. This is a no-go: it establishes no root, and
`nonsofic-hyperbolic-group` stays OPEN.

Setting of `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`:
`sigma : G -> S_U` a sofic model of the hyperbolic Leavitt cover
`1 -> N -> G -> R^x -> 1`, Koopman on `H`, block invariance putting the block
algebra `A` in the commutant of `sigma(G)`. Decompose `H = H_b (+) H_wm (+) H_inf`
as there. On `H_inf`, for a finite-dimensional irreducible `rho` of `N` of
unbounded multiplicity over `A`, let `W_rho` be the projective representation of
`Q = R^x` from `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`,
let `A_rho` be its abelian commutant piece, and put

```text
P  = fixed-space projection of  W_rho(EL_alpha(R)),
P' = W_rho(u)^* P W_rho(u) = fixed-space projection of  W_rho(u^-1 EL_alpha(R) u),
```

with `u` the defect compressor. `P` and `P'` are unitarily conjugate and nested,
and the surviving-shape proposal (recorded on
`relative-normalization-modulo-kazhdan-kernel`) is a quantized relative index
`[P : P'] in {4 cos^2(pi/n)} U [4, infinity)` forced to `1` by an
almost-invariance bound below `2`.

**Statement.** No such index exists that is simultaneously (a) defined and
(b) sensitive to `u`. Precisely:

1. **No quantization.** The inclusion cut out by `(P', P)` has diffuse relative
   commutant, since unbounded multiplicity over `A` means `A_rho` is diffuse. It
   is therefore not a subfactor inclusion, so Jones' quantization theorem does
   not apply. Any conditional-expectation (Pimsner--Popa) relative index of a
   non-factor inclusion ranges over all of `[1, infinity)`; in particular it has
   **no gap in `(1, 2)`**, so an almost-invariance bound "index `< 2`" does not
   force index `1`.
2. **No finite trace to normalize.** In a trace-zero model the ambient algebra
   `{W_rho(Q), A_rho}''` carries no finite trace with `tau(P), tau(P') in (0, infinity)`:
   both fixed projections of the infinite group `W_rho(Q)` have canonical
   dimension `0` or `infinity`. So a coupling/relative-von-Neumann-dimension
   index `[P : P']` is the indeterminate `0/0` or `infinity/infinity`.
3. **Dichotomy.** Quantization of a relative index requires a subfactor, i.e.
   trivial relative commutant, i.e. bounded multiplicity over `A` -- exactly the
   sector `H_b`, where `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`
   already proves blindness. The defect survives only on `H_inf`, where the
   relative commutant is diffuse and no quantization exists. **Jones
   quantization and the surviving defect are mutually exclusive sectors.**

**Red-flag check.** This is an obstruction to a method, not a nonsoficity
argument. It does not use soficity of `G`, proves nothing about Thompson's `V`,
and establishes no root. The diffuse relative commutant on `H_inf` traces to the
defect witness `A = <eps_u^k(V_1000)>` being infinite with a strict
self-embedding, which forces unbounded multiplicity.

## Attempts

- **Could (T) supply the missing subfactor?** No. A median/(T) argument that
  trivialized `A_rho` on the relevant piece would put that piece in `H_b`
  (bounded multiplicity), where the datum is already blind. (T) cannot both keep
  the analysis on `H_inf` (diffuse commutant, where the defect lives) and produce
  a factor (trivial commutant, needed for quantization). This is item 3.
- **Kosaki/Longo type-III index?** Same obstruction: the Kosaki--Longo index is
  quantized only for subfactors; with diffuse relative commutant it is
  continuous, and in a trace-zero model there is no finite normal state making
  the minimal expectation's index finite and sensitive.
- **What any working size must instead do.** Detect a strict inclusion of
  unitarily conjugate infinite-multiplicity `A_rho`-modules without a trace and
  without quantization -- i.e. a genuinely new invariant of the pair
  `(W_rho(EL_alpha), A_rho)` that is monotone under the compressor and that no
  strict self-embedding preserves. None is constructed. **This is where it
  stops.**
