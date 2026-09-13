---
rg: 2
id: jones-index-blind-on-unbounded-defect-sector
kind: claim
title: A Jones-type relative index on the unbounded-multiplicity Kazhdan sector adds no leverage for RNORM, since its gap below 2 is automatic and a bound below 2 is the defect statement itself
distinct_from:
  bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect: that shows Kazhdan-projection sizes are blind on the bounded-multiplicity sector H_b; this treats the complementary sector H_inf and shows the proposed Jones-type index there equals the defect indicator, so an index bound below 2 is no weaker than exact normalization on that sector.
  finite-orbit-indices-miss-twists-without-finite-quotients: that shows finite-orbit integer indices are blind because the defect witness has no finite quotients; this shows the operator-algebraic replacement on H_inf is not blind but tautological, its only gap being free for every conditional expectation.
artifacts:
  - research/artifacts/rnorm-jones-index-2026-09-12.md
---

**ESTABLISHED** (route `jones-index-blind-on-unbounded-defect-sector-proof`).
Not independently reviewed. This is a no-leverage result. It establishes no root,
and `nonsofic-hyperbolic-group` stays OPEN.

**Correction.** The first landed version (939a37611) said two things, both now
withdrawn:
- The Pimsner--Popa index of a non-factor inclusion fills `[1, infinity)` with no
  gap in `(1,2)`. That is false: by item 1 below, every proper inclusion with a
  conditional expectation has index `>= 2`, factor or not.
- Quantization and the defect live on disjoint sectors. This dichotomy is also
  withdrawn.

The id keeps its old wording, but the content is the statement below.

Setting of `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`:
`sigma : G -> S_U` a sofic model of the hyperbolic Leavitt cover
`1 -> N -> G -> R^x -> 1`, Koopman on `H`, block invariance putting the block
algebra `A` in the commutant of `sigma(G)`, and `H = H_b (+) H_wm (+) H_inf`. On
`H_inf`, for a finite-dimensional irreducible `rho` of `N` of unbounded
multiplicity over `A`, let `W_rho` be the projective representation of `R^x` from
`kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`, and put

```text
P  = fixed-space projection of  W_rho(EL_alpha(R)),
P' = W_rho(u)^* P W_rho(u) = fixed-space projection of  W_rho(u^-1 EL_alpha(R) u),
```

with `u` the defect compressor. The two projections are unitarily conjugate and
nested; relabel so that `P' <= P`, and put `Q = P - P'`. The surviving-shape
proposal (recorded on `relative-normalization-modulo-kazhdan-kernel`) was a
quantized relative index `[P : P']`, forced to `1` by an almost-invariance bound
below `2`.

**Statement.**

1. **The gap is free.** Let `N <= M` be a unital inclusion of von Neumann algebras
   and `E : M -> N` a conditional expectation. The Pimsner--Popa index
   `Ind(E) = inf{lambda^-1 : E(x) >= lambda x for all x >= 0}` lies in
   `{1} U [2, infinity]`, and `Ind(E) = 1` iff `N = M`. No factoriality, trace,
   Jones quantization, or property (T) is used.
2. **The index is the defect indicator.** Let `M = P B(H_inf) P`,
   `N = P' M P' + Q M Q` and `E_P(x) = P'xP' + QxQ`. For `P != 0`:
   - `Ind(E_P) = 1` if `P' = P`;
   - `Ind(E_P) = 2` if `P' != P`.

   The same holds for any expectation onto a subalgebra attached to `(P, P')`
   that equals the whole algebra exactly when `P' = P`: by item 1, "index `< 2`"
   means `P' = P`.
3. **Consequence.** In the surviving shape, the step "a bound below `2` forces
   index `1`" is item 1, a tautology. The bound itself is equivalent to
   `W_rho(u)^* P W_rho(u) = P` on `H_inf`, which is the RNORM normalization on
   that sector. Jones' finer quantization `{4 cos^2(pi/n)}` in `[2,4)` is never
   used. Item 1 holds for amenable hosts too, so any (T) input has to go entirely
   into proving `P' = P`, and the index contributes nothing. This trips the lane
   brief's red flag: an index step that works for amenable hosts is a relabeling,
   not a mechanism.

**Remark (not part of the proof).** A dimension-ratio reading
`[P:P'] = tau(P)/tau(P')` needs a trace on an algebra containing `P, P'` with
`0 < tau(P) < infinity`. None has been constructed, and `W_rho(R^x)''` has no
evident finite trace in a sofic model. The first version asserted that no such
trace exists. That is not proved.

**Red-flag check.** Uses no soficity of `G`, proves nothing about Thompson's `V`,
and establishes no root.

## Attempts

- **Kun--Thom analogy.** Their step "an integer index below `2` is `1`" is the
  same free gap. The real content was the median/(T) estimate on finite clusters.
  - On `H_inf`, `A_rho` commutes with `W_rho(R^x)`: block invariance makes
    `1 (x) A_rho` commute with `U_rho (x) W_rho`.
  - So a Kun--Thom-style argument would disintegrate over `A_rho` and need
    `Q_omega = 0` fibre by fibre, which is the defect statement again.
  - Not pursued.
- **What any working mechanism must do.** Force `Q = 0` exactly on `H_inf`.
  Index theory supplies no intermediate quantity: `Ind(E_P)` jumps from `1` to
  `2` as soon as `Q != 0`, however small `Q` is. **This is where it stops.**

**Scope (2026-09-12).** `unbounded-defect-sector-vanishes-in-koopman-models`
shows that in every sofic model `H_inf = 0`, and `Q = 0` for every `rho`. So the
setting above is empty for the Leavitt cover, and `Ind(E_P) = 1` throughout.
Items 1 and 2 concern an arbitrary inclusion and an arbitrary pair `P' <= P`, and
remain true. The last Attempts bullet asks a mechanism to force `Q = 0` on
`H_inf`. That holds automatically, with no (T), and gives no leverage for RNORM.
