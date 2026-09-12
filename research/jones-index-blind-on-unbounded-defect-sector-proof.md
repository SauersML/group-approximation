---
rg: 2
id: jones-index-blind-on-unbounded-defect-sector-proof
kind: route
title: A diffuse relative commutant defeats Jones quantization, and trace-zero kills relative dimension, on the defect sector
target: jones-index-blind-on-unbounded-defect-sector
requires:
  - bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect
  - kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure
artifacts:
  - research/artifacts/rnorm-jones-index-2026-09-12.md
---

Complete proof: artifact Sections 2--4.

**Inputs.** From `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`,
on the isotypic sector `V_rho (x) W_rho` the ambient von Neumann algebra commuting
with `sigma(N)` is `1 (x) A_rho`, and `sigma(G)` acts as `(closure of T.rho(N)) (x) W_rho`
with `W_rho` a projective representation of `Q = R^x`. By the definition of the
unbounded-multiplicity sector `H_inf` in
`bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`, `A_rho` has no
minimal projections there: it is **diffuse**.

**Step 1 (no quantization; artifact Section 2).** `P` and `P' = W_rho(u)^* P W_rho(u)`
are the fixed projections of `W_rho(EL_alpha(R))` and its `u`-conjugate. Consider
any conditional expectation `E` onto the smaller and its Pimsner--Popa index
`Ind(E) = inf{lambda^-1 : E(x) >= lambda x, x >= 0}`. Jones' index theorem
restricts `[M:N]` to `{4 cos^2(pi/n)} U [4, infinity)` only when `N <= M` are
II_1 **factors**. Here the relative commutant contains the diffuse `A_rho`, so
the inclusion is not factor--factor; standard non-factor inclusions realize a
continuum of index values (e.g. a direct integral / weighted diagonal over the
spectrum of `A_rho` gives `Ind(E) = int f dmu` for any measurable weight `f >= 1`).
Hence `Ind` takes every value in `[1, infinity)` and there is no gap in `(1,2)`.
An almost-invariance bound `Ind < 2` therefore does not force `Ind = 1`.

**Step 2 (no finite trace; artifact Section 3).** The model is trace-zero: the
ultraproduct trace is `tau(sigma(g)) = lim #Fix(sigma_n(g))/|X_n|`, which is `0`
for every `g` of infinite conjugacy class. On `{W_rho(Q), A_rho}''` a finite
trace `tau` would give the fixed projection `P` of the infinite group
`W_rho(EL_alpha(R))` the value `tau(P) = tau` of the projection onto invariant
vectors of an infinite group with no finite-dimensional summand at that sector,
which is `0`; and off `H_b` there is no finite-multiplicity piece to carry a
positive value. So `[P:P'] = tau(P)/tau(P')` is `0/0` (or `infinity/infinity` for
a semifinite trace, since a semifinite trace assigns `infinity` to these
projections). The relative von Neumann dimension is indeterminate.

**Step 3 (dichotomy; artifact Section 4).** A relative index is quantized iff the
inclusion is (essentially) a subfactor, i.e. its relative commutant is trivial,
i.e. `A_rho = C` on the sector, i.e. bounded multiplicity over `A`. That is the
sector `H_b`, where `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`
proves every such datum is blind: `sigma(G)`, `sigma(Gamma_hat)` and every
compressed image lie in the strong closure of `T.sigma(N)`, so `P = P'` there and
the index is trivially `1` for a reason unrelated to the defect. The defect
`W_rho(u) P W_rho(u)^* != P` survives only where `A_rho` is diffuse, i.e. `H_inf`,
where Steps 1--2 apply. So no sector admits a quantized index that detects the
defect.

**Literature (standard, not re-read from source here):** V. Jones, *Index for
subfactors*, Invent. Math. 72 (1983) -- quantization for II_1 subfactors;
Pimsner--Popa, *Entropy and index for subalgebras*, Ann. Sci. ENS 19 (1986) --
the expectation index and its behaviour for non-factor inclusions; Kosaki, *Extension
of Jones' theory to arbitrary factors*, J. Funct. Anal. 66 (1986). These are used
only as the standard quantization-requires-factors facts.

**No root established.** The target is a blindness statement; `cairn why` must
show `nonsofic-hyperbolic-group` and `relative-normalization-modulo-kazhdan-kernel`
OPEN.
