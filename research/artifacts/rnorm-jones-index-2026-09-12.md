# The Jones-index surviving shape for RNORM is dead

Date: 2026-09-12. Lane `rnorm-jones-index` (swarm 7).

- **Target:** the surviving shape recorded on
  `relative-normalization-modulo-kazhdan-kernel` and in
  `rnorm-kazhdan-projection-sizes-2026-09-12.md` Section 4: a quantized Jones-type
  relative index on the unbounded-multiplicity Kazhdan sector `H_inf`, forced to
  `1` by an almost-invariance bound below `2`.
- **Outcome:** no such index exists. Landed as
  `jones-index-blind-on-unbounded-defect-sector`. RNORM and
  `nonsofic-hyperbolic-group` stay OPEN.

## 1. What was proposed

On `H_inf` the position of `Gamma_hat = EL_alpha(R)` is genuine data: `P` (fixed
space of `W_rho(Gamma_hat)`) and `P' = W_rho(u)^* P W_rho(u)` are unitarily
conjugate and nested, with strict inclusion allowed at infinite multiplicity. The
proposal was to read a Jones index `[P:P'] in {4 cos^2(pi/n)} U [4, infinity)`,
use a median/(T) argument to bound it below `2`, and conclude `= 1` (so `P = P'`,
twist trivial, normalization, RNORM). This copies Kun--Thom's integer index below
`2` on the *finite* cluster groupoid.

## 2. No quantization: the inclusion is not a subfactor

Jones' theorem quantizes `[M:N]` to `{4 cos^2(pi/n)} U [4, infinity)` **only for
II_1 factors** `N <= M`. The relevant inclusion here has relative commutant
containing `A_rho`, and on `H_inf` `A_rho` is diffuse by definition (that is what
"unbounded multiplicity over the abelian block algebra `A`" means). So it is not a
subfactor inclusion.

For a non-factor inclusion the Pimsner--Popa index
`Ind(E) = inf{ lambda^-1 : E(x) >= lambda x }` of a conditional expectation is
unrestricted: over the spectrum `(Spec A_rho, mu)` a diagonal expectation with a
measurable weight `f >= 1` has `Ind = int f dmu`, which realizes every value in
`[1, infinity)`. Concretely there is no gap in `(1,2)`. Therefore the crucial
step of the proposal -- "bound below `2` forces `= 1`" -- has nothing to bite on.

This is the exact point where the analogy with Kun--Thom breaks. Their index was
a ratio of **finite cardinalities** (orbit and isotropy sizes of a finite
groupoid), landing in the integers, where "below `2`" does force `1`. Replacing
finite cardinalities by an operator-algebra index only restores a gap when the
inclusion is a subfactor.

## 3. No finite trace: relative dimension is indeterminate

The alternative reading of `[P:P']` is a ratio of von Neumann dimensions. In a
trace-zero sofic model the canonical trace `tau(sigma(g)) = lim #Fix/|X_n|`
vanishes on every infinite-conjugacy-class element. The fixed projections `P, P'`
of the infinite group `W_rho(Gamma_hat)` on `H_inf` carry no finite-dimensional
summand there, so a finite trace gives `tau(P) = tau(P') = 0`, and a semifinite
trace gives `+infinity`. Either way `[P:P'] = tau(P)/tau(P')` is indeterminate.
`W_rho(R^x)''` has no evident finite trace, as already noted on the crux node.

## 4. The dichotomy: quantization and the defect are disjoint sectors

Combine Sections 2--3 with `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`:

| sector | relative commutant `A_rho` | quantized index? | defect visible? |
|---|---|---|---|
| `H_b` (bounded mult.) | trivial (subfactor) | yes | **no** -- Theorem B: `P = P'`, `sigma(G)` in closure of `T.sigma(N)` |
| `H_wm` (weakly mixing) | -- | -- | no -- all Kazhdan projections vanish |
| `H_inf` (unbounded mult.) | diffuse | **no** (Sec. 2--3) | yes, but unquantized |

A relative index is Jones-quantized iff the inclusion is a subfactor iff the
relative commutant is trivial iff multiplicity is bounded -- which is precisely
the sector `H_b` where the datum is provably blind. The defect survives only on
`H_inf`, where quantization fails. So **no sector supports a quantized index that
sees the defect.** (T) cannot rescue this: trivializing `A_rho` to make a factor
moves the analysis into `H_b`.

## 5. What survives

Any working size on `H_inf` must detect a strict inclusion `P' subsetneq P` of
unitarily conjugate, infinite-multiplicity `A_rho`-modules **without a trace and
without quantization**: a monotone invariant of the pair
`(W_rho(EL_alpha(R)), A_rho)` under the compressor `u` that no strict
self-embedding of the defect witness `A = <eps_u^k(V_1000)>` can preserve. This is
the same barrier reached by every prior RNORM lane, now sharpened to say why the
one operator-algebraic candidate (a Jones index) cannot be it. None is
constructed. **This is where it stops.**

## 6. Red-flag check

The obstruction uses only the structure of `H_inf` (diffuse `A_rho`) and
trace-zero; it does not use soficity of `G`, holds whether or not `G` is sofic,
and proves nothing about `V`. The diffuse relative commutant itself comes from the
defect witness being infinite (Thompson's `V` inside `A`, strict self-embedding
`eps_u`), which is the ultimate source of unbounded multiplicity. No property (T)
is claimed to be used, because this is a no-go, not a nonsoficity proof.

Literature used as standard facts, not re-read from source in this lane: Jones
(Invent. Math. 72, 1983), Pimsner--Popa (Ann. Sci. ENS 19, 1986), Kosaki
(JFA 66, 1986).
