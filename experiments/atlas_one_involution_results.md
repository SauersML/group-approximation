# Natural-A8 atlas / one-involution red-team

Date: 2026-08-11

## Scope

This experiment tests whether the finite geometry behind the two-chart atlas
is immediately incompatible with the algebraic shape of the one-involution
FALSE endpoint.  It is deliberately a **red-team test**, not a microstate for
the group in `FALSE_MACKEY_SPLIT_COCYCLE.md`.

The distinction matters.  The program uses exact representations of the
free-product atlas source and tests only the 648 necessary centrality words
from `atlas_two_chart_search.py`.  Its commuting-conjugate test contains only
the identity and twelve chart generators.  It does not yet contain a complete
normal-generating list for the atlas kernel, an exhaustion of the group, or
the concrete radical word `s` from the Mackey/coinduced model.

Corollary 10 of `notes/FALSE_MACKEY_SPLIT_COCYCLE.md` now records that a full
one-involution construction in normalized Hilbert--Schmidt norm would already
be a final FALSE certificate.  Thus normalized-HS search is mathematically
appropriate, but the finite constraint set here is still incomplete.

## Exact eight-dimensional seed

GAP was used to convert every `GL_4(F_2)` matrix occurring in the atlas words
through the exceptional isomorphism

`GL_4(F_2) ~= A8`

and then through the natural eight-point action of `A8`.  The conversion is
stored in `atlas-a8-natural.json`; the GAP generator is
`atlas_a8_natural_export.py`.

A transvection maps to a fixed-point-free involution, hence to four disjoint
transpositions in this action.  Give opposite signs to the two points in each
2-cycle.  The resulting diagonal self-adjoint involution `T` satisfies

`S T S* = -T`

exactly.  At multiplicity `k`, the two atlas factors act by

`rho(g) tensor I_k`, `U (rho(g) tensor I_k) U*`,

while `T` is amplified by `I_k`.

For the orbit window

`B={1} union {the twelve chart generators}`, 

the program tests all 78 commutators of

`T_g=pi(g) T pi(g)*`, `g in B`.

The best inner automorphism from the earlier exhaustive 40,320-alignment scan
gives a particularly strong exact control point.  It satisfies 42 of the 54
source relations, and because both chart images are permutations, every
`T_g` in the tested window remains diagonal.  Therefore its antipodal and
orbit-commutator defects are exactly zero.

## Validation

All execution was on shared MSI node `acn116`, restricted to four cores.  No
code was built or run locally.  No MSI jobs or experiment processes remain.

The joint cyclic derivative was compared with centered finite differences.
For steps `1e-3`, `3e-4`, and `1e-4`, the absolute errors were

`2.04e-7`, `1.84e-8`, and `2.04e-9`.

The program also verifies exactly that the distinguished natural permutation
is fixed-point-free of order two and that its antipodal defect is zero.  Exact
amplification of the dimension-16 optimizer to dimension 32 reproduced all
normalized-HS statistics to floating-point precision.

## Results

The exact inner-alignment seed is already much better than the identity
alignment:

| alignment | dimension | atlas RMS | atlas max | orbit RMS | orbit max |
| --- | ---: | ---: | ---: | ---: | ---: |
| identity | 8 | 0.7817359600 | 1.4142135624 | 0 | 0 |
| best inner | 8 | 0.4681194318 | 1.4142135624 | 0 | 0 |

Bounded Riemannian searches used three starts, 500 iterations per start, and
two weighted objectives.  The best points were:

| atlas weight | dimension | atlas RMS | atlas max | orbit RMS | orbit max |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1.00 | 8 | 0.4681194318 | 1.4142135624 | 0 | 0 |
| 0.75 | 8 | 0.4681194318 | 1.4142135624 | 0 | 0 |
| 1.00 | 16 | 0.4680593715 | 1.4142831876 | 0.0057187746 | 0.0099917988 |
| 0.75 | 16 | 0.4679216052 | 1.4142336672 | 0.0056703570 | 0.0107174595 |

The best dimension-16 point is only `0.00271125` away from the amplified
inner seed in normalized Hilbert--Schmidt norm.  Operator diagnostics give

| model | atlas operator max | orbit operator max | antipodal operator defect |
| --- | ---: | ---: | ---: |
| exact dimension-8 seed | 2.0000000000 | 0 | 0 |
| best dimension-16 point | 1.9999999998 | 0.0193286491 | 0 |

## Interpretation

The finite commuting-Boolean geometry is **not** responsible for the large
atlas residual: it coexists exactly with the best classical chart alignment.
Multiplicity two has a genuine nonclassical descent direction which lowers
the atlas RMS while keeping the finite orbit window very nearly commuting.
But the improvement is only `1.98e-4`, the worst normalized-HS atlas defect
does not improve, and the worst operator defect stays at its maximal value
`2`.  This is local perturbative daylight, not evidence of convergence.

The persistent worst family is again the scalar `e/E` Steinberg--Cuntz
branch.  Blindly increasing multiplicity is therefore low yield.  The next
useful computation is a dual trace/SOS attack on that branch, after extracting
enough of the actual normal kernel to ensure that the selected polynomial
inequality targets the real atlas endpoint.

The newer coinduced-parity note also changes the direct one-involution search:
the infinite-dimensional antipodal/commuting model is already exact.  The
remaining question is matrix approximation of its crossed product, i.e. a
common-Cartan/phase-completion problem retaining the radical sign.  Future
primal work should target that explicit crossed product rather than spend
compute rediscovering the exact parity action.

## Artifacts

- `atlas_one_involution_search.py`: joint normalized-HS optimizer and operator
  diagnostics;
- `atlas_a8_natural_export.py`, `atlas-a8-natural.json`: exact GAP conversion;
- `atlas-one-involution.log`: gradient check and reproducible final metrics;
- `atlas-one-involution-operator.log`: operator-norm audit;
- `atlas-oneinv-k{1,2}-inner-w{0.75,1.0}.npy`: retained optimizer states.
