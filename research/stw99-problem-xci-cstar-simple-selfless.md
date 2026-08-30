---
rg: 2
id: stw99-problem-xci-cstar-simple-selfless
kind: claim
title: The reduced C*-algebra of every C*-simple group is selfless (STW Problem XCI)
root: true
distinct_from:
  stw99-problem-xc-cstar-simple-strict-comparison: that asks for strict comparison; this asks for Robert's selflessness, which implies strict comparison (Robert, Theorem 3.1) and is the refinement STW record as Problem XCI.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

**Problem XCI of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026)** (Robert).  Is `C*_r(F₂)` selfless?  If `G` is a
countable discrete C\*-simple group, is `C*_r(G)` selfless?

Selflessness (Robert, *Selfless C\*-algebras*, Definition 2.1): `(A, τ)` is
selfless when `A != C`, `τ` has faithful GNS representation, and the
first-factor embedding

```text
i_1:(A,τ) -> (A,τ) * (A,τ)
```

is existential.  Equivalently, for some ultrafilter `ω` there is a
trace-preserving embedding `σ:(A,τ)*(A,τ) -> (A^ω,τ^ω)` with
`σ i_1=Δ_A`; Robert's Theorem 2.6 gives the analogous equivalent formulation
with the infinite reduced free product.  Thus the splitting map runs **from
the free product to the ultrapower**, not conversely.  Selfless tracial
algebras are simple, have stable rank one and strict comparison, and their
trace is the unique trace and unique normalized 2-quasitrace (Robert,
Theorem 3.1).

The first part is solved: `C*_r(F_n)` is selfless for `n ≥ 2`
(Amrutam--Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2412.06031, published
in *Inventiones* 242 (2025)).  The universal C\*-simple-group question remains
open as of 30 August 2026.  Subsequent primary-source advances include
Ozawa's topologically-free extreme-boundary/PHP criterion
(arXiv:2508.07938), Vigdorovich's theorem for all nontrivial linear groups
with trivial amenable radical (arXiv:2602.10616v3), and the relative
selflessness machinery of Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert
(arXiv:2607.20361); none asserts the universal statement above.

## Attempts

- `stw91-directed-unions-of-selfless-groups` proves a local-to-global
  permanence principle and supplies new positive examples.
- `stw91-countable-free-direct-sum-is-selfless` applies it to the countable
  restricted direct sum of `F_2`, then proves this group is neither linear nor
  acylindrically hyperbolic.
- `stw91-zero-dimensional-step-amplification-preserves-selflessness` proves
  that every exact selfless group remains selfless after amplification to
  locally constant functions on any compact metrizable zero-dimensional
  space.  The proof iterates exact tensor permanence over finite clopen
  partitions and then passes to their directed union.
- `stw91-reduced-free-products-preserve-selflessness` proves that the reduced
  free product of any two selfless C*-probability spaces is selfless, without
  exactness.  It places the two factor splittings in a common Fubini
  ultrapower, verifies freeness of the factor ultrapowers, and regroups the
  resulting four free copies.  Hence free products of groups already known
  to satisfy XCI again satisfy XCI.
- `stw91-finite-subgroup-projection-obstruction` gives a concrete negative
  certificate in ordered `K_0` using averaging projections of finite
  subgroups.
