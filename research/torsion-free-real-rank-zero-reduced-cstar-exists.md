---
rg: 2
id: torsion-free-real-rank-zero-reduced-cstar-exists
kind: claim
title: Some countable torsion-free group has a reduced group C*-algebra of real rank zero
distinct_from:
  kadison-kaplansky-counterexample-exists: that asks for one nontrivial projection; this asks for real rank zero, the dense case of the trichotomy, which forces projections of all traces in a dense set.
  torsion-free-matrix-trace-defect-exists: that asks for any non-integer K_0 trace; this is equivalent to a non-discrete K_0 trace image, excluding the bounded-denominator case.
---

**OPEN.** There is a countable torsion-free group `Λ` with `RR(C*_r Λ) = 0`: invertible self-adjoint
elements are dense among self-adjoint elements of `C*_r(Λ)`.

**Equivalent form.** By `torsion-free-trace-defects-are-discrete-or-real-rank-zero`, this holds iff some
countable torsion-free `G` has a dense `K_0` trace image `τ_*(K_0(C*_r G))`, for example one containing an
irrational number. The witness is then `Λ = G * Z`.

**Refutes the root.** Route `kk-counterexample-via-real-rank-zero-host`.

## Attempts

- **Where it cannot live.** A torsion-free `Λ` for which `C*_r(Λ)` is known to have no nontrivial projection
  is excluded. This covers groups with surjective assembly (`assembly-image-traces-are-integral-for-torsion-free-groups`):
  a-T-menable groups, hyperbolic groups and real-rank-one lattices. It also covers torsion-free discrete
  subgroups of reductive Lie groups with property (RD) (`unconditional-spectra-of-kk-witnesses-cross-the-gap`,
  item 6), and free products of groups with integral `K_0` traces
  (`reduced-free-product-k0-generated-by-factor-images`).
- **Irrational trace sources.** Main records none over torsion-free groups. Four shapes would give one:
  - a higher Kazhdan projection with irrational `β^n_(2)` (`reduced-higher-kazhdan-projection-kk-witness`);
  - a lattice-transfer complex with a Laplacian gap (`complex-with-irrational-and-torsion-free-lattices`);
  - a scalar unitary commutator `exp(2πiθ)` with `θ` irrational
    (`scalar-unitary-commutators-force-k0-trace-values`);
  - any gapped self-adjoint matrix over `Z[i][G]` with irrational trace below the gap.
- **Arithmetic case excluded.** A defect with bounded denominators, `S = (1/m)Z` with `m >= 2`, refutes the
  root but does not give real rank zero on `G * Z`.
- **Literature (bounded check, three web searches on 2026-09-12).** The real-rank-zero literature for group
  C\*-algebras treats amenable groups.
  - Moutzouris (arXiv:2306.07231, abstract) calls it an open problem whether a discrete amenable group with
    real-rank-zero `C*(G)` must be locally finite. He proves that elementary amenable normal subgroups of
    finite Hirsch length are then locally finite.
  - Torsion-free amenable groups are excluded here anyway, since they satisfy Baum--Connes.
  - Nothing was found on reduced algebras of non-amenable torsion-free groups.
  - Dykema--Rørdam II gives real rank zero for infinite reduced free products with dense trace image, all of
    whose known group instances have torsion.
- **Analogy.** Robert (arXiv:2309.14188v3, introduction) proposes selfless algebras of real rank zero as
  C\*-analogues of II_1 factors. A witness here would be such an analogue coming from a torsion-free group.
