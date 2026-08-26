---
rg: 2
id: kt-compression-fixed-tracial-states-are-atomic-or-regular
kind: claim
title: Every tracial state of the Kun--Thom subgroup fixed by all compression endomorphisms is a mixture of finite-dimensional characters and a trace supported on the center
distinct_from:
  model-characters-of-compressed-pairs-are-compression-invariant: that establishes that model characters are compression-fixed; this asks to classify the compression-fixed tracial states, a question about the subgroup alone.
  kazhdan-generated-amenable-algebra-is-atomic: that classifies characters with amenable GNS algebra (atomic ones); this asks about all compression-fixed tracial states, whose GNS algebras may be non-amenable.
---

OPEN.  Let `Gamma = EL_r(F_q[x_1..x_d])`, `r, d >= 3`, with the compression
endomorphisms `phi_A(g) = A g A^(-1)` for non-negative `A in SL_d(Z)` (monomial
substitution `x^v |-> x^(A v)`).

**Claim.**  Every tracial state `chi` of `C^*(Gamma)` with `chi o phi_A = chi`
for all non-negative `A` is of the form `sum_i lambda_i chi_i + lambda_infty
chi_Z`, with `chi_i` normalized characters of finite-dimensional
representations and `chi_Z` supported on the finite center.

**Consequence if established.**  Combined with
`model-characters-of-compressed-pairs-are-compression-invariant`,
`finite-dimensional-gamma-part-of-a-model-is-compression-blind` and
`tempered-gamma-part-of-a-model-is-compressor-invariant`, the remainder
corner of every model of the Kun--Thom pair would be empty, and the
abstract-embedding formulation of hyperlinearity of `W`, `E` and `D` would
reduce exactly to the canonical regular-character formulation: the abstract
lens would add nothing, and `hyperlinear-wreath-model` would be known to be
equivalent to its Connes-embeddability form even after the trace conditions
are dropped.  Refuted, it would exhibit the only place a non-canonical
hyperlinear model could live.

## Attempts

- **Finite-dimensional fixed points are plentiful, and all blind.**  For a
  cofinite ideal `I` with `phi_A^(-1)(I) = I` for every non-negative `A` --
  for instance `I_N = (x_1^N - 1, ..., x_d^N - 1)`, invariant because each
  `A` acts on `R_+/I_N = F_q[(Z/N)^d]` by a ring automorphism -- the regular
  character of the finite quotient `EL_r(R_+/I)` is fixed, since `phi_A`
  descends to an automorphism of that finite group.  Every maximal ideal of
  `R_+` lies over a torsion point of `(bar F_q)^d`, whose orbit under the
  monomial substitutions is finite, so invariant cofinite ideals exist at
  every torsion point; the augmentation ideal is only the simplest case.
  These fixed points are exactly the characters of finite-quotient models,
  in which the image of `Gamma` is normal and compression is invisible
  (`finite-quotient-blindness`), consistent with
  `atomic-tracial-algebra-endomorphisms-are-automorphisms`.  A single
  irreducible character is fixed only if the induced automorphism fixes its
  class; mixtures over automorphism orbits always are.
- **Regular-type fixed points.**  `delta_e` and every `chi_Z` are fixed.  A
  pulled-back regular character `1_N` of an infinite quotient `Gamma/N` is
  fixed iff `phi_A^(-1)(N) = N` for all `A`; for `N = E_r(R_+, I)` this needs
  a substitution-invariant ideal `I` with `R_+/I` infinite.  None is known:
  the powers of the augmentation ideal and the ideal of the coordinate
  hyperplane arrangement are both moved by a transvection substitution.  In
  any case such an `N` is not in the finite core, so it cannot arise from a
  model in criterion form
  (`model-characters-of-compressed-pairs-are-compression-invariant`, (2)).
- **General characters.**  `Gamma` is not a lattice for `d >= 2`, so the
  Bekka / Peterson / Bader--Boutonnet--Houdayer--Peterson character rigidity
  theorems do not apply; a proof would have to use the compression
  invariance itself, e.g. that `chi` extends to a trace-preserving
  endomorphism `theta_A` of its GNS algebra `P_chi` with
  `theta_A(P_chi) = pi_chi(A Gamma A^(-1))''`, and that property (T) of the
  subgroup `A Gamma A^(-1)` is inherited.  No argument is recorded beyond
  the atomic case.
