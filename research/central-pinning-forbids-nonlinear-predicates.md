---
rg: 2
id: central-pinning-forbids-nonlinear-predicates
kind: claim
title: A finite group with a unique J equals minus one irreducible can pin only affine joint spectra on commuting involutions
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  finite-predicate-signed-permutation-sector: that exhibits a finite group with an irreducible sector carrying an arbitrary nonlinear predicate; this proves that such a sector is never the unique sector of its central character, so it cannot be selected by pinning the central involution.
  regular-trace-blocks-exact-local-predicate-return: that kills exact predicate returns by evaluating in the regular representation of the ambient group; this is finite-group character theory and says which predicates a central character can pin in every representation.
---

Let `H` be a finite group and `J in Z(H)` an involution such that exactly
one irreducible representation `pi` satisfies `pi(J)=-I`.  Then

```text
chi_pi(h)=0  for h notin {1,J},        (dim pi)^2=|H|/2.          (CP1)
```

Consequently, for commuting involutions `x_1,...,x_k in H` generating `E`,
the joint spectrum of `(pi(x_1),...,pi(x_k))` is an **affine subspace** of
`F_2^k`: all characters of `E`, each with multiplicity `dim pi/|E|`, if
`J notin E`; the characters with `lambda(J)=-1`, each with multiplicity
`2 dim pi/|E|`, if `J in E`.  The same holds in every finite-dimensional
representation of any `Gamma>=H` in which `J` acts as `-I`, since it is a
multiple of `pi`.

*Proof.*  The `(1-J)/2` summand of `C[H]` has dimension `|H|/2` and equals
`M_(dim pi)` by uniqueness, giving the dimension identity; character
orthogonality `|H|=sum_h|chi_pi(h)|^2>=2(dim pi)^2=|H|` forces the character
to vanish off `{1,J}`.  The multiplicity of `lambda` in `pi|_E` is
`(1/|E|)sum_(e in E)chi_pi(e)conj(lambda(e))`, to which only `e=1` and
possibly `e=J` contribute.

**Consequence for compilers.**  The robustness of the Pauli and Clifford
compilers comes from central pinning: an approximate representation with
`J` near `-I` on positive density is near a multiple of the unique sector.
This claim shows that design can enforce only linear (XOR) constraints on
commuting involutions.  The nonlinear predicate sector `pi_S` of
`finite-predicate-signed-permutation-sector` always coexists with other
irreducibles of the same central character, and no central element
prefers it.  Sector selection for nonlinear predicates therefore needs a
finite-dimension-specific mechanism, and by
`regular-trace-blocks-exact-local-predicate-return` not an exact identity.
This is the group-theoretic reason exact groupification of a nonlinear
BCS (`bcs-to-lcs-exact-support-gap`) is hard while LCS solution groups are
immediate, and the reason the Taller--Vidick reduction goes through 3-XOR
with a noisy long code.
