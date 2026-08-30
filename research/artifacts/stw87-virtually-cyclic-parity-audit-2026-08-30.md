---
title: STW LXXXVII virtually cyclic parity audit (2026-08-30)
---

# Result

Every free minimal zero-dimensional action of every infinite finitely
generated virtually cyclic group has crossed-product nuclear dimension
exactly one.  The result has no metrizability assumption.

# Type audit

An infinite virtually cyclic group is finite-by-`Z` or dihedral type.  The
first type has a quotient onto `Z`, so the existing PV unit-index argument
excludes dimension zero.  The second has a Bass--Serre presentation

```text
G=G_1 *_F G_2,          [G_1:F]=[G_2:F]=2
```

with all three groups finite.  This includes, but is strictly larger than,
`D_infinity=C_2*C_2`.

# Orbit-sum audit

For a pointwise free action, finite subgroup crossed products are matrix
algebras over the corresponding zero-dimensional orbit spaces.  The two
maps out of `K_0(C(K) crossed_product F)=C(K/F,Z)` sum an integer-valued
function over the two `F`-orbits in each `G_i`-orbit.  Pimsner's general
tree-action six-term sequence therefore reduces the full crossed-product
K-theory to the kernel and cokernel of `(S_1,-S_2)`.  For nonmetrizable `K`,
this follows from separable invariant subalgebras and directed-limit
continuity of amenable crossed products and K-theory.

The class `(1,-1)` is killed by two.  If it survives, `K_0` has nonzero
two-torsion.  If it vanishes, an integer-valued `f` has both orbit sums one,
and `2f-1` is a nonzero odd-valued kernel element in `K_1`.  Both alternatives
exclude local AF.  This calculation uses only the index-two geometry; no
cyclic quotient or finite-index subalgebra argument is hidden in it.

# Scope

The theorem closes the exact dimension for the full virtually cyclic class.
It does not extend automatically to higher-rank virtually nilpotent groups:
their finite-abelianization cases need not split as an index-two amalgam, and
AF-ness cannot be tested by passing to an arbitrary finite-index subgroup.
The result advances the quotient analysis for LXXXVII but does not supply a
new proof of the full uniform Roe algebra equality, which is already known
when asymptotic dimension is one.
