---
rg: 2
id: primitive-packet-corner-is-matrix-over-hecke-atom
kind: claim
title: A primitive packet corner is a full matrix algebra over one rank-one Hecke atom
distinct_from:
  piecewise-group-transport-gives-corner-unitaries: that constructs corner unitaries from group-conjugate projection pieces; this classifies every algebraic unitary normalizing the packet diagonal, including pieces not represented by individual group elements.
  free-phase-context-escape-criterion: that gives the collision criterion and an explicit free-phase escape; this identifies the complete ambient algebra of all marginal-fixing unitaries and shows exactly where its escaped coefficients live.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that classifies finite type-changing paths and their projective multiplicity gauges; this is an exact Morita normal form inside one primitive type for arbitrary finite-support Hecke coefficients.
  uncoupled-spectator-cannot-create-first-chord: that computes the special tensor product `M_D(C) tensor C[H]`; this works for an arbitrary group containing the finite packet, where the rank-one Hecke algebra need not be a tensor spectator or a group algebra.
  finite-normal-type-corner-is-twisted-group-algebra: that assumes the finite packet is normal and identifies the rank-one coefficient algebra as a twisted quotient-group algebra with its trace; this needs no normality and instead classifies diagonal normalizers and marginal commutants over the arbitrary Hecke atom.
---

Let `Gamma` contain a finite subgroup `K`, let `p in C[K]` be the primitive
central projection of an irreducible `K`-type of dimension `D`, and choose
matrix units

```text
(E_ij)_(1<=i,j<=D) in p C[K] p,       e=E_11.             (PMH1)
```

Put

```text
H=e C[Gamma] e.                                            (PMH2)
```

Then there is an explicit unital star-algebra isomorphism

```text
Phi:p C[Gamma] p -> M_D(H),
Phi(x)_ij=E_(1i) x E_(j1),                                (PMH3)
```

with inverse

```text
Psi((a_ij))=sum_(i,j) E_(i1) a_ij E_(1j).                 (PMH4)
```

It sends the finite root block `pC[K]p` to the scalar matrix algebra
`M_D(Ce)`.  In particular, if `q=sum_(i in I)E_ii`, then

```text
q C[Gamma] q isomorphic to M_|I|(H),
q C[K] q isomorphic to M_|I|(Ce).                         (PMH5)
```

## Full-diagonal normalizers

Let

```text
D_I=direct_sum_(i in I) C E_ii.                           (PMH6)
```

An algebraic corner unitary `U in qC[Gamma]q` normalizes `D_I` if and only
if there are a permutation `sigma in Sym(I)` and unitaries `h_i in H` such
that `Phi(U)` is the Hecke-monomial matrix

```text
Phi(U)_(sigma(i),i)=h_i,          all other entries zero. (PMH7)
```

Indeed, conjugation by `U` must permute the minimal projections `E_ii` of
the finite-dimensional algebra `D_I`.  The sole nonzero block in column `i`
is

```text
h_i=E_(1,sigma(i)) U E_(i1),                              (PMH8)
```

and `U^*U=UU^*=q` says `h_i^*h_i=h_ih_i^*=e`.  Conversely `(PMH7)` is
unitary and implements `sigma`.

Thus non-scalar rank-one Hecke units can give a finite-support normalizer
outside the root block, but they are **pure gauges** on the full context
MASA: conjugation still only permutes its original atoms.  Such a normalizer
cannot create an escaped context partition.

## Marginal commutants

Let `d_1,...,d_r in D_I` be diagonal signs.  Partition `I` into their joint
sign fibers

```text
I_omega={i:(d_1(i),...,d_r(i))=omega}.                    (PMH9)
```

The complete algebraic commutant inside the corner is

```text
q C[Gamma]q intersect {d_1,...,d_r}'
   isomorphic to direct_sum_omega M_|I_omega|(H).         (PMH10)
```

This follows entrywise from `(PMH3)`: an `(i,j)` coefficient commutes with
every scalar diagonal sign exactly when `i,j` have the same joint pattern.
Consequently every algebraic unitary fixing the selected marginals is one
arbitrary unitary matrix over `H` on each collision fiber, and there are no
other degrees of freedom.

There is an equally explicit normalizer statement.  Put

```text
f_omega=sum_(i in I_omega)E_ii,
A_S=direct_sum_omega C f_omega.                           (PMH11)
```

If `U A_S U^*=A_S`, then `U` permutes the nonzero `f_omega`.  Canonical
trace invariance forces

```text
|I_(sigma(omega))|=|I_omega|,                            (PMH12)
```

and, after ordering the fibers, `Phi(U)` has exactly one nonzero block in
each block row and column, that block being a unitary in
`M_|I_omega|(H)`.  Conversely every such Hecke-block-monomial matrix
normalizes `A_S`.  Literal oriented shared-marginal equality is the special
case in which the fiber permutation is trivial, hence exactly `(PMH10)`.

If the selected marginals separate the context coordinates, every
`I_omega` is a singleton.  Then `(PMH10)` is diagonal, every such unitary
fixes every `E_ii`, and **no** finite-support multi-piece corner unitary can
move the context partition.  If a fiber has size at least two, its matrix
algebra over `H` is the sole possible location of block escape.  The known
Hadamard/free-phase cell is one explicit unitary in such a block; any future
cycle-closing construction must instead solve its coupled equations in
these same rank-one-Hecke matrix blocks.

This is not a general no-go for the signed-Hecke route.  It reduces that
route exactly: after the finite packet coordinates are stripped off, all
genuinely new holonomy is carried by the algebraic unitary groups
`U(M_m(H))` of the collision fibers.  Adding literal packet normalizers or
more finite matrix coordinates cannot enlarge this list.
