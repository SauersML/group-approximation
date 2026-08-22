# Popa compactness audit for the scalar Gao carrier

Date: 2026-08-21

## Primary inputs and their actual hypotheses

Gao, *Relative Embeddability of von Neumann Algebras and Amalgamated Free
Products*, arXiv:2012.07940v3, Definition 2.2 and Proposition 2.2:
<https://arxiv.org/html/2012.07940>.

After Gao Proposition 2.2 removes the QWEP coefficient factor, a hypothetical
SL3 witness has the form

```text
P=L(SL_3(Z)) subset M=L(SL_3(Z[1/2])) -> calA=prod_omega A_k,
P subset calB=prod_omega B_k,
```

where `A_k` are finite QWEP algebras, `B_k subset A_k` are hyperfinite, and
the square is commuting.  There is no remaining `1 tensor P` coefficient
leg into which one could conjugate a corner.

Popa, *On a class of type II_1 factors with Betti numbers invariants*,
Annals of Mathematics 163 (2006), Proposition 3.1 and Theorem 5.4:
<https://annals.math.princeton.edu/2006/163-3/p03>.

The rigidity-versus-Haagerup argument requires completely positive maps on
one ambient algebra which converge pointwise to the identity and are compact
relative to a fixed base.  Property `(T)` upgrades their convergence on the
rigid subalgebra to uniform convergence.  It does not manufacture the
compact maps.

Popa's intertwining-by-bimodules criterion (originally Popa 2001/2003; see
the equivalent conditions collected in Theorem 17.1.1 of the UCLA II_1
factor notes) identifies the exact analytic datum: finite-right-module
mass in the basic construction, equivalently failure of a mixing net as in
`(GPC1)`.  Hyperfiniteness of each coordinate is not this datum.

## Exact rank-escape obstruction

Because `SL_3(Z)` is residually finite, its group factor embeds
trace-preservingly into a tracial ultraproduct of matrix algebras.  Thus an
ultraproduct of finite-dimensional, hence hyperfinite, coordinates can
contain the diffuse property-`(T)` factor `P`.

Let `D_k subset B_k` be finite-dimensional approximants to representing
sequences for a fixed generating set of `P`.  If

```text
max_generator ||x_k-E_(D_k)(x_k)||_2 ->_omega 0
```

and `dim(D_k)` were bounded on an omega-large set, the ultraproduct of the
`D_k` would be finite dimensional and would contain all generators, hence
all of `P`.  This is impossible.  Therefore `dim(D_k)->_omega infinity` for
every asymptotically exact choice.

This divergence is precisely why the coordinate expectations do not induce
a compact operator on the ultraproduct `L^2` space.  A successful Popa lane
must prove new arithmetic tightness -- a uniform compact deformation or an
equivalent finite-basic-construction mass estimate -- from the simultaneous
Hecke correspondences.  Coordinate hyperfiniteness, QWEP, property `(T)`,
and the relative-Haar word do not provide it separately.

## Dyadic word boundary

The separate Cairn theorem
`gao-re-witness-carries-orthogonal-arithmetic-hecke-tower` already records
that the dyadic element is orthogonal to the carrier while generating
bifinite `P-P` Hecke correspondences.  This is compatible, not contradictory,
with Popa intertwining: the source correspondence
`closure(P lambda(h) P)` is itself bifinite because `h` commensurates
`SL_3(Z)`.  Thus even a positive-corner intertwiner would not make
`E_P(lambda(h))=0` impossible; one would still need a theorem excluding the
nontrivial Hecke sector.
