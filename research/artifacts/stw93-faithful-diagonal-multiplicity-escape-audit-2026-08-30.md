# XCIII: faithful diagonal and multiplicity-escape audit

## Question tested

The rank-one matrix-ultraproduct no-go for abstract central commutator
lifting uses a defining algebra containing its trace-zero projection.  Its
diagonal trace is therefore not faithful.  The actual XCIII diagonal

```text
A=C*_r(F_2) tensor Z
```

is faithfully traced, and the `L(F_2)` tensor factor supplies a uniform
adjoint `L^2` spectral gap.  The first test was whether these two facts force
the norm trace kernel of a relative commutant to disappear.

They do not.  Start with any faithful MF embedding into a norm matrix
ultraproduct and amplify its `k`-th coordinate by a multiplicity `m_k` tending
to infinity.  A rank-one projection in the multiplicity coordinate commutes
exactly with the diagonal, has operator norm one, and has normalized trace
`1/m_k`.  It therefore survives in the norm ultraproduct but vanishes in the
tracial ultraproduct.  The pullback trace on the diagonal is unchanged, as is
its GNS von Neumann algebra and every spectral-gap inequality there.

For `C*_r(F_2) tensor Z`, MF follows from the matrix models for the reduced
free-group algebra together with nuclear quasidiagonality of `Z`.  The
pullback of the ambient ultraproduct trace is the unique faithful trace, and
the GNS algebra remains `L(F_2) tensor_bar R`.  Thus this is a literal model
of the two proposed extra inputs, not the trace-unfaithful defect of the
earlier rank-one construction.

## Why it is not a negative XCIII model

The multiplicity projection has arbitrarily many orthogonal equivalent
copies in the relative commutant.  Every bounded trace must therefore give
it value zero.  Equivalently, this projection already lies in the closed
self-commutator space of the relative commutant.  Amplification creates the
norm trace kernel and simultaneously supplies the central directions that
make it tracially invisible.

This separates three statements which should not be conflated:

1. faithful diagonal plus full-factor spectral gap does **not** imply that
   norm-central trace-zero classes vanish;
2. those inputs do not by themselves convert `2`-norm estimates into norm
   estimates on the trace kernel; but
3. the standard amplified classes are harmless because they have
   multiplicity escape.

The remaining negative-witness geometry is now sharper.  A positive
`h in J_tau intersect D` detected by a bounded trace cannot have arbitrarily
many orthogonal Cuntz-equivalent copies inside `D`.  A successful positive
XCIII proof could therefore aim to establish such central divisibility for
every trace-kernel element.  A counterexample must instead construct a
trace-zero element which is finite from the relative-commutant viewpoint,
despite the faithful diagonal and free-factor spectral gap.

This can be made quantitative without projections.  For `a in D_+`, put

```text
cap_D(a)=sup{n:n[a]<=[1] in Cu(D)}.
```

If a bounded trace charges `h`, then it charges `(h-epsilon)_+` for some
`epsilon>0`; its dimension function bounds `cap_D((h-epsilon)_+)` by the
reciprocal of the support mass.  Therefore a genuine negative XCIII witness
has a spectral cut of finite central Cuntz capacity.  Conversely, proving
infinite capacity for every positive spectral cut in the kernel would settle
ordinary trace uniqueness.  This is the precise projection-free form of
the multiplicity-escape hinge.

## Trust boundary

No property-(SI), unique-trace, or unique-quasitrace conclusion is drawn for
the actual central sequence algebra.  The construction concerns faithful MF
diagonals in norm matrix ultraproducts and proves an exact limitation of the
spectral-gap strategy.  It does not identify the actual diagonal
`A -> A_omega`, nor does it produce a trace charging the displayed kernel
projection.
