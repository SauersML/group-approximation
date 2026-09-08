# The rho5 split has feasible multiplicities at every exact frozen anchor

2026-09-08. Direct finite-dimensional algebra. No computation or search.

The row `rho_5` makes the parent involution a product of two prescribed
conjugates of the same involution. Its exact spectral constraints can
be solved completely. They are already feasible at every exact native
S3 anchor. This isolates the need to retain the prescribed conjugator
words; it does not solve their equations.

## 1. The actual shared occurrences

Use the shorter native compiler of the
[eight-row packet](leavitt-eight-word-exact-reduction-2026-09-08.md).
In particular

```text
gamma(X)=C X C^(-1),
d=[B_2,gamma(B_1)],       h=gamma^2(d),
a=[d,h],                 A=j=a gamma(d) a^(-1),
D=C^(-1) A C.
```

The symbol `a` is a compiler word and differs from `A`. The compiled
Thompson three-cycle is denoted `B`; it is also a fixed word in the
same source tuple. With `X^Y=Y^(-1)XY`, the two exponents in the
actual split row are

```text
E_0=B D A D A A^(B A),
E_1=B^(-1) D A D A A^(B^(-1) A),

rho_5=D^(-1) A^(E_0) A^(E_1).                       (1)
```

Assume the exact anchor

```text
C^3=I,       A^2=(AC)^2=I.                          (2)
```

Then `A,D` are self-adjoint unitaries with the same spectrum. Each
of `U=A^(E_0)` and `V=A^(E_1)` is another such involution. The row
`rho_5=I` says

```text
UV=D.                                               (3)
```

Since `(UV)^(-1)=VU` and `D^(-1)=D`, equation (3) forces `UV=VU`.
This is an exact implication; it does not depend on an additional
commutation row.

## 2. Necessary and sufficient rank criterion for the split

Let `A,D` be any fixed self-adjoint unitaries on `C^n` with the same
negative eigenspace dimension

```text
q=rank((I-A)/2)=rank(A-I)=rank((I-D)/2).              (4)
```

There exist commuting involutions `U,V`, each unitarily conjugate to
`A`, with `UV=D` if and only if

```text
q is even,       3q<=2n.                            (5)
```

For necessity, simultaneously diagonalize the commuting involutions.
Write their joint sign-space dimensions as

```text
             (+,+)   (-,+)   (+,-)   (-,-)
dimension       w       x       y       z.
```

The negative dimensions of `U,V,UV` respectively are `x+z,y+z,x+y`.
They all equal `q`, so

```text
x=y=z=q/2,       w=n-3q/2.                          (6)
```

The nonnegative integer conditions on these four dimensions are (5).

For sufficiency, keep the supplied `D` fixed. Split its negative
eigenspace into orthogonal spaces `H_10,H_01`, each of dimension
`q/2`. Inside its positive eigenspace choose `H_11` of dimension
`q/2`; this is possible because `n-q>=q/2`. Let `H_00` be the
remaining positive space. For their orthogonal projections define

```text
U=P_00-P_10+P_01-P_11,
V=P_00+P_10-P_01-P_11.                              (7)
```

These are commuting self-adjoint unitaries and

```text
UV=P_00-P_10-P_01+P_11=D.
```

Each has negative dimension `q`; classification of self-adjoint
unitaries by their two eigenspace dimensions gives unitary conjugacies
to `A`. This also covers `q=0`. No choice of a conjugating word is
made in this construction.

## 3. The native anchor already meets the criterion

Now return to the frozen source in dimension `n=24k=3m`, with
`m=8k`. Each of the three eigenspaces of `C` has dimension `m`.
The anchor relations imply

```text
A C A=C^(-1).
```

Thus `A` preserves the fixed eigenspace of `C` and exchanges its
`omega,omega^2` eigenspaces. On their direct sum, the involution has
block form `[[0,V],[V^*,0]]` for a unitary `V`; it has exactly
`m` positive and `m` negative eigenvalues. If the restriction to
the fixed eigenspace has `b` negative eigenvalues, then

```text
q=m+b,       0<=b<=m.                               (8)
```

Equivalently, in the S3 decomposition, `b` is the sign multiplicity,
`m-b` is the trivial multiplicity, and `m` is the standard multiplicity.
In particular `n/3<=q<=2n/3`, which gives the inequality in (5).

The parity condition is also supplied by the actual source. The word
`d` is a commutator of unitaries, so its determinant is one. The
compiler makes `A` a unitary conjugate of `d`:

```text
A=(a C)d(a C)^(-1),       det A=det d=1.             (9)
```

Since `A` is an involution, `det A=(-1)^q`, proving that `q` is even.
This uses the source authentication, not an extra assumption on the
abstract S3 pair.

Consequently the construction (7) is available for every actual exact
anchor, regardless of the value of the compiled `B`. Imposing the
additional exact finite anchor `B^3=(AB)^4=I` does not change this
conclusion. No assertion is needed that every numerical value permitted
by (8) is realized by a native source tuple.

## 4. What the feasible split does and does not establish

For the actual row, the two involutions must be the particular
`A^(E_0),A^(E_1)` in (1). Construction (7) supplies only two unitary
conjugates, with independently available conjugating matrices. It does
not assert that either conjugating matrix equals its prescribed word.

It follows that the rank data obtained from the split equation and
conjugacy spectra yield no additional obstruction at the exact native
anchor. They cannot replace a quantitative argument using the shared
occurrences in (1), or their interaction with the other packet rows.

This is not a countermodel of `rho_5` with its word occurrences, and it
does not solve `rho_8`. In particular it neither extends the known
672-dimensional source model to the full packet nor proves a uniform
HS gap. The result records a precise limitation of a multiplicity-only
approach to the remaining split relation.
