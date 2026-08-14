# The determinant central extension does not pass to the Hilbert--Schmidt quotient

Date: 2026-08-14

## 1. Outcome

Dadarlat--Glebe's determinant central extension retains microscopic winding
data for **operator-norm** asymptotic representations.  It cannot be
transplanted verbatim to the normalized-Hilbert--Schmidt quotient used for
hyperlinearity.

The obstruction is exact.  Hilbert--Schmidt-small unitaries may cross the
logarithm branch cut on a subspace of rank `o(d)`.  The normalized logarithm
then fails additivity by a nonzero element of the normalized `K_0` lattice.
That element tends to zero, but it is not eventually zero, so it is precisely
the microscopic class that the operator-norm construction retains.

There are only two immediate choices:

1. retain the lattice element, in which case the proposed Hilbert--Schmidt
   logarithm is not additive and does not define the required central
   extension; or
2. quotient by the normalized `K_0` lattice, in which case additivity is
   restored but the desired integer/parity signal is erased.

Thus the determinant construction does not supply the missing
index-to-phase transducer.  A viable replacement would still need
presentation-forced spectral control or genuinely asymmetric boundary data.

## 2. The rank-one branch-crossing test

Let `d_n -> infinity` and put

```text
u_n=diag(-1,1,...,1) in U(d_n).                     (DHS1)
```

With normalized Hilbert--Schmidt norm,

```text
||u_n-1||_2=2/sqrt(d_n) -> 0.                       (DHS2)
```

Hence `(u_n)` represents the identity in the tracial matrix ultraproduct.
Using the principal logarithm, however,

```text
L_n(u_n)=(1/(2 pi i)) tr_(d_n)(log u_n)=1/(2d_n).  (DHS3)
```

Since `u_n^2=1`,

```text
L_n(u_n^2)=0,
2L_n(u_n)-L_n(u_n^2)=1/d_n.                         (DHS4)
```

The sequence `(1/d_n)` belongs to `c_0(N,R)` but not to the finitely
supported subgroup `c_00(N,R)`.  Therefore it is nonzero in

```text
c_0(N,R)/c_00(N,R).                                 (DHS5)
```

So the principal-log map on the Hilbert--Schmidt-null subgroup is not a
homomorphism into the coefficient group which remembers microscopic
winding.  The failure occurs even for commuting involutions and even though
the product is exactly the identity.

More generally, putting `-1` on `r_n=o(d_n)` coordinates gives

```text
||u_n-1||_2^2=4r_n/d_n -> 0,
2L_n(u_n)-L_n(u_n^2)=r_n/d_n.                       (DHS6)
```

Thus every sublinear-rank branch crossing produces the same conflict.

## 3. Why the operator-norm construction avoids the defect

Dadarlat--Glebe work with the Banach-algebra ideal

```text
c_0(N,A_n)={ (a_n) : ||a_n|| -> 0 }.                (DHS7)
```

For elements uniformly inside a logarithm chart, their local determinant
`L_tau` is additive.  Their Proposition 2.4 uses the hypotheses

```text
||v_i-1|| < 1/4                                    (DHS8)
```

to keep the straight-line homotopy inside one invertible logarithm
neighborhood.  Equation `(DHS1)` never enters that neighborhood:
`||u_n-1||=2` for every `n`, although `(DHS2)` tends to zero.

This is not a technical mismatch of constants.  Operator norm forbids any
branch-cut eigenvalue, while normalized Hilbert--Schmidt norm deliberately
forgets a sublinear-rank collection of them.

## 4. Quotienting by `K_0` repairs the law and kills the phase

For `M_d(C)` with normalized trace, the de la Harpe--Skandalis determinant is
naturally valued modulo

```text
tr_d(K_0(M_d(C)))=(1/d) Z.                          (DHS9)
```

The additivity defect `1/d_n` in `(DHS4)` vanishes modulo this lattice.  But
that same integer is the proposed microscopic index.  Any map

```text
1/d_n |-> (-1)                                     (DHS10)
```

must distinguish two logarithm lifts which the determinant identifies.
It therefore does not descend from the determinant class.

Equivalently, determinant parity is discontinuous for normalized
Hilbert--Schmidt convergence: changing one eigenvalue from `+1` to `-1`
changes the parity while costing only `2/sqrt(d)`.  A group presentation
might conceivably protect such a parity through an additional uniform gap,
but tracial convergence and the determinant formalism alone do not.

## 5. Consequence for the active hyperlinear program

This closes the automatic implication

```text
operator-norm determinant extension
  => normalized-HS index-to-phase extension.        (DHS11)
```

It also complements `FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md`.  The
direct compression `PUP` has index zero because it is square.  The
determinant alternative can retain a nonzero microscopic winding in the
operator-norm corona, but loses its cocycle law on the Hilbert--Schmidt-null
ideal unless that winding is quotiented out.

The live endpoints therefore remain matrix-coordinate recovery of the fixed
Pauli block shifts, equivariant recovery of a common finite lamp algebra in
the Kun--Thom model, or a new presentation-supplied asymmetric boundary
construction.  None is supplied by the determinant central extension.

## Primary source

- M. Dadarlat and F. Glebe, *Central Extensions and Almost
  Representations*, International Mathematics Research Notices 2025,
  rnaf261, [arXiv:2502.04590](https://arxiv.org/abs/2502.04590), especially
  Definition 2.1, Proposition 2.4, and Definition 3.2.
