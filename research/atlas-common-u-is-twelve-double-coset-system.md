---
rg: 2
id: atlas-common-u-is-twelve-double-coset-system
kind: claim
title: The exact common-frame lift is a twelve-double-coset unitary feasibility system
distinct_from:
  atlas-a4-packet-four-rectangle-normal-form: that reduces an already chosen edge-message assignment to four cycle holonomies; this gives the gauge-invariant equations on the common relative frame from which such messages would have to be selected.
  atlas-shifted-factorizations-have-independent-right-gauge: that identifies noncanonicity of each factorization witness; this quotients all those fibers and writes the resulting exact finite product of unitary groups.
  atlas-a4-19243-type-relaxation-has-regular-zero: that proves feasibility after forgetting intertwiner coordinates; this is the remaining intertwiner/common-frame fiber over that regular point.
---

Put `D=20160k`, `rho=Reg(A8) tensor I_k`, and let `R=rho(r_0)` be the
fixed packet alignment.  For a cyclic subgroup `C_m<A8`, regular restriction
gives

```text
rho|_(C_m)=directSum_(chi in dual(C_m)) chi tensor C^(D/m).
```

Hence its unitary commutant is exactly

```text
K_2(k)=U(10080k)^2,
K_3(k)=U(6720k)^3.                                    (CUL1)
```

Collapse the thirty packet occurrences to the twelve distinct edges of
`K_(2,2) disjointUnion K_(2,4)`.  For every edge `e`, introduce

```text
X_e in K_3(k),       Y_e in K_2(k)                    (CUL2)
```

with the factors reversed on a reversed packet word.  Fix one edge `e_0`.
Then an exact common relative frame satisfying all thirty A4 packet words and
collision 19243 exists if and only if `(CUL2)` has a solution of

```text
X_e R Y_e = X_(e_0) R Y_(e_0)       (e != e_0),
q_19243(X_(e_0) R Y_(e_0))=I_D.                       (CUL3)
```

The common unitary is the shared product in `(CUL3)`.  Thus the exact problem
has twenty-four cyclic-centralizer factors, eleven common-product equations,
and one collision equation.  All coefficient matrices are permutation
matrices; after cyclic Fourier transform the equations are algebraic over
`Q(zeta_3)`.

Each edge has an independent redundant right-regular gauge

```text
Q(k)=U(rho(A8)')=product_(pi in Irr(A8)) U(k dim(pi)),
(X_e,Y_e) -> (X_e W_e,W_e^(-1)Y_e).                  (CUL4)
```

Here `W_e` commutes with `R`, so `(CUL4)` preserves the product.  The actual
parameter space is therefore the compact quotient

```text
((K_3(k) x K_2(k))/Q(k))^12,                          (CUL5)
```

subject to `(CUL3)`.

The four rectangle holonomies are not coordinates on `(CUL5)`: they require
choosing a section of the twelve independent fibers `(CUL4)`, and different
sections of the same common `U` change them.  Consequently no exact escape or
incompatibility can be certified from four freely named rectangle matrices
alone.  It must be proved on `(CUL3)`, or through a mixed moment invariant
under every gauge `(CUL4)`.

For each fixed `k`, feasibility of `(CUL3)` is a compact real-algebraic
decision problem and in principle admits exact quantifier elimination; a
solution can be chosen with real-algebraic coordinates.  But the factors in
`(CUL1)` grow with `k`, and amplification embeds the `k`-system into every
`lk`-system.  Therefore this reduction does not collapse the all-multiplicity
question to `k=1` or to a fixed finite SDP.

In the finite-tracial replacement of `(CUL1)--(CUL5)`, the known quotient
trace supplies an exact solution with positive four-transvection energy.
Thus a dimension-free incompatibility for all matrix `k` is precisely a
matrix-only nonliftability theorem for this algebraic tower.  Universal
tracial SOS, four-rectangle gauge fixing, and fixed-rank searches cannot
decide it.

The cycle-invariant audit is now exact.  By
`atlas-four-rectangles-do-not-descend-to-common-u`, the incidence graph has
the expected four degree-four fundamental cycles, but they do not define
nontrivial functions on `(CUL5)`.  Labelling each edge by its canonical common
product `X_eRY_e=U` makes every cycle identically flat; labelling it by one
factor makes its holonomy depend on the independent gauge `(CUL4)`.  Thus the
next invariant must be a genuinely mixed common-`U` Gram coordinate rather
than a rectangle word.

That first mixed coordinate is now explicit on the quotient.
`atlas-mixed-c3-gram-has-local-zero-interval` substitutes any common product
`U=X_eRY_e` into
`Lambda(U)=||E_K^-U^*rho(b_0)UE_K^+-P_6(.-)P_6||_2^2` and proves invariance
under all twelve gauges.  Collision plus the regular local profiles leaves a
whole interval of values including zero.  Hence the remaining all-`k`
question is exactly whether the simultaneous twelve-product equations cut
that interval down to `{0}`.
