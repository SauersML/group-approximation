# Wave 3: all three twists survive the specified PSL2(19)-squared cover

This pass determines the central-twist question for the actual next cover
constructed in wave2. Let `M` be the intersection of the two specified
kernels of the pinned triangle `Λ -> PSL_2(19)`. Then **every nonzero
central five-twist remains nonzero on `M`**. This is survival in that
one additional cover, not persistence in every finite cover, and it does
not settle residual finiteness.

The proof reduces a potential 11,696,400-coordinate calculation to400
coordinates and supplies three explicit finite-field obstruction vectors.
The conclusion can be verified with standard-library Python integer
arithmetic, without trusting a matrix-rank routine.

## Specified group, specified cover

The group and quotient maps are exactly those in
[[wave2-detector-psl19-perfect-first-kernel]] and
[[wave2-detector-psl19-has-second-simple-quotient]]. In `PSL_2(F_19)`:

```
x_12=[[2,11],[16,3]],
x_13=[[5,11],[4,9]],
x_23=[[6,15],[12,8]].
```

The first quotient is identity on each vertex. The second is identity
on vertex1 and conjugation by the inverses of
`u=[[1,5],[9,17]]` and `v=[[1,14],[12,13]]` on vertices2,3. The joint
map is onto `F=PSL_2(19)^2`; its kernel is `M` and its index is3420².
The three edge images in `F` are

```
(x_12,x_12), (x_13,x_13), (x_23,[[1,8],[12,6]]).
```

No different random triangle or quotient is substituted.

## Why the calculation shrinks

Let `B` be a projective-point stabilizer in `PSL_2(19)`. Its order is171,
prime to5. Put `H=f^-1(B²)` under the joint map. The index of `H` in
`Λ` is400 and `[H:M]=171²`. Restriction

```
H²(H;F_5) -> H²(M;F_5)
```

is injective by transfer. Thus a twist vanishes on `M` if and only if
it vanishes on `H`: one direction is restriction, and the reverse is
the injectivity assertion applied to its restriction to `H`.

The coset action `Λ/H` is the explicit action on
`P¹(F_19) × P¹(F_19)`. Each vertex has two orbits, of sizes20 and380,
with stabilizer orders171 and9. For `V=F_5^(Λ/H)`, Shapiro and
prime-to-five averaging give `H¹(A_v;V)=0`.

This vanishing is the condition needed to reuse the affine moment
argument. Freeness of the vertex action is not required. The subgroup
`H` may have torsion; its stabilizers have order prime to5, and the
cohomological lifting argument remains valid.

If a twist split over `H`, the extension acting on the cosets of a
complement would give a lift to `V semidirect Sym(Λ/H)` taking its
central generator to the constant function1. The vertex cocycles
would be coboundaries. Their edge differences would therefore satisfy
the same moment identities as in the full regular-coordinate test.
The proof node gives this bridge directly, including the converse;
it does not assume an unjustified regular-module replacement.

## Exact finite certificate

Each of the three order-five edges has80 free orbits on the400 points.
Let `B_edge` be the240-by400 matrix of orbit indicators, and let
`mu_12,mu_13,mu_23` be the first-moment rows, using successive powers
of the corresponding edge generator on each orbit.

Exact arithmetic gave:

```
rank(B_edge)=235,
rank([B_edge;mu_12;mu_13;mu_23])=238.
```

More usefully, the stored vectors `lambda_1,lambda_2,lambda_3` satisfy

```
B_edge lambda_i=0,
(mu_12(lambda_i),mu_13(lambda_i),mu_23(lambda_i))=e_i.
```

Their support sizes are158,159,154. A lift of a twist would imply

```
c_12 mu_12(lambda)-c_13 mu_13(lambda)+c_23 mu_23(lambda)=0
```

for every orbit-sum-zero vector. The three certificates force all
three twist coefficients to vanish. This proves the claimed survival
on `H`, hence on `M`.

Files in `experiments/hrf-wave3-detectors-2026-09-20/`:

- `borel_square_moments.py`: constructs the action, exact matrices,
  ranks, and three witnesses using python-flint.
- `borel_square_cycles.json`: the three400-entry certificate vectors.
- `verify_cycles.py`: reconstructs the permutations and checks the
  certificate using only Python's standard library.
- `borel_square_matrix.json` and `borel_square_moment_result.json`:
  inspectable matrix and numerical outputs.

Runtime on the available machine, measured with `/usr/bin/time -l`:
0.16seconds wall time and37,634,048bytes maximum resident set size for
the complete generator/rank/witness run. No huge matrix or long-running
job was launched. The standard-library checker returned:

```
PASS: all240 orbit sums vanish; the3 by3 moment matrix is identity modulo5.
```

## What is and is not known about homology

The reduced400-sheeted subgroup has six vertex orbits,240 edges,
400 faces, and boundary rank235 over `F_5`. Since all its stabilizers
have order prime to5, its mod-5 cohomology is computed by the quotient
cell complex. Thus `b_1(H;F_5)=240-(6-1)-235=0` and
`b_2(H;F_5)=400-235=165`.

This does **not** imply `H_1(M;F_5)=0`. A prime-to-five finite quotient
can act on nonzero first homology with no invariant vectors. The
proved result is precisely retention of the three original twist
classes on `M`. The full homology of `M`, and further covers where
these classes might eventually die, remain open in this calculation.

Cairn claim: [[wave3-detector-psl19-square-kernel-retains-five-twists]].
Written proof and exact certificate passed independent review. The
reviewer replayed the matrix computation and all720 orbit-sum equalities
in the standard-library checker, and checked the nonnormal-subgroup
lifting equivalence and transfer argument. No formal proof-assistant
certification is asserted.
