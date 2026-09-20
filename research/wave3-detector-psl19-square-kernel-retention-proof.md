---
rg: 2
id: wave3-detector-psl19-square-kernel-retention-proof
kind: route
title: Reduce the specified square cover to a400-point prime-to-five stabilizer cover and obstruct splitting with three exact orbit-moment cycles
target: wave3-detector-psl19-square-kernel-retains-five-twists
requires:
  - wave2-detector-psl19-has-second-simple-quotient
  - hrf-alt-edge-twist-finite-detector-spectrum
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-detectors-2026-09-20.md
  - experiments/hrf-wave3-detectors-2026-09-20/borel_square_cycles.json
  - experiments/hrf-wave3-detectors-2026-09-20/verify_cycles.py
---

Let `F=Q²`, `f=(f_0,f_1)`, and let `B<=Q` stabilize infinity in the
projective line. It has order `19*9=171`. Set `H=f^-1(B²)`. Then
`[Λ:H]=20²=400`, `M` is normal in `H`, and `[H:M]=171²` is prime to5.
Restriction `H²(H;F_5)->H²(M;F_5)` is injective: corestriction after
restriction multiplies by `[H:M]`, an invertible scalar. It therefore
suffices to prove that each nonzero twist remains nonsplit over `H`.

Write `X=Λ/H=F/B²=P¹(F_19)²` and `V=F_5^X`, with the permutation
action `(g u)(x)=u(g^-1 x)`. If a central extension `Λ_c` splits over
`H`, let `S` be a complementary copy of `H` in its preimage. Left
multiplication on `Λ_c/S` commutes with the free central `C_5` action.
The `C_5`-orbits identify with `X`. After choosing origins in these
fibres, this gives a homomorphism `Λ_c -> V semidirect Sym(X)` whose
permutation part is the prescribed action and whose central generator
maps to the constant function1. Conversely such a homomorphism
retracts the preimage of `H` onto `C_5` by evaluation at the fixed
basepoint of `H`, so it gives a splitting. This is an exact finite
lifting test and does not require `H` to be normal or torsion-free.

Each vertex acts on `X` through a graph of a projective conjugation of
`Q`, hence is conjugate as a permutation action to the diagonal action
of `Q` on its projective line squared. Its orbits have sizes20 and380;
their stabilizers have orders171 and9. Both are prime to5. Shapiro's
lemma and averaging over these finite stabilizers imply
`H¹(A_v;V)=0`. Thus the vertex parts of any proposed lift have the form
`a -> ((a-1)u_v, f(a))` for some `u_v in V`.

Use the edge order `(12,13,23)`. On an edge `e=ij`, the twisted
identification forces

```
(x_e-1)(u_i-u_j)=c_e*1.
```

All edge orbits in `X` have length5. For any orbit with basepoint `b`,
a particular solution for `w_e=u_i-u_j` is
`w_e(x_e^k b)=-k c_e`; the difference between any two solutions is
constant on each orbit. Consequently if `lambda in F_5^X` sums to zero
on every orbit of each edge, pairing against `lambda` gives

```
c_12 mu_12(lambda) - c_13 mu_13(lambda) + c_23 mu_23(lambda)=0,
mu_e(lambda)=sum_orbits sum_(k=0)^4 k lambda(x_e^k b).
```

This necessary equality follows from
`(u_1-u_2)+(u_2-u_3)-(u_1-u_3)=0`. The moment does not depend on the
orbit basepoint because the orbit sum is zero.

The projective edge matrices in the two factors of `F` are precisely

```
(x_12,x_12), (x_13,x_13), (x_23,y),
y=[[1,8],[12,6]],
```

where the three `x_e` are the pinned wave2 matrices. The stored
certificate gives three vectors `lambda_1,lambda_2,lambda_3` on the
400 points. The standard-library verifier reconstructs each edge
permutation from these matrices and checks, exactly modulo5, all240
orbit-sum equalities for each vector and

```
(mu_12(lambda_i),mu_13(lambda_i),mu_23(lambda_i))=e_i.
```

The necessary equality therefore forces respectively
`c_12=0`, `c_13=0`, and `c_23=0`. Every nonzero twist fails to split
over `H`, and injectivity of restriction then proves its nonvanishing
over `M`. The argument uses explicit finite witnesses, not a numerical
rank estimate or an extrapolation over untested covers.
