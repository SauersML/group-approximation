---
rg: 2
id: tfd-deck-gap-and-qutrit-bimodule-tensor-countermodel-proof
kind: route
title: Tensor a quotient representation with the right regular head complement
target: tfd-deck-gap-is-morita-neutral-to-a-rectangular-qutrit-head
requires:
  - tfd-tensorization-gaps-every-finite-deck-packet
  - tensor-the-hecke-carrier-with-the-qutrit-regular-bimodule-proof
---

# The tensor identities

Let `pi_0:Gamma->U(V)` be finite-dimensional and let `K` be any
finite-dimensional Hilbert space. For the tensor-amplified representation

~~~text
pi(g)=pi_0(g) tensor I_K
~~~

each Schreier return `r(s,x) in Lambda` satisfies

~~~text
(pi(r(s,x))-I)^*(pi(r(s,x))-I)
 =
((pi_0(r(s,x))-I)^*(pi_0(r(s,x))-I)) tensor I_K.          (1)
~~~

A vector in `V tensor K` is `Lambda`-fixed exactly when each of its
`K`-coefficients is fixed by `pi_0(Lambda)`. Therefore

~~~text
(V tensor K)^Lambda=V^Lambda tensor K,
P_Lambda(pi)=P_Lambda(pi_0) tensor I_K.                   (2)
~~~

Averaging (1) proves both identities in `(TDQ3)`. Inserting (2) in
`(FDP3)` shows that the TFD inequality tensorizes with equality of its
multiplicity structure. It controls the first factor and is deliberately
blind to every projection in `I_V tensor B(K)`.

If `pi_0` factors through `Gamma/Lambda`, then every return is the
identity and `P_Lambda(pi)=I`. Both sides of `(FDP3)` are zero on the
whole amplified host. This is not a small-gap example: it is the exact
kernel allowed by the theorem.

# The rectangular head inside the kernel

Let `F` be finite, put `K=ell^2(F)), and let `lambda_F` be its left
regular representation. For a self-adjoint projection `q in C[F]`, let

~~~text
P=R(q),                    P(x)=xq.
~~~

Left and right multiplication commute, so `P` commutes with every
`lambda_F(u)`. Its normalized rank is

~~~text
rank(P)/|F|=tau_F(q)=alpha.                               (3)
~~~

Put `K_0=(I-P)K` and let `j:K_0->K` be the inclusion. Choose any
finite-dimensional quotient representation
`sigma:Gamma/Lambda->U(V)`) and define

~~~text
H_T=V tensor K,                  H_S=V tensor K_0,

Pi_T(g,u)=sigma(gLambda) tensor lambda_F(u),
Pi_S(g,u)=Pi_T(g,u) restricted to H_S,

S=I_V tensor j,                  T=S^*,
Q=I_(H_T)-ST=I_V tensor P.                                (4)
~~~

The commutation of `P` with the left regular action makes `H_S`
invariant. Direct multiplication gives, for every `(g,u)`,

~~~text
Pi_T(g,u)S=S Pi_S(g,u),

TS=I_(H_S),             ST=I_(H_T)-Q,
QS=0,                   TQ=0.                             (5)
~~~

Equation (3) gives `tr_(H_T)(Q)=alpha`. Every Schreier return lies in
`Lambda`, so its image under both `Pi_T` and `Pi_S` is the identity.
Thus the complete return packet, not only a chosen finite subset, has zero
energy in this model.

For completeness, this rectangular system sits in one ordinary finite
group representation. On `H_T direct-sum H_S` put

~~~text
z=diag(I_(H_T),-I_(H_S)),

a=[ Q  S ].
  [ T  0 ]
~~~

Equations (5) give

~~~text
a^2=z^2=I,                    (az)^4=I.                    (6)
~~~

Both `a` and `z` commute with the diagonal
`(Gamma/Lambda) times F` image. Hence the generated image is a quotient
of the finite group
`((Gamma/Lambda) times F) times D_8`. The construction is an exact
finite-dimensional absorber, not merely a tensor-category analogy.

# The qutrit specializations

Take first the abelian order-eighteen head torus
`B=<H> times C` and

~~~text
q_b=Ee_b,                  E=(I-H)/2.
~~~

This is a minimal character projection. Its regular trace is `1/18`,
and, because `B` is abelian, `R(q_b)=L(q_b)`). Equations (4)--(6)
therefore give a literal qutrit trace-`1/18` head with full
`B)-covariance and zero deck-return energy.

For the full head group `F_0` of order `288`, the same group-algebra
projection has regular rank

~~~text
288 tau_(F_0)(q_b)=16.
~~~

The right copy `R(q_b)` commutes with the full left `F_0)-action and
again gives (4)--(6). The natural left copy `L(q_b)` is noncentral and
cannot itself be a fully `F_0)-covariant cokernel; an unconstrained
same-rank router between the two copies exists and is exactly the finite
commutant/absorber dichotomy.

This proves the claimed cross-lane boundary. TFD removes nonflat normal
modes in a finite host, while the qutrit head is placed wholly in the
allowed flat multiplicity kernel. A relation that merely appends the two
modules cannot see it. Only a mixed relation involving the nonfinite raw
coefficient and the left-right router can escape this exact model.
