---
rg: 2
id: endpoint-first-raw-prefix-toeplitz-threshold-proof
kind: route
title: Iterate the zero prefix and close coefficient roots under Steinberg commutators
target: endpoint-first-raw-prefix-escape-hits-toeplitz-core
requires:
  - endpoint-zero-tail-packet-has-marked-finite-model
  - literal-prefix-coupling-of-j1-j2-has-gl7-model
  - native-a1-b2-hecke-triangle-has-gl7-model
  - leavitt-first-offdiagonal-core-is-marked-non-lef
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
---

Let `Omega={0,1}^N` and use the prefix action

```text
s_i(omega)=i omega,
t_i(j omega)=omega if i=j, and 0 otherwise.             (1)
```

For `alpha=000...` and `beta=1000...`, equation `(1)` gives

```text
t_0 alpha=alpha,       t_0 beta=0,
s_0 alpha=alpha,       s_0 beta=01000....               (2)
```

Thus the already named occurrence `T_0=x_97(t_0)` preserves the two-tail
carrier of the prerequisite, whereas `L_y=x_87(s_0)` does not.

Now let `F subseteq Omega` be finite and suppose the common-tail space
`span(F)^20` is invariant under `L_y`.  Applying `L_y=1+s_0E_87` to a basis
vector supported in coordinate `7` shows that `s_0 omega belongs to span(F)`
for every `omega in F`.  Since the tails form a basis of the prefix module,
this means

```text
s_0F subseteq F.                                         (3)
```

The injection `s_0:F->F` is a permutation of the finite set.  Hence for
every `omega in F` there is an `r>0` with

```text
s_0^r omega=omega.
```

Comparing binary coordinates forces every coordinate of `omega` to be zero,
so `omega=alpha`.  Therefore `F subseteq {alpha}`.  But `q=s_1t_1` is the
projection onto tails beginning in `1`, whence `q span(F)=0`.  In particular
`x_13(q)` restricts to the identity.  This proves the finite-tail assertion.

For the generated-group assertion, choose the five coordinates
`I={1,3,7,8,9}` and set

```text
A=<D,s_0,t_0>,             H=<EL_I(D),x_97(t_0),x_87(s_0)>.
```

The constant subgroup `EL_I(F_2)<=EL_I(D)` contains Weyl words inducing all
permutations of `I`.  Since signs vanish in characteristic two, Weyl
conjugation moves each of `x_97(t_0)` and `x_87(s_0)` to `x_ij(t_0)` and
`x_ij(s_0)` for every `i!=j` in `I`.

Define

```text
A_0={a in A : x_ij(a) belongs to H for every i!=j in I}.
```

The inclusion `EL_I(D)<=H` gives `D subseteq A_0`, and the preceding Weyl
conjugations give `s_0,t_0 in A_0`.  Root addition makes `A_0` additively
closed.  Given `a,b in A_0` and distinct `i,j`, choose a third coordinate
`k in I`; the ordinary Steinberg relation

```text
[x_ik(a),x_kj(b)]=x_ij(ab)                              (4)
```

makes `A_0` multiplicatively closed.  Hence `A_0=A`, so every elementary
generator of `EL_I(A)` lies in `H`.  The reverse containment is immediate,
proving `(RPE3)`.

The subring `J=<s_0,t_0>` satisfies `t_0s_0=1` and has head idempotent

```text
Q=1-s_0t_0=s_1t_1=q.
```

Thus `EL_I(J)<=H` and contains the literal mark `x_13(q)`.  By
`binary-jacobson-elementary-mark-is-finite-quotient-invisible`, every
homomorphism from this rank-five Jacobson group to a finite group kills
`x_13(q)`.  Restricting any finite quotient of `H` to this subgroup proves
the final assertion.
