---
rg: 2
id: finite-subgroup-corner-basis-number-proof
kind: route
title: Apply the lifted trace to the projective equivalence defined by rectangular inverses
target: finite-subgroup-corners-have-invariant-basis-number
requires:
  - lifted-trace-detects-finite-subgroup-projectives
  - leavitt-corner-idempotent-unital-surjection
---

Let P=eS^k. A rectangular inverse pair over T=eM_k(S)e defines an
S-module isomorphism P^n ~= P^m: expand each T-entry into its k by k
matrix over S and apply the resulting block maps to the e-summands.
Consequently (n-m)[P]=0 in K_0(S). The lifted-trace theorem gives

    t_p([P])=d/|H|,       d=dim_(F_p)(eF_p[H]^k)>0.

Applying it yields (n-m)d/|H|=0 in Z_p. Since Z_p embeds in the
characteristic-zero field Q_p and d is a positive integer, n=m. This
also proves the module version of invariant basis number, because any
isomorphism between finite free T-modules has rectangular inverse
matrices over T.

For the designated cubic corner, H=<g> has order three and eF_2[H]
has dimension two, so t_2([eS])=2/3. A binary Leavitt family would give

    X=(S_0 S_1),       Y=(T_0 T_1)^t,
    XY=e,             YX=diag(e,e).

Hence [eS]=2[eS], contradicting t_2([eS])=2/3. This excludes all
families before imposing evaluation constraints, and hence excludes a
unital ring section of the corner evaluation.

For this special case, a finite coefficient certificate suffices. Lift
e to E=2+g+g^2 in (Z/4)[G], whose identity coefficient is 2. The
rectangular equivalence lifts through the square-zero ideal by the
argument in the lifted-trace proof, forcing

    T(E)=T(diag(E,E)),       2=0 modulo four.

The general p-adic argument also handles all m,n for which n-m is
divisible by any prescribed power of p. No bound on the ambient
supports of the intertwiners is imposed.
