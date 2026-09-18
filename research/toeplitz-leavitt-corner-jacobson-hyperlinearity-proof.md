---
rg: 2
id: toeplitz-leavitt-corner-jacobson-hyperlinearity-proof
kind: route
title: Identify the complementary Toeplitz algebra with J by coefficient extraction, then use the trivial centralizer of the finitary kernel
target: toeplitz-supported-leavitt-corner-is-jacobson-hyperlinearity
requires:
  - jacobson-shift-representation-is-faithful
  - binary-jacobson-mark-dichotomy-holds-from-rank-two
  - leavitt-corner-bcs-support-coefficient-gate
---

Notation as in the target.  A countable group is hyperlinear when it embeds
in the unitary group of a tracial matrix ultraproduct.  `Rad_hyp(G)` is the
intersection of the kernels of all homomorphisms from `G` into such unitary
groups.  Subgroups of hyperlinear groups are hyperlinear.

## Step 1. (TJ1): the complementary Toeplitz algebra is J

In `R=L_(F_2)(1,2)` we have `t_2s_2=1`.  By the universal property of `J`,
there is a unital ring map `iota:J->T_2` with `S |-> s_2` and `T |-> t_2`.
It is onto by the definition of `T_2`.  Also
`iota(Q)=1-s_2t_2=s_1t_1=q`, using `s_1t_1+s_2t_2=1`.

Next, `q` is not zero.  Indeed `t_1 q s_1=(t_1s_1)(t_1s_1)=1`, and `R` is a
nonzero ring.

Now let `a` be a nonzero element of `ker(iota)`.  By item 1 of
`jacobson-shift-representation-is-faithful` (with `C=Z/2Z`), the shift
representation is faithful.  So `a v_j` is nonzero for some `j`.  Pick an
index `i` at which the coefficient of `v_i` in `a v_j` is `1`.  Coefficient
extraction `(JSF3)` gives

```text
Q T^i a S^j Q = Q.
```

The left side lies in the ideal `ker(iota)`, so `Q` does too.  Then
`q=iota(Q)=0`, a contradiction.  Hence `iota` is an isomorphism.

It induces a group isomorphism `EL_20(J) -> EL_20(T_2)`, sending
`x_13(Q)` to `x_13(q)`.  Under the symbol map `Q |-> 0`, since `Q` lies in
`M_fin(N,F_2)` by `(JSF2)`.  So `x_13(Q)` maps to `1` in
`EL_20(F_2[z,z^(-1)])`.  By exactness in item 1 of
`binary-jacobson-mark-dichotomy-holds-from-rank-two`, `x_13(Q)` lies in
`L_20`.  It is not the identity, because `Q` is not zero.

## Step 2. (TJ2): one mark in the kernel decides everything

Fix `n>=2` and a nonidentity `w in L_n`.

First, suppose `G_n` is hyperlinear.  A hyperlinear embedding of `G_n` is a
homomorphism into a hyperlinear group.  It retains `w` and kills no
nonidentity element, so `w notin Rad_hyp(G_n)`.

Next, suppose `w notin Rad_hyp(G_n)`.  Then some homomorphism into a
tracial-ultraproduct unitary group retains `w`, and that target is a
hyperlinear group.

Finally, suppose `h:G_n -> H` retains `w`, with `H` hyperlinear.  Item 2 of
`binary-jacobson-mark-dichotomy-holds-from-rank-two` says:
"`C_(G_n)(L_n) = 1`, so any homomorphism out of `G_n` retaining any
nonidentity element of `L_n` ... is injective".  So `h` is injective.  Its
image is a countable subgroup of `H`, hence hyperlinear, and `G_n` is
isomorphic to it.

These three implications close the cycle of equivalences.  For the radical
statement, suppose `Rad_hyp(G_n)` does not contain `L_n`.  Pick `w` in
`L_n` but not in the radical.  Then `G_n` is hyperlinear, so
`Rad_hyp(G_n)=1`.

## Step 3. (TJ3): the Leavitt corner

Let `Phi` be an `LNC3` diagram with support `X`, and suppose
`pi(X) <= EL_20(T_2)`.  Put `Gamma_X=<X,z> <= Delta`.

- By the hyperlinear shadow gate in `leavitt-corner-bcs-support-coefficient-gate`,
  "for every group homomorphism `h` from `Gamma_X=<X,z> <= Delta` to a
  hyperlinear group, `h(z)=1`."
- `pi(z)=x_13(q)` lies in `EL_20(T_2)`, because `q` is in `T_2`.  So
  `pi(Gamma_X) <= EL_20(T_2)`.
- Put `h = iota^(-1) o pi` restricted to `Gamma_X`.  It maps into `G_20`,
  and `h(z)=x_13(Q)` is not the identity.

Now suppose `G_20` were hyperlinear.  Then `h` would be a homomorphism into a
hyperlinear group retaining `z`, which the gate forbids.  Therefore `G_20` is
nonhyperlinear.  The equivalent form is the contrapositive.
