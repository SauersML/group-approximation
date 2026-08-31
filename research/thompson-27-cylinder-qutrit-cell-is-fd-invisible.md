---
rg: 2
id: thompson-27-cylinder-qutrit-cell-is-fd-invisible
kind: claim
title: Twenty-seven Thompson cylinders give an fd-invisible three-phase qutrit cell
artifacts:
  - research/thompson-27-cylinder-qutrit-cell-proof.md
distinct_from:
  two-qutrit-controlled-bases-give-proper-multipath-marginal: that builds the local cell in a virtually free amalgam and proves its multipath marginal is not a renamed finite type there; this embeds the same finite packet in hosts whose finite-dimensional representations annihilate its root, while isolating the finite-support limitation.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that proves ambient minimal almost periodicity; this gives an explicit finite-subgroup type, exact context partition, proper marginal, and coefficientwise three-phase collision inside that ambient group.
  finite-support-corner-localizes-obstruction: that localizes any completed no-CE atlas to its support subgroup; this identifies the concrete finite support of the new cell and the exact kind of off-code relation still required.
---

Let `omega` be a primitive cube root and put

```text
Omega=F_3^2 x F_3,
D_27={1^r 0:0<=r<=25} union {1^26}.                    (TVQ1)
```

Label the 27 cylinders of the maximal binary prefix code `D_27` by
`(u_1,u_2,s) in Omega`.  In the finite prefix-permutation subgroup
`Sym(D_27)<=V`, define

```text
J(u_1,u_2,s)  =(u_1,u_2,s+1),
X_i(u_1,u_2,s)=(u_1+delta_(i1),u_2+delta_(i2),s),
Z_i(u_1,u_2,s)=(u_1,u_2,s-u_i).                        (TVQ2)
```

These permutations generate the order-`3^5` extraspecial group

```text
F=<J,X_1,Z_1,X_2,Z_2 |
   J central, every generator has order 3,
   X_i Z_i=J Z_i X_i,
   all other displayed pairs commute>.                 (TVQ3)
```

Put

```text
K=<J,X_1,Z_1>,                    C=<J,Z_1>,
q=e_(<J>,omega)=z_(K,pi_omega),

B_0=Z_2,             B_1=X_2,             B_2=X_2 Z_2,
A_a=<J,Z_1,B_a>.                                      (TVQ4)
```

For `a,b in F_3`, let `alpha_(a,b)` send `J,Z_1,B_a` to
`omega,omega^a,omega^b`, respectively, and put

```text
p_(a,b)=z_(A_a,alpha_(a,b)).
```

Then, already in `C[V]`,

```text
p_(a,b) p_(c,d)=0 unless (a,b)=(c,d),
sum_(a,b) p_(a,b)=q.                                  (TVQ5)
```

The projection

```text
P=p_(0,0)+p_(1,0)+p_(2,0)                              (TVQ6)
```

is a proper noncentral marginal:

```text
0<P<q,             tau_V(P)=1/9,             tau_V(q)=1/3. (TVQ7)
```

Thus the fine context `{p_(a,b)}` and the coarse context `{P,q-P}`
share the proper plus marginal `P`.

This realization meets the phase-balance escape sharply.  Every group element
in the support of the fine context which lies outside the root subgroup
`K` has a unique form

```text
J^j Z_1^k B_a^t,                         t in {1,2},     (TVQ8)
```

for one `a).  It occurs in exactly the three atoms `p_(a,b)`,
`b in F_3`, with equal-modulus coefficients whose phases are a common
scalar times

```text
1, omega^(-t), omega^(-2t).                            (TVQ9)
```

Their sum is zero.  Hence there are no escaped support leaves and no
degree-two term pairings: cancellation outside `K` is genuinely
three-phase, coefficient by coefficient.

At the same time the selected root type is finite-dimensional-invisible in
each of the following ambient groups:

1. `V`;
2. `EL_4(L_(F_2)(1,2))`, using the cylinder-swap copy of `V`, Leavitt
   self-similarity, and `GL_4=EL_4`;
3. `St_n(L_(F_2)(1,2))` for `n>=5`, using the lifted Thompson subgroup.

Indeed every finite-dimensional unitary representation restricts trivially
to that copy of `V`, so it sends `J` to the identity and therefore sends

```text
q=(1/3)(1+omega^(-1)J+omega^(-2)J^2)
```

to zero.

This is a simultaneous positive solution of the **local** fd-invisibility,
proper-multipath, and three-phase gates.  It is not a nonhyperlinear group.
Every coefficient displayed above is supported in the finite group
`F<=Sym(D_27)`; the regular representation of `F` realizes the entire
cell with `q!=0`.  Ambient minimal almost periodicity does not make that
finite support load-bearing.

Consequently a completed no-CE atlas cannot keep all of its support in one
fixed prefix-permutation group.  The exact next object is a mixed
nontransport overlap relation between such cells whose support contains an
off-code prefix or Steinberg element and whose cumulative support subgroup is
not the finite `Sym(D_27)`.  A conjugacy arrow, a flat Morita cycle, or
another permutation of the same 27 leaves does not suffice.
