---
rg: 2
id: odd-tensor-threehot-hidden-sector-proof
kind: route
title: Multiply three marked selector eigencharacters and track their trace mass
target: odd-tensor-closure-forces-a-threehot-hidden-sector
requires:
  - lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass
---

For a representation `pi`, write

```text
P_a^pi=product_(i=1)^m (I+(-1)^(a_i)pi(X_i))/2.         (OTP1)
```

The factors commute, so these are the joint spectral projections of the
finite elementary abelian selector subgroup.

Take negative-`J` representations `pi_1,pi_2,pi_3` and characters
`a_r in Spec_X(pi_r)`.  Choose nonzero
`xi_r in ran(P_(a_r)^(pi_r))`.  In the diagonal tensor-product
representation

```text
Pi(g)=pi_1(g) tensor pi_2(g) tensor pi_3(g),             (OTP2)
```

one has, for every selector,

```text
Pi(X_i)(xi_1 tensor xi_2 tensor xi_3)
 =(-1)^((a_1)_i+(a_2)_i+(a_3)_i)
   (xi_1 tensor xi_2 tensor xi_3).                      (OTP3)
```

The tensor vector is nonzero.  Moreover

```text
Pi(J)=(-I) tensor (-I) tensor (-I)=-I.                  (OTP4)
```

Thus `a_1+a_2+a_3 in Sigma_-`, proving ternary closure.

For completeness, every nonempty ternary-closed subset `S` of
`F_2^m` is affine.  Fix `s_0 in S`.  Then `H=S+s_0` contains zero,
and if `x+s_0,y+s_0 in H`, ternary closure gives

```text
(x+s_0)+(y+s_0)
 = (x)+(y)+(s_0)+s_0 in H.                              (OTP5)
```

Equivalently, `x+y+s_0 in S`.  Hence `H` is a subgroup and
`S=s_0+H`.

Now suppose the representations carry finite traces `tau_r`.  The joint
spectral projection in `Pi` at `a_1+a_2+a_3` contains the nonzero
orthogonal summand

```text
P_(a_1)^(pi_1) tensor P_(a_2)^(pi_2)
  tensor P_(a_3)^(pi_3).                               (OTP6)
```

Under the product trace its mass is the product of the three input masses.
This proves `(OTH4)`; taking all three representations equal proves the
tensor-cube statement.

For the uniform source bound, sort the outcome weights in the context from
the source theorem:

```text
alpha_1>=alpha_2>=...>=alpha_M,
sum_(j>=3) alpha_j>=eta_0.                              (OTP7)
```

Then

```text
alpha_1>=1/M,
alpha_3>=eta_0/(M-2),
alpha_2>=alpha_3.                                       (OTP8)
```

Choose the three distinct outcomes carrying `alpha_1,alpha_2,alpha_3`.
Equations `(OTP6)--(OTP8)` give

```text
tau^tensor3(P_threehot)
 >=alpha_1 alpha_2 alpha_3
 >=eta_0^2/(M(M-2)^2),                                  (OTP9)
```

which is `(OTH6)`.

All of this uses only that the visible coordinates are literal commuting
group involutions and that the marked class is closed under diagonal tensor
products.  Relations involving arbitrary shared noncommuting ancillas remain
true in `Pi` automatically and cannot remove the vector in `(OTP3)`.
They can evade the conclusion only if the decoder's source projections are
not the literal joint spectral projections `(OTP1)`, or if it is explicitly
restricted to a pointed non-tensor-closed state face.
