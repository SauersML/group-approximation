---
rg: 2
id: tensor-affine-selector-pattern-barrier-proof
kind: route
title: Tensor three fixed-phase representations and use ternary affine closure
target: tensor-affine-selector-pattern-barrier
requires: []
---

Take three patterns `epsilon,eta,theta in Sigma_fd`, realized by
representations `pi_epsilon,pi_eta,pi_theta`.  Their diagonal tensor product

```text
pi(g)=pi_epsilon(g) tensor pi_eta(g) tensor pi_theta(g)
```

is again a finite-dimensional unitary representation.  On the distinguished
phase,

```text
pi(J)=(-I) tensor (-I) tensor (-I)=-I,
```

while for every selector

```text
pi(z_i)=(epsilon_i eta_i theta_i) I.
```

Hence `Sigma_fd` is closed under coordinatewise ternary multiplication.

Identify `{+1,-1}^m` with the additive group `F_2^m`.  Thus `Sigma_fd` is a
nonempty subset closed under

```text
x+y+z.
```

Fix `x_0 in Sigma_fd` and put

```text
H=Sigma_fd+x_0.
```

Then `0 in H`.  If `h_1=x_1+x_0` and `h_2=x_2+x_0` lie in `H`, ternary
closure gives

```text
x_0+h_1+h_2 = x_0+x_1+x_0+x_2+x_0 = x_0+x_1+x_2 in Sigma_fd,
```

so `h_1+h_2 in H`.  Therefore `H` is a subgroup of `F_2^m`, and

```text
Sigma_fd=x_0+H
```

is affine.

Exactly the same proof works for any tensor-closed representation class.  For
finite tracial von Neumann algebras, use the spatial tensor product and product
trace; the scalar identities above are unchanged.

For `m>=3`, the one-hot set is not affine by
`one-hot-selector-parity-barrier`, so it cannot equal `Sigma_fd`.  This proves
the claim.
