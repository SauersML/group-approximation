---
rg: 2
id: kazhdan-hellinger-block-balance-proof
kind: proof
title: Apply the Kazhdan gap to square roots of block multiplicities
target: property-t-kills-multiplicity-only-jacobson-gauges
requires:
  - jacobson-property-t-and-finite-k-do-not-exactify-the-head
---

Let `pi` be the permutation representation of `Q` on
`l^2(Omega)`, and put

```text
xi(omega)=sqrt(p(omega)).
```

Then `||xi||_2=1`. For `s in Sigma`,

```text
||pi(s)xi-xi||_2^2
 =sum_omega
   |sqrt(p(s^(-1)omega))-sqrt(p(omega))|^2
 <=sum_omega |p(s^(-1)omega)-p(omega)|
 =2 h_s(p).                                             (KHB4)
```

The scalar inequality used here is

```text
|sqrt(a)-sqrt(b)|^2 <= |a-b|,             a,b>=0.
```

Let `P` be the orthogonal projection onto the invariant vectors and
write `xi=xi_0+xi_perp`, where `xi_0=P xi`. Since `xi_0` is
invariant, the Kazhdan inequality and `(KHB4)` give

```text
kappa ||xi_perp||_2
 <=max_(s in Sigma)||pi(s)xi_perp-xi_perp||_2
 <=sqrt(2 eta).                                         (KHB5)
```

Set `a=sqrt(2 eta)/kappa`. If `a<1`, then
`||xi_0||_2>=1-a>0). Normalize

```text
u=xi_0/||xi_0||_2.
```

Projection onto invariant functions averages on each orbit, so
`xi_0` and `u` are nonnegative and constant on every orbit. Also

```text
||xi-u||_2
 <=||xi-xi_0||_2+|1-||xi_0||_2|
 <=2a.                                                   (KHB6)
```

Define the invariant probability `p_bar(omega)=u(omega)^2`. By
Cauchy--Schwarz,

```text
||p-p_bar||_1
 =sum_omega |xi(omega)^2-u(omega)^2|
 <=||xi-u||_2 ||xi+u||_2
 <=4a.                                                   (KHB7)
```

If `a>=1`, choose any probability which is uniform on one orbit;
the trivial bound `||p-p_bar||_1<=2` applies. This proves
`(KHB2)`.

For `q in Q`, invariance of `p_bar` gives

```text
sum p_bar(omega) f(omega)
 =sum p_bar(omega) f(q^(-1)omega).
```

Subtract this identity from the two terms in `(KHB3)` and apply
`(KHB7)` twice. This proves `(KHB3)`.

Finally, consider exact blocks of dimensions `d_omega), with total
dimension `D), and put `p(omega)=d_omega/D`. To match the
`omega)-block with the `s omega)-block by partial isometries, the
least possible unmatched dimension, normalized by `D`, is

```text
(1/D) sum_omega (d_omega-d_(s omega))_+
 =(1/2) sum_omega |p(omega)-p(s omega)|
 =h_s(p).                                                (KHB8)
```

Thus `o(D)) total holes imply `eta=o(1)). If a kernel mark
`a` has normalized block observable

```text
f_a(omega)=||pi_omega(a)-1||_2^2
```

and the exact label covariance identifies the observable of
`q a q^(-1)` with `f_a after q^(-1)`, equation `(KHB3)` makes
their global squared lengths asymptotically equal. Hence no
multiplicity-only matching can separate conjugate closing and head
roots by a positive amount.

The proof uses property T only after the ansatz has produced the
genuine permutation representation `pi`. It therefore does not
contradict the general property-T firewall, where arbitrary
normalized-HS microstates supply no such exact label action.
