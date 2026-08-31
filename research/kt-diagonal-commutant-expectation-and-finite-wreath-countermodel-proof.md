---
rg: 2
id: kt-diagonal-commutant-expectation-and-finite-wreath-countermodel-proof
kind: route
title: Preserve the BCJM diagonal under Gamma rounding and isolate the missing Laurent extension
target: gamma-only-exactification-preserves-the-diagonal-but-not-the-kt-return
requires:
  - amenable-lamp-rounding-preserves-the-kt-named-return-wall
  - kt-elementary-kazhdan-packet-rounds-base-lamp
  - kt-full-kazhdan-majorana-return-collapses-in-fd
---

# 1. Round into the exact Gamma commutant

For every `s in K`,

~~~text
||[p,pi(s)]||_2
 <=||[p,u_s]||_2+2||u_s-pi(s)||_2
 <=delta+2 epsilon.                                      (DCE1)
~~~

Apply `kt-elementary-kazhdan-packet-rounds-base-lamp` to the genuine
representation `pi`. It gives a projection `P in pi(Gamma)'` with

~~~text
||p-P||_2
 <=(sqrt(2)/kappa_K)(delta+2 epsilon)=eta.                (DCE2)
~~~

This is the only place where property `(T)` is used.

# 2. Return to the diagonal masa

Let

~~~text
a=E_D(P).
~~~

Conditional expectation is the orthogonal projection from `L^2(M_d)`
onto `L^2(D)`. Since `p in D`,

~~~text
||a-p||_2=||E_D(P-p)||_2<=||P-p||_2<=eta.                (DCE3)
~~~

Moreover, `a` is the closest element of `D` to `P`. Therefore

~~~text
||P-a||_2<=||P-p||_2<=eta.                               (DCE4)
~~~

In fact the Pythagorean identity gives

~~~text
||P-p||_2^2=||P-a||_2^2+||a-p||_2^2.                    (DCE5)
~~~

The element `a` is a diagonal positive contraction. Put

~~~text
e=1_[1/2,1](a) in D.
~~~

At every diagonal coordinate where `e` and `p` differ, the corresponding
coordinates of `a` and `p` differ by at least `1/2`. Hence

~~~text
||e-p||_2^2<=4||a-p||_2^2,
||e-p||_2<=2 eta.                                        (DCE6)
~~~

This proves `(GDE1)--(GDE3)`. It also identifies a useful but limited
classical remnant. For `s in Gamma`, define the unistochastic map on the
diagonal by

~~~text
T_s(x)=E_D(pi(s)xpi(s)^*).
~~~

Because `P` commutes with `pi(s)`,

~~~text
||T_s(a)-a||_2
 =||E_D(pi(s)(a-P)pi(s)^*)||_2
 <=||a-P||_2<=eta.                                       (DCE7)
~~~

The family `(T_s)` need not be a group action: inserting `E_D` between
two conjugations generally makes `T_sT_t!=T_(st)`. Thus `(DCE7)` is not
a finite permutation action to which the Kazhdan gap can be applied again.
It is simply another expression of the surviving multiplicity problem.

# 3. An exact trace-faithful Gamma-only countermodel

The ring `F_2[x_1,x_2,x_3]` is residually finite. Consequently `Gamma`
has finite quotients

~~~text
q_n:Gamma -> Q_n
~~~

which separate every fixed nonidentity element eventually. One may obtain a
single sequence by taking cumulative products of finite ring specializations.
Let `lambda_(Q_n)` be the left regular representation.

Now put

~~~text
B=(C_2)^4,
F=B rtimes <t>,
t^4=1,
t z_i t^(-1)=z_(i+1 mod 4).                              (DCE8)
~~~

Let `lambda_F` be the left regular representation of this finite
semidirect product, set

~~~text
rho_n(g,f)=lambda_(Q_n)(q_n(g)) tensor lambda_F(f),
U_n=1 tensor lambda_F(t),
V_n=1 tensor lambda_F(z_0),
p_n=(1+V_n)/2.                                           (DCE9)
~~~

Fourier transform the `B` coordinate in `ell^2(F)`. The matrices
`lambda_F(b)`, `b in B`, are then diagonal. In particular `p_n` is a
literal diagonal projection of normalized trace `1/2`.

The representation `rho_n` of `Gamma times F` is genuine. Its
restriction to `Gamma` commutes with `p_n`, and `U_n` even commutes
with the entire Gamma image. The traces are canonical: if `f!=1`, the
regular trace of `lambda_F(f)` is zero; if `f=1` and `g!=1`, then
the regular trace of `lambda_(Q_n)(q_n(g))` is eventually zero.

Put

~~~text
W_n=U_nV_nU_n^*=1 tensor lambda_F(z_1),
r_n=(1+W_n)/2.
~~~

The three finite-group elements `z_0,z_1,z_0z_1` are nonidentity, so their
regular traces vanish. Therefore

~~~text
tr(p_n)=tr(r_n)=1/2,
tr(p_nr_n)=1/4,                                          (DCE10)

||[p_n,U_n]||_2^2
 =||p_n-r_n||_2^2
 =1/2.                                                   (DCE11)
~~~

This proves `(GDE4)` with every error equal to zero. It also matches the
entire canonical two-lamp Boolean table, not merely the ranks of the two
projections. Since `Gamma` has property `(T)`, the example proves that
property `(T)`, exact Gamma multiplication, a diagonal lamp, canonical
trace, and exact normalization of the Gamma image do not control an external
return.

# 4. Why the actual h is different

The countermodel deliberately represents a direct-product return `t`.
It cannot be extended to a representation of the pinned Laurent elementary
actor while keeping the wall. In every genuine finite-dimensional
representation

~~~text
rho:E=EL_3(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) -> U(D),
~~~

finite-image compression gives

~~~text
rho(E)=rho(Lambda)<=rho(Gamma).
~~~

In particular `rho(h) in rho(Gamma)`. A
`rho(Gamma)`-central projection then commutes with `rho(h)`, and the
wall vanishes. This is exactly the argument in
`kt-full-kazhdan-majorana-return-collapses-in-fd`.

Thus the live input is not exactification of the subgroup tuple
`theta_n|Gamma` by itself. It is one coherent exactification which also
places the supplied matrix for `h` in the corresponding Laurent actor
representation.

# 5. Stability literature audit

The pinned subgroup is a rank-three elementary group over a three-variable
polynomial ring, not `SL_3(Z)`.

First, the unrestricted same-dimensional theorem is false. The group is
infinite, residually finite, hyperlinear, and Kazhdan. Becker--Lubotzky,
arXiv:1809.00632, prove that every infinite hyperlinear property-`(T)`
group fails normalized-Hilbert--Schmidt stability. Their theorem does not
exclude a source-specific correction for restrictions of canonical
Kun--Thom wreath microstates, but it prevents importing a general strict
exactification theorem.

Second, the character classification of Lavi--Levit, arXiv:2007.15547,
assumes

~~~text
d>max{stable_range(R),2}.                                 (DCE12)
~~~

Its stated general theorem does not supply the pinned `d=3` case over
`R=F_2[x_1,x_2,x_3]`; the standard Bass dimension estimate gives only
`stable_range(R)<=4`, which does not imply the strict inequality
`3>stable_range(R)` needed in `(DCE12)`. More importantly, classification of limiting
characters is not by itself a perturbation theorem for a prescribed
regular-character microstate.

Third, the known hyperfinite-HS conclusions from character rigidity do not
cover this restriction. Its limiting character is `delta_e`, whose GNS
algebra is `L(Gamma)`; since the infinite Kazhdan group `Gamma` is
nonamenable, this is not the amenable-GNS sector.

Finally, weak-ucp or flexible HS stability strong enough to produce a
nearby representation on the `K union {h}` interface is not proved for
this universal-lattice group in the audited sources. Property `(T)`
rounds a projection after a genuine actor has been supplied, as in Sections
1--2; it does not construct that actor. The global route therefore remains
open precisely at source-specific Laurent-actor exactification.
