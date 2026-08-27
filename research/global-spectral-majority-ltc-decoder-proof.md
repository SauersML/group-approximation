---
rg: 2
id: global-spectral-majority-ltc-decoder-proof
kind: route
title: Decode cloud majorities pointwise on the common spectrum and paste the code characters
target: balanced-occurrences-have-linear-character-decoder
requires: []
---

Let `N=W^*(A_(i,v))`.  Since `N` is abelian, write
`N=L_infinity(Omega,mu)` and

```text
 A_(i,v)(omega)=(-1)^(a_(i,v)(omega)),
 a_(i,v)(omega) in F_2.                                 (GCP1)
```

All choices below are among finite sets, so fix lexicographic tie breaking;
the resulting functions of `omega` are measurable.  For each coordinate
choose the stationary cloud majority `b_i(omega)`.  If `p_i(omega)` is the
minority stationary mass in that cloud, then

```text
 sum_v lambda_(i,v)
   |A_(i,v)(omega)-(-1)^(b_i(omega))|^2=4p_i(omega).
                                                                  (GCP2)
```

For signs, distance to the nearer constant is at most twice variance about
the mean.  The scalar expander Poincare inequality therefore gives

```text
 4p_i(omega)
 <=(2/lambda) E_((u,v) equality edge i)
       |A_(i,u)(omega)-A_(i,v)(omega)|^2.               (GCP3)
```

Average with `nu_i` and put `m(omega)=sum_i4nu_i p_i(omega)`.  Thus
`int m dmu<=C E_eq`.

Now fix an original check `h`.  On every repeated copy `t` of `h`, either
its local parity word is wrong, or, if `Hb(omega)` is nonzero at `h`, at
least one occurrence `(i,h,t)` differs from its cloud majority.  Pointwise,

```text
 1_(Hb(omega))_h=1
 <=1_(local parity of (h,t) is wrong)
   +sum_(i in h)1_(a_(i,h,t)(omega)!=b_i(omega)).       (GCP4)
```

Average `(GCP4)` over the repeated copies and over original checks.  The
incidence domination `(GCD0)` gives, pointwise,

```text
 |Hb(omega)|/M
 <=e_orig(omega)
   +C_inc sum_i nu_i sum_v lambda_(i,v)
                  1_(a_(i,v)(omega)!=b_i(omega))
 <=e_orig(omega)+(C_inc/4)m(omega).                     (GCP5)
```

where `int e_orig dmu=E_orig/4` up to the fixed normalization convention.
By `(GCD1)`, choose a nearest `c(omega) in ker H` with

```text
 |b(omega)-c(omega)|/L
 <=C(e_orig(omega)+m(omega)).                           (GCP6)
```

Because `nu_i<=C/L`, `(GCP6)` also implies

```text
 sum_i nu_i 1_(b_i(omega)!=c_i(omega))
 <=C(e_orig(omega)+m(omega)).                           (GCP6a)
```

Let `P_c` be the indicator of `{omega:c(omega)=c}`.  These indicators form
a PVM in `N` and `(GCD2)` is its coordinate marginal.  Finally, pointwise,

```text
 1_(a_(i,v)!=c_i)
 <=1_(a_(i,v)!=b_i)+1_(b_i!=c_i).                      (GCP7)
```

The first term averages to `m(omega)/4`; `(GCP6a)` bounds the second by
`C(e_orig(omega)+m(omega))`.  Integrating and
using `(GCP3)` proves `(GCD3)`.

Every output face now consists of commuting reflections with the prescribed
parity product.  The standard binary atom formula

```text
 P_z^f=product_(i in f)(I+(-1)^(z_i)S_i)/2             (GCP8)
```

reconstructs its exact codeword PVM.  Fixed face width and telescoping make
the atom movement a fixed multiple of the marginal movement, completing
the same-Hilbert face statement.

For `(GCD5)`, choose a globally commuting tuple `A` within `o(1)` of the
infimum in `(GCD4)`.  For an equality word, the difference of residuals is
the difference of two coordinates.  For an original parity word, bounded
width and unitary telescoping give

```text
 ||r(A)-I||_2^2
 <=2||r(Q)-I||_2^2+C sum_(i in supp r)||A_i-Q_i||_2^2. (GCP9)
```

Bounded incidence and the balanced weights make the average last term
`O(d_ab(Q)^2)`.  Apply `(GCD3)` to `A`, and use the squared triangle
inequality once more between `Q`, `A`, and its decoded code tuple.  Taking
the infimum proves `(GCD5)`.
