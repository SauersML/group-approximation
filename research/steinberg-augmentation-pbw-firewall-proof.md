---
rg: 2
id: steinberg-augmentation-pbw-firewall-proof
kind: route
title: Compute the root strings and a degree-jumping quotient class
target: steinberg-standard-augmentation-filtration-firewall
requires:
  - steinberg-fox-chord-actions-are-explicit
  - steinberg-zero-marginal-space-is-biaffine-circulation
---

Let `I=ker(k[G] -> k)` for `k=F_p` and `G=SL_3(F_p)`.  Since `G` is
perfect,

```text
I/I^2 = k tensor G_ab = 0.
```

Hence `I=I^2` and `I^n=I` for every `n>=1`.  The defect-zero Steinberg
block lies in `I` and is invisible in all positive associated-graded
quotients.

For the local obstruction, on a simple-root Steinberg string
`v_n=f_i^(n)v_+`, `0<=n<p`, direct binomial expansion gives

```text
A^(-1)v_n=sum_(j=0)^n 2^j binom(n,j)v_(n-j),
q^(-1)v_n=sum_(k=0)^(p-1-n) 2^(-k)binom(n+k,k)v_(n+k).
```

Thus for `T_1=(1-q^(-1))A^(-1)`,

```text
[T_1]_(r,n)=-2^(n-r)
 (binom(n+r,n)-1_(r<=n)binom(n,r)).                    (SAP1)
```

In particular, `T_1v_0` has a nonzero component in every grade
`1,...,p-1`, while `T_1v_(p-1)` has a nonzero grade-one component.  The
second simple root has the same binomial bracket, scaled by `2^(-r)`.
So neither ascending PBW nor descending Jennings degree is preserved.

There is also an obstruction intrinsic to the quotient by incidence-dual
potentials.  Write

```text
R=k[a,b,c]/(a^p-a,b^p-b,c^p-c),
U={alpha(a,b)+beta(c,ac-b)},       Q=R/U.
```

A row-echelon basis of `Q` consists of all `a^i b^j c^k` with `i,k>=1`,
except `a b^j c` for `0<=j<=p-2`: point potentials pivot the `c^0`
monomials, plane monomials `c^k(ac-b)^l` pivot the `a^0` terms, and
`(ac-b)^l-(-b)^l` pivots `ab^(l-1)c`.

For `p>=5`, take the normal class `phi=a^2c`.  It has `P=H=0`, so all
exceptional tree cuts vanish.  Modulo point potentials,

```text
(1-q^(-1))A^(-1)phi = c G(a),
G=a^2(1+2a)^(p-2)-(1/2)(a-1/2)^2 a^(p-2).             (SAP2)
```

After reducing `a^p=a`, the coefficients of `a` and `a^(p-1)` cancel,
while the coefficient of `a^(p-2)` is `1/4`.  The `B` term starts with
`a,b` degree at most two.  Its only additional quotient pivots produce
`a^t c^t` with `t<=3`, never `a^(p-2)c` (at `p=5`, the possible `t=3`
term has `c^3`).  The `-phi` term cannot cancel it either.  Therefore the
normal form of `X^*[phi]` contains `(1/4)[a^(p-2)c]`, proving the claimed
degree jump.
