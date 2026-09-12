---
rg: 2
id: regular-chart-wedderburn-coefficient-compiler-proof
kind: route
title: Insert Wedderburn matrix units between every two operators
target: regular-chart-wedderburn-coefficient-compiler
requires: []
---

Over `C`, Maschke and Wedderburn give a finite star-algebra decomposition

```text
C[G] ~= direct_sum_(sigma in G^) M_(d_sigma)(C).
```

Choose standard matrix units `e^sigma_ab` in each summand and represent them
through the left regular representation.  They satisfy

```text
(e^sigma_ab)* = e^sigma_ba,
e^sigma_ab e^tau_cd = delta_(sigma,tau) delta_(b,c) e^sigma_ad,
sum_(sigma,a) e^sigma_aa = 1.                        (W1)
```

The regular representation contains `sigma` with multiplicity `d_sigma`.
After tensoring with `C^k`, therefore,

```text
rank(e^sigma_aa)=d_sigma k,                           (W2)
```

so `p_sigma=e^sigma_11` is a fixed group-algebra projection exposing a
`d_sigma k`-dimensional coefficient corner.  In particular the corner size
is a fixed multiple of the external multiplicity and no choice depending on
`k` is involved.

For an arbitrary ambient operator `X`, define

```text
X^(sigma,tau)_(a,c)=e^sigma_(1,a) X e^tau_(c,1).
```

Multiplying this block on the left and right by the reverse matrix units and
using `(W1)` gives

```text
e^sigma_(a,1) X^(sigma,tau)_(a,c) e^tau_(1,c)
 = e^sigma_aa X e^tau_cc.
```

Summing over all indices and using the resolution of the identity in `(W1)`
yields the exact reconstruction formula

```text
X = sum_(sigma,tau,a,c)
      e^sigma_(a,1) X^(sigma,tau)_(a,c) e^tau_(1,c).  (W3)
```

Adjoints are immediate:

```text
(X*)^(tau,sigma)_(c,a)
 = (X^(sigma,tau)_(a,c))* .                           (W4)
```

For multiplication, insert the same finite resolution of the identity
between `X` and `Y`:

```text
(XY)^(sigma,upsilon)_(a,e)
 = e^sigma_(1,a) X
   (sum_(tau,c) e^tau_cc)
   Y e^upsilon_(e,1)

 = sum_(tau,c)
   (e^sigma_(1,a) X e^tau_(c,1))
   (e^tau_(1,c) Y e^upsilon_(e,1)),                  (W5)
```

which is exactly the asserted path-sum rule.

Equations `(W3)--(W5)` induct on word length, so every fixed star-polynomial
in finitely many ambient operators compiles to a finite coefficient program.
Every `e^sigma_ab` is a partial isometry of operator norm at most one, hence
left and right multiplication by it are contractions for the ambient
normalized Hilbert--Schmidt norm.  A fixed compiled program uses only
finitely many such compressions and finitely many sums.  Triangle and
Cauchy--Schwarz therefore introduce only constants determined by the fixed
finite index set, hence by `G` and the program, not by `k`.

This proves the claim.  For `G=A_8` the compiler is finite once and for all:
all dependence on a hypothetical hyperlinear coordinate is confined to the
finite family of coefficient blocks of its one relative chart unitary.