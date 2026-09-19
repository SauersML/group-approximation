---
rg: 2
id: stw84-square-root-covariance-and-fourier-row-gap-proof
kind: route
title: Use square-root covariance for the cutdown and balanced diagonal projections for the row obstruction
target: stw84-weighted-fourier-cutdown-and-row-gap
requires:
  - stw84-augmentation-ideal-has-finite-dimensional-folner-carriers
  - stw84-folner-carrier-corners-are-normal-closure-corners
artifacts:
  - research/artifacts/stw84-weighted-fourier-cutdown-audit-2026-08-30.md
---

## 1. Square-root covariance retains the positive weights

If `0<=r,s<=1`, the standard square-root estimate gives

```text
||r^(1/2)-s^(1/2)|| <= ||r-s||^(1/2).                 (WFC6)
```

Apply this to `r=alpha^k(h)` and `s=h`.  Equation `(WFC1)` gives

```text
||alpha^k(h^(1/2))-h^(1/2)|| <=sqrt(|k|/N).           (WFC7)
```

The exact carrier equation `ha=ah=a` implies
`h^(1/2)a=ah^(1/2)=a`: this follows by applying continuous functional
calculus to `h` on the left and right annihilators of `1-h`.  Using the
crossed-product relation `U^k b=alpha^k(b)U^k`,

```text
C_h(aU^k)
 =h^(1/2)aU^k h^(1/2)
 =a alpha^k(h^(1/2))U^k.
```

Subtract `aU^k=a h^(1/2)U^k` and use `(WFC7)`.  This proves `(WFC2)`;
the triangle inequality proves `(WFC3)`.  In particular, the square-root
loss is the only loss in this argument and the spectral floor of `h` never
enters.

## 2. The canonical weighted row is c.p.c.

Put

```text
v_i=n^(-1/2)h^(1/2)U^i       (0<=i<n)
```

and regard `v=(v_0,...,v_(n-1))` as a row over `A`.  Then

```text
Theta_(h,n)(c)=v c v^*,
sum_i v_i v_i^*=h.
```

Hence `(WFC4)` is completely positive and has norm
`||Theta_(h,n)(1)||=||h||=1`; it is c.p.c.  This is precisely the scalar
matrix restriction of the usual weighted return map paired with compression
to an `n`-point Fourier interval.

## 3. Balanced diagonal projections force a uniform gap

Let `S subset {0,...,n-1}` have `|S|=floor(n/2)`, and let `p` be the
diagonal projection onto `S`; put `q=1-p`.  The off-diagonal entries do not
occur in either projection, so

```text
Theta_(h,n)(p)=(|S|/n)h,
Theta_(h,n)(q)=((n-|S|)/n)h.                          (WFC8)
```

Their product has norm

```text
||Theta_(h,n)(p)Theta_(h,n)(q)||
 =|S|(n-|S|)/n^2,                                    (WFC9)
```

because `||h^2||=1`.  If `Psi:M_n->A` is c.p.c. order zero and
`epsilon=||Theta_(h,n)-Psi||`, then `Psi(p)Psi(q)=0`, while

```text
Theta(p)Theta(q)
 =[Theta(p)-Psi(p)]Theta(q)
  +Psi(p)[Theta(q)-Psi(q)].
```

Both `Theta(q)` and `Psi(p)` are contractions.  Thus `(WFC9)` is at most
`2epsilon`, proving the first inequality in `(WFC5)`.  For `n=2` it is
`1/8`; for odd `n>=3` its minimum is attained at `n=3` and equals `1/9`;
the even values are `1/8`.  This proves the uniform bound.

Finally, restriction of an order-zero map to a C-star subalgebra remains
order zero.  Therefore any order-zero perturbation of a coefficient-valued
row map on `M_n(D)` would restrict to an equally good perturbation of
`Theta_(h,n)` on `M_n tensor 1_D`, which is forbidden below `1/9`.

The argument obstructs only the unsplit canonical row.  It does not rule
out a different finite-dimensional factorization or a bounded collection
of order-zero return colours, and it makes no claim about the nuclear
dimension of `J`.
