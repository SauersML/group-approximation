---
rg: 2
id: hrf-audit-stability-prime-central-finite-residuals-proof
kind: route
title: Unbounded finite central orders give nonroundable projective sectors; bounded orders kill almost every prime kernel
target: hrf-audit-stability-forces-prime-central-finite-residuals
requires:
  - bdhv-central-extension-property-t
artifacts:
  - research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md
---

We give the finite-dimensional argument directly rather than importing the
stronger Dogon--Vigdorovich nonhyperlinearity theorem.

Suppose the orders of `z` in finite quotients `q_n:E->Q_n` are unbounded; after
passing to a sequence they are `m_n -> infinity`. In the left regular
representation of `Q_n`, the eigenspace of `q_n(z)` for
`lambda_n=exp(2 pi i/m_n)` has dimension `d_n=|Q_n|/m_n>0`. It is invariant because
`z` is central. The resulting genuine representation `rho_n:E->U(d_n)` satisfies
`rho_n(z)=lambda_n I`.

Fix a section `s:Gamma->E`, with `s(1)=1`, and put `alpha_n=rho_n o s`. If
`s(g)s(h)=z^{k(g,h)}s(gh)`, then

```
alpha_n(g)alpha_n(h)=lambda_n^{k(g,h)} alpha_n(gh).
```

Thus `alpha_n` is asymptotic, even in operator norm. Stability would give genuine
`pi_n:Gamma->U(D_n)`, with `D_n>=d_n`, `D_n/d_n->1`, and compressions approaching
`alpha_n`. Let `P_n:C^{D_n}->C^{d_n}` be the comparison co-isometry. On rectangular
matrices with norm `||X||^2=Tr(X*X)/d_n`, consider the genuine representation

```
sigma_n(x)X = rho_n(x) X pi_n(q(x))*.
```

The unit vector `P_n` is asymptotically invariant. Indeed, for fixed `x in E`,
write `x=z^k s(q(x))`; the scalar error tends to zero and

```
||alpha_n(q(x))P_n-P_n pi_n(q(x))||^2
 <= ||alpha_n(q(x))-P_n pi_n(q(x))P_n*||^2 + (D_n-d_n)/d_n -> 0.
```

However, `sigma_n(z)X=lambda_n X`, so `sigma_n` has no nonzero invariant vector.
A fixed Kazhdan pair for `E` contradicts the almost invariance of `P_n`.

Therefore all finite central orders are at most some `B`. Taking
`M=lcm(1,...,B)` makes every finite quotient of `E` kill `z^M`. For a prime
`p` not dividing `M`, any finite quotient of `E_p` pulls back to a finite
quotient of `E`. The order of the image of `z` divides both `p` and `M`, so it is
one. Its class in `E_p` has exact order `p`, because `<z>` is an injected infinite
cyclic subgroup. This proves item 1.

If the extension `E_p` split over finite-index `L<=Gamma`, the image of a splitting
would be a finite-index subgroup `S<=E_p` disjoint from its central `C_p`. The
normal core of `S` has finite index and is still disjoint from `C_p`, giving a
finite quotient that detects the centre, a contradiction. This proves item 2.

A finite-kernel surjection of finitely generated groups is a quasi-isometry;
thus hyperbolicity of `Gamma` implies hyperbolicity of `E_p`.

Finally, if `Gamma` is hyperbolic Kazhdan and `b_2>0`, it is finitely presented,
`H_1(Gamma;Z)` is finite and `H_2(Gamma;Z)` has positive free rank. Choose an integral
cohomology class whose evaluation on `H_2` is nonzero, using the surjection from
universal coefficients. For its central extension, the five-term sequence is

```
H_2(Gamma;Z) -> Z -> H_1(E;Z) -> H_1(Gamma;Z) -> 0.
```

The first map has nonzero image, so `H_1(E;Z)` is finite. The required
`bdhv-central-extension-property-t` makes `E` Kazhdan and completes item 3.
