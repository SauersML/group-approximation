---
rg: 2
id: rank-five-rectangle-one-letter-proof
kind: route
title: Invert the two nonzero C3 Fourier-edge coefficients inside F4
target: rank-five-rectangle-is-one-letter-hecke-element
requires:
  - z-fixed-support-five-hecke-normal-form
artifacts:
  - research/artifacts/rank-five-rectangle-one-letter-reduction-2026-08-21.md
---

The corner algebra `eF_2[H]e` is the nontrivial simple summand of
`F_2[C_3]`, hence is `F_4` with identity `e`.  In particular

```text
p=e(1+[r])e=1+[r],       q=e(1+[s])e=1+[s]
```

are nonzero and therefore invertible in this corner.  Since
`alpha z=z alpha=z`, its `e`-component is `a=e alpha e=alpha+z`, and direct
expansion gives

```text
a=[h_0]e+p[x]q.
```

Multiplying on the left by `p^(-1)` and on the right by `q^(-1)` yields

```text
p^(-1) a q^(-1)=c+e[x]e,
c=p^(-1)[h_0]e q^(-1) in F_4^x.
```

The multiplicative group `F_4^x` is precisely `{[h]e:h in H}`, so write
`c=[h]e`.  Multiplication by the corner unit `[h]^(-1)e` converts the last
display to

```text
e+e[h^(-1)x]e=e(1+[y])e,       y=h^(-1)x.
```

Since `h in H`, membership in `N_G(H)` is unchanged, so `y` remains outside
the normalizer.  Left/right multiplication by corner units bijects one-sided
inverse pairs and conjugates the reverse product, preserving whether it is
the corner identity.
