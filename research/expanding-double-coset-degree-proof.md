---
rg: 2
id: expanding-double-coset-degree-proof
kind: route
title: Reduce mod p squared and count a Borel times a hyperplane of the congruence kernel
target: expanding-double-coset-degree-is-p-times-flags
requires: []
---

The coset count of a double coset is the index of the intersection:
`Lambda h Lambda / Lambda` is in bijection with
`Lambda / (Lambda cap h Lambda h^(-1))`.

**The intersection is a mod-`p^2` condition.**  Conjugation by
`h = diag(p, 1, p^(-1))` scales the entry `(i, j)` by `d_i / d_j`
with `d = (p, 1, p^(-1))`, so `h A h^(-1)` is integral iff

```text
p | a_21,   p^2 | a_31,   p | a_32.                             (DCP1)
```

Since `SL_3(Z) -> SL_3(Z/p^2)` is surjective (strong approximation /
elementary generation), the index equals `[SL_3(Z/p^2) : S]` where
`S` is the subgroup defined by `(DCP1)` mod `p^2`.

**Counting `S`.**  `|SL_3(Z/p^2)| = p^8 |SL_3(F_p)|` (the reduction
kernel is `{A_0 (1 + pX)}`-torsor with `X in M_3(F_p)`, `tr X = 0`:
`p^8` elements).  The image of `S` mod `p` is the lower-Borel
condition `a_21 = a_31 = a_32 = 0`, the Borel subgroup `B(F_p)`.
Over a fixed `A_0` with reduction in `B`, the fiber of lifts is the
kernel torsor `{A_0 (1 + pX)}`, and the residual condition
`p^2 | a_31` reads `c + (A_0 X)_31 = 0 (mod p)` where
`(A_0)_31 = p c`.  Because the reduction of `A_0` lies in `B`, its
third row mod `p` is `(0, 0, a_33)` with `a_33 != 0`, so
`(A_0 X)_31 = a_33 X_31`: the condition is affine-linear in the free
coordinate `X_31` (unconstrained by `tr X = 0`), and exactly `1/p` of
the fiber satisfies it.  Hence `|S| = |B(F_p)| p^7` and

```text
[SL_3(Z/p^2) : S] = p^8 |SL_3(F_p)| / ( p^7 |B(F_p)| )
                  = p [SL_3(F_p) : B(F_p)]
                  = p (p + 1)(p^2 + p + 1),                     (DCP2)
```

the flag count of `F_p^3` (choose a line, `p^2 + p + 1`; then a
plane through it, `p + 1`) times `p`.  This is `(DC1)`.

**Sanity check at rank one.**  The same computation for `SL_2`,
`h = diag(p, p^(-1))`, condition `p^2 | c`, gives
`p [SL_2(F_p) : B] = p (p + 1)` — the classical degree of the
`diag(p, p^(-1))` Hecke operator on `PGL_2` (`6` at `p = 2`),
confirming the method.

**The fingerprint.**  For the exact quasi-regular profile
`psi_k = 1_Lambda`, the conjugates `pi(w_i) k pi(w_i)^*` are pairwise
orthonormal and orthogonal to `k` (`1_Lambda(w_j^(-1) w_i) =
delta_(ij)`), so

```text
|| S(k) ||_2^2 = 1/4 + (1/(4 L^2)) * L = 1/4 + 1/(4 L),
```

which at `L = 42` is `43/168`, `(DC2)`.
