---
rg: 2
id: isw-corollary-b-uses-only-the-standard-area-cocycle-proof
kind: route
title: Read the Corollary B text and compute the alternating square of the symmetric square by hand
target: isw-corollary-b-uses-only-the-standard-area-cocycle
requires: []
---

Clauses (i) and (ii) are statement-level transcriptions of
arXiv:2006.01874, read at source 2026-08-21: Corollary B on p. 2; the
`R = Z` construction in Section 3.2, p. 11 (area form `xt - yz`,
extension by `c((a,g),(b,h)) = c(a, g.b)`,
`c_k(g,h) = exp(2 pi i c(g,h)/k)`, non-coboundarity of `c_k|_{Z^2}` via
non-symmetry at `g = (1,0), h = (0,1)`, factorization through
`Gamma_k = (Z/k)^2 x| SL_2(Z/k)` and the projective representation
`pi_k: Gamma_k -> U(l^2(Gamma_k))` attached to the quotient class
`mu_k`); the general-ring case and the co-induction clause on p. 12
(ideals `I_k` with `R/I_k` finite via Baumslag's residual finiteness of
finitely generated commutative rings, characters `phi_k` with
`phi_k -> 1` and `phi_k(2x_k) != 1`, relative property (T) of
`(Omega, R^2)` from Shalom [Sh99, Cor. 3.5], and co-induction citing
the proof of [Io11, Prop. 4.5]).

Clause (iii) is a finite hand computation using only the two INTEGRAL
unipotents, so no Zariski-density input is needed.  On the basis
`(e^2, ef, f^2)` of `Sym^2(Q^2)`:

```text
u: e -> e, f -> e+f   acts by U = [[1,1,1],[0,1,2],[0,0,1]],
l: e -> e+f, f -> f   acts by L = [[1,0,0],[2,1,0],[1,1,1]].
```

An alternating form has Gram matrix `M = [[0,p,q],[-p,0,r],[-q,-r,0]]`.
Computing `U^T M U` gives entries `(1,3) = 2p + q` and
`(2,3) = p + q + r`; equality with `M` forces `p = 0` then `q = 0`.
With `p = q = 0`, the `(1,2)` entry of `L^T M L` is `r`; equality with
`M` (whose `(1,2)` entry is `0`) forces `r = 0`.  Hence the only
`{u,l}`-invariant alternating form is zero; a fortiori there is no
`SL_2(Z)`- or `GL_2(Z)`-invariant nonzero alternating form on
`Sym^2(Q^2)`, nor on `Sym^2(Z^2)` (tensor with `Q`).
