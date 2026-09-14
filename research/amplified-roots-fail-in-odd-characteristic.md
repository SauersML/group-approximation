---
rg: 2
id: amplified-roots-fail-in-odd-characteristic
kind: claim
title: In every odd characteristic, a unimodular equation with dihedral permutation constants has no approximate roots in normalized rank at any amplification
distinct_from:
  amplified-algebraic-roots-for-nonsingular-equations: that is the universal root premise ARR(L) for every algebraically closed L; this is one explicit family of constants and words showing ARR(L) fails whenever the characteristic of L is odd.
  char-two-jordan-square-root-needs-amplification: that shows exact roots can need amplification in characteristic 2; this shows that in odd characteristic no amplification gives even approximate roots.
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

**ESTABLISHED** through `amplified-roots-fail-in-odd-characteristic-proof`
(direct proof, linear algebra only; unreviewed, no novelty claimed).

**Statement.** Let `p` be an odd prime and `L` any field of characteristic `p`.
Let `a, b` in `GL_p(L)` be the permutation matrices of two distinct
reflections of the regular `p`-gon (acting on `Z/p`), so `c = ab` is the
matrix of a `p`-cycle. Put `k = (p+1)/2` and

```text
w_p = x^k a x^{-(k-1)} b ,      exponent sum 1 in x .
```

Then for every `r >= 1` and every `T` in `GL_{pr}(L)`,

```text
rho( w_p(T ; a (x) 1_r , b (x) 1_r) - 1 )  >=  (p-1) / (p^2 K_p),
K_p = (p+2)(4p-3)/p + p(p+2) + 2(p^2+1),
```

where `rho` is the normalized rank. For `p = 3` the bound is `1/225`.

**The Groebner instance.** For `p = 3` and `a = (0 1)`, `b = (0 2)`, the
substitution `x -> x a` sends `x a x a x^{-1} b` to `x^2 a x^{-1} b = w_3`
with the same defect. So the MSI finding of
`research/artifacts/ideas-nonhyperlinear-2026-09-13.md` (no exact root at
`r = 1` over the algebraic closure of `F_3`) extends to: no approximate root at
any amplification, with defect at least `1/225`.

**Consequences.**
- `amplified-algebraic-roots-for-nonsingular-equations` is refuted: `ARR(L)`
  fails for every algebraically closed `L` of odd characteristic.
- `linear-sofic-kl-from-amplified-algebraic-roots` gives nothing for groups
  that are `F`-linear sofic only over fields `F` of odd characteristic, since
  every extension of `F` has the same characteristic.
- The proof uses the Frobenius identity `(s-1)^p = s^p - 1` and a semisimple
  involution. Characteristic 0 is untouched and stays open as
  `amplified-algebraic-roots-in-characteristic-zero`; characteristic 2 is
  undecided.
- This is not a Kervaire--Laudenbach failure: the adjunction of `D_p = <a,b>`
  along `w_p` is `D_{p^2}` (proof, remark), which contains `D_p`. What fails is
  realizing the root on a module that restricts to the amplified permutation
  module, even approximately.
