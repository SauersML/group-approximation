---
rg: 2
id: weyl-reverser-computation-proof
kind: route
title: Four one-line conjugations and a fixed-point count give the normalizer
target: weyl-reverser-blocks-naive-swap-twist-descent
requires:
  - swap-twist-centralizer-is-the-congruence-core
---

`w_13 = [[0,0,1],[0,-1,0],[1,0,0]]` has determinant `1`, order `2`, and
conjugates `diag(a, b, c)` to `diag(c, b, a)`; in particular
`w_13 h w_13^(-1) = h^(-1)`.

**The involution.**  `x_0^2 = h w_13 h w_13 = h (w_13 h w_13^(-1))
w_13^2 = h h^(-1) = e`.  `x_0 notin Lambda` because `h notin Lambda`
and `w_13 in Lambda`.

**The swap.**  `w_13 in Lambda` commutes with `s`, so

```text
x_0 s x_0^(-1) = h w_13 s w_13^(-1) h^(-1) = h s h^(-1),
x_0 (h s h^(-1)) x_0^(-1)
  = h w_13 h s h^(-1) w_13^(-1) h^(-1)
  = h (w_13 h w_13^(-1)) (w_13 s w_13^(-1)) (w_13 h^(-1) w_13^(-1)) h^(-1)
  = h h^(-1) s h h^(-1) = s.
```

Hence `x_0 z x_0^(-1) = x_0 s x_0^(-1) . x_0 h s h^(-1) x_0^(-1)
= (h s h^(-1)) s = z^(-1)` (the product of the two involutions in the
opposite order).

**Normalizing the core.**  `w_13 C_0 w_13^(-1) = w_13 (Lambda cap
h Lambda h^(-1)) w_13^(-1) = Lambda cap h^(-1) Lambda h`, and
conjugating by `h` sends `Lambda cap h^(-1) Lambda h` to
`h Lambda h^(-1) cap Lambda = C_0`.  So `x_0 C_0 x_0^(-1) = C_0`.

**The normalizer.**  Let `gamma in Gamma` normalize `<z>`.  Since `z`
is hyperbolic on the Bass--Serre tree (translation length `4`,
`swap-twist-centralizer-is-the-congruence-core`), `gamma z gamma^(-1)`
is hyperbolic with the same translation length and axis `gamma l`, and
`gamma z gamma^(-1) = z^(+-1)` forces `gamma l = l`.  If
`gamma z gamma^(-1) = z` then `gamma in C_Gamma(z) = C_0`.  If
`gamma z gamma^(-1) = z^(-1)` then `x_0 gamma` centralizes `z`
(`x_0 gamma z (x_0 gamma)^(-1) = x_0 z^(-1) x_0^(-1) = z`), so
`x_0 gamma in C_Gamma(z) = C_0`, i.e. `gamma in x_0 C_0`.  This proves
`(WR1)`; both cosets are realized (`e` and `x_0`).

**The moment.**  In any unitary model, `pi(x_0) z pi(x_0)^(-1) z =
z^(-1) z = 1` holds as an operator identity, so its trace is `1`; the
amalgamated-freeness prediction for the centered alternating four-letter
word is `0`.  The contradiction is exact and model-independent.
