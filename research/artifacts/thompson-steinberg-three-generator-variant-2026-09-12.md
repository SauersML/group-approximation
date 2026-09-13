# Three generators, sixteen relators: Bleak--Quick's two-generator V plus one transvection

Lane `ex-free-objects`, 2026-09-12. Unreviewed. A variant of
`research/artifacts/thompson-steinberg-presentation-2026-09-12.md`, whose conventions are used here.

## The presentation

Generators `u, v, x`. With `{}^g q = g q g^-1`:

```text
(V)  Bleak--Quick Theorem 1.3: u^6, v^3, (u^3 v)^4 and four words of lengths 69, 31, 25, 35
(X)  x^2,   (u^3 x)^3
(H)  [x, sigma_1 sigma_2 sigma_3],   [x, sigma_4 sigma_5]
(B)  [x, {}^(v^-1 u^3 v u^2 v^-1) x],   [x, {}^(v^-1) x],   [x, {}^(u^3 v^-1 u) x]
(C)  [x, {}^(u^3 v^-1) x] = {}^(v^-1) x
(Q)  {}^(u v^-1 u^-1 v^-1 u^-1 v^-1) x . {}^(u v^-1 u v^-1 u v^-1) x = x
```

In (H), each `sigma_i` is a conjugate `{}^(g_i) u^3` of `u^3 = (00 01)`, representing a swap:

```text
sigma_1 = (100 101)    g_1 = v u^-1 v^-1 u^3 v u^2 v^-1
sigma_2 = (110 1110)   g_2 = u v u^2 v^-1 u v^-1 u
sigma_3 = (110 1111)   g_3 = u v u^-2 v^-1 u v^-1 u
sigma_4 = (101 110)    g_4 = v u^-2 v^-1 u^-1 v^-1
sigma_5 = (101 111)    g_5 = v u^-2 v^-1 u v^-1
```

(the products are in the order that matched exactly). Then `sigma_1 sigma_2 sigma_3 = iota_1(u)`
and `sigma_4 sigma_5 = iota_1(v)`, which generate the copy of `V` on the cone `1`.

Sixteen relators, total literal length 467; the longest, `[x, iota_1(u)]`, has length 108. Literal
words: `experiments/nonsofic-certificates/presentations/thompson-steinberg-uv-presentation.json`.

Images: `u -> U_(00 01) U_(10 110) U_(10 111)`, `v -> U_(01 10 11)^-1`, `x -> 1 + S[00]T[01]`,
with `U_g e_w = e_(w.g)`. Of the four orientation readings of `u, v`, only the two with
`v -> U^-1` satisfy Theorem 1.3. The two `u` readings give inverse elements, and either works.

**Theorem.** These images define an isomorphism `<u, v, x | 16 relators> -> L_(F_2)(1,2)^x`.

## Proof

Steps 0-5 of the four-generator artifact apply verbatim, with three substitutions.
- Step 0 uses Bleak--Quick Theorem 1.3 instead of (2.4).
- Step 1 uses the generators `iota_1(u), iota_1(v)` of the pointwise stabilizer of the cones
  `00, 01`. They generate it because `u, v` generate `V` and `iota_1 : V -> Stab` is an isomorphism.
- In Step 5, `(u^3 x)^3 = 1`, `u^6 = 1` and `x in N` give `u^3 in N`. So the quotient map
  `V -> Q/N` kills `u^3 = (00 01) != 1`, and simplicity of `V` gives `Q/N = 1`.

The configuration relators are the same five, at the same base cones. Step 4 sends `t -> u^3`.

## Verification record

`experiments/nonsofic-certificates/presentations/verify_thompson_steinberg_uv.py`, MSI, 1.2 s,
PASS.
- All seven Theorem 1.3 relators hold in `L^x`, and `u^3 = U_(00 01)` exactly.
- BFS over `u^(+-1), v^(+-1)` explored 21,497 elements and found all eleven conjugators. Each
  predicate was rechecked in dual mode.
- The exact images `iota_1(u)`, `iota_1(v)` and the six transvections all match.
- All sixteen relators hold in `L^x`.
- Negative controls `(vx)^3`, `[x,u^3]`, `[x,T(01,10)]` and `[x,u]` are all nontrivial.

An earlier run searched directly for conjugators of `u` and `v` onto the cone `1`, which are
five-cone and three-cone predicates. At depth 12 and 126,772 elements it found none, so they
were assembled from swaps instead.

## Comparison

| presentation | generators | relators | total length | longest |
| --- | --- | --- | --- | --- |
| atlas `T_St` (central extension only) | 12 | 4,648 | > 713,754 | 595 |
| Steinberg-Weyl | 7 | 60 | 1,007 | 38 |
| Thompson-Steinberg, Theorem 2.1 words (2.4) | 4 | 18 | 322 | 37 |
| Thompson-Steinberg, Theorem 1.3 | 3 | 16 | 467 | 108 |
