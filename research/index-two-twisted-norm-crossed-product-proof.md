---
rg: 2
id: index-two-twisted-norm-crossed-product-proof
kind: route
title: The division closure is a rank-2 crossed product over D(N), and its left ideals are lines D(a + h)
target: index-two-strong-atiyah-is-a-twisted-norm-equation
requires: []
---

**Input.** For torsion-free `G`, Strong Atiyah over `K` holds if and only if
`D_K(G)` is a division ring. This is Linnell's theorem, as recorded in
`strong-atiyah-torsion-free` (see Lueck, *L^2-invariants*, Lemma 10.39). It was not
re-read here.

Put `D = D_K(N)`, `R = D + Dh` inside `U(G)`, and `c = h^2`, which lies in `N`.

**R is a ring containing `K[G]`.** `h K[N] h^-1 = K[N]`, and conjugation by `h`
preserves `U(N)` and division closure. So `hDh^-1 = D`, `hd = sigma(d) h`, and
`h^2 = c` is in `D`. The sum is direct: as operators on
`l^2(G) = l^2(N) + l^2(N) h`, the elements of `U(N)` preserve the first summand
and those of `U(N) h` exchange the two.

**`R = D_K(G)`.**
- *`R` is division closed in `U(G)`.* Let `r` in `R` be invertible in `U(G)`.
  Right multiplication by `r` is a left `D`-linear injection `R -> R`, since
  `sr = 0` gives `s = s r r^-1 = 0`. `R` is 2-dimensional over `D`, so this map is
  onto, `sr = 1` for some `s` in `R`, and `r^-1 = s` lies in `R`. So
  `D_K(G) <= R`.
- *`D <= D_K(G)`.* `D_K(G) cap U(N)` contains `K[N]`. It is division closed in
  `U(N)`: an element of `U(N)` invertible in `U(N)` is invertible in `U(G)`, so its
  inverse lies in `D_K(G) cap U(N)`. So it contains `D`, and with `h` it gives
  `R <= D_K(G)`.

**`R` fails to be a division ring iff `sigma(a) a = c` has a solution.**
- *Solution gives a proper ideal.* If `sigma(a) a = c`, then
  `h(a + h) = sigma(a) h + c = sigma(a)(a + h)`. So `D(a + h)` is a left ideal of
  `R`, nonzero and of `D`-dimension 1, hence proper.
- *No division gives a solution.* Suppose `R` is not a division ring. Take `r != 0`
  not invertible. `R` is left Artinian, so a one-sided inverse is two-sided, and
  `Rr` is a proper nonzero left ideal of `D`-dimension 1, say `D(a + bh)`.
  - Left ideal: `h(a + bh) = sigma(b) c + sigma(a) h` equals `lambda (a + bh)` for
    some `lambda` in `D`. So `sigma(b) c = lambda a` and `sigma(a) = lambda b`.
  - If `b = 0`, then `sigma(a) = 0`, so `a = 0`, which is impossible. So scale to
    `b = 1`.
  - Then `lambda = sigma(a)`, and `c = lambda a = sigma(a) a`.

With the input, item 2 follows.
