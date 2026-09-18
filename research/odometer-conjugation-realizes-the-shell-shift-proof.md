---
rg: 2
id: odometer-conjugation-realizes-the-shell-shift-proof
kind: route
title: On N the odometer is the shift, and a tree automorphism is determined by its germ on the dense set N
target: odometer-conjugation-realizes-the-shell-shift
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

**Item 1.** Take `n >= 1` with `g(n-1) ∈ N`, which excludes only finitely many `n`. Then

    s g s^-1(n) = g(n-1) + 1 = (o g o^-1)(n),

computed in `Z_2`.

**Item 2.** Suppose `g|_N = h|_N`. Then `g` and `h` agree on a cofinite subset of `N`. That set is still dense in `Z_2`, because every cylinder contains infinitely many integers. Both maps are continuous, so `g = h`.

If `g != 1`, pick `x` with `g(x) != x`, and a cylinder `U ∋ x` small enough that `gU ∩ U = ∅`. Then `g` moves the infinitely many integers in `U`.

**Item 3.**
- *A genuine action with infinite supports.* The lift `rho` is a genuine action, and it has infinite supports by item 2.
- *Window zero.* By item 1, `s rho_g s^-1 = s (g|_N) s^-1 = (o g o^-1)|_N = rho_(psi(g))` in `NearSym(N)`, with `psi(g) = o g o^-1 ∈ G`.
- *The group `R_rho`.* Every element of `<G, o>` commensurates `N`. Restriction to a commensurated subset, `x ↦ x|_N`, is therefore a homomorphism `<G, o> -> NearSym(N)` sending `o` to `s`. It is injective by item 2, and its image is `<rho(G), s>`.
- *The ascending HNN structure.* Consider the natural map `G *_psi -> <G, o>` sending the stable letter to `o`. It is injective:
  - an element of `G *_psi` has normal form `t^-m g t^n` with `m, n >= 0`;
  - the index character takes the value `n - m` on its image, so a trivial image forces `n = m`;
  - then `o^-m g o^m = 1` gives `g = 1`. `∎`

**Item 4.**
- Suppose `g o = o g`. Then `g(x) = x + g(0)` on the dense set `Z`, so `g` is translation by `c = g(0) ∈ Z_2`.
- If `c ∉ Z`, then `gN ∩ N = ∅`, so `g` does not commensurate `N`.
- If `c ∈ Z`, then `g` has index `c`. Index `0` forces `c = 0`. `∎`

**Item 5.**
- `sigma(x) = x XOR 1` preserves `N` and has index `0`.
- `c = o sigma o^-1` maps `x` to `x+1` if `x` is odd and to `x-1` if `x` is even. It maps `N \ {0}` onto itself, so it has index `0`.
- `o c o^-1 (x) = c(x-1) + 1 = sigma(x)`.
- On `N` the two act as `(0 1)(2 3)…` and `(1 2)(3 4)…` up to finitely many points. These are genuine permutations, so the near action of `D_∞` lifts. `∎`

**Item 6.**
- If all level-`L` sections of `g` lie in `<o>`, say `g|_u = o^(k_u)`, then `g(u + 2^L y) = g(u) + 2^L (y + k_u)` for `u < 2^L`. So `g|_N` is eventually `2^L`-periodic.
- Sections of `o^k` at every level are again powers of `o`, and sections of products are products of sections. So the property passes from the generators, at the maximum of their levels, to all of `G`.
- By item 2, `G` embeds into the virtually abelian group of eventually `2^L`-periodic index-zero near permutations (item 1 of `window-zero-twists-are-fixed-point-free`). `∎`
