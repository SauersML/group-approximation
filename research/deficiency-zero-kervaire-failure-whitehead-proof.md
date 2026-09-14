---
rg: 2
id: deficiency-zero-kervaire-failure-whitehead-proof
kind: route
title: Count cells to force balance and unimodularity, get contractibility from Hurewicz and Whitehead, and let Klyachko forbid an aspherical coefficient complex
target: deficiency-zero-kervaire-failure-yields-whitehead-counterexample
requires:
  - klyachko-kl-holds-for-torsion-free
  - kervaire-laudenbach-holds-for-hyperlinear
  - kervaire-laudenbach-holds-for-mf
artifacts:
  - research/artifacts/ideas-bridges-2026-09-13.md
---

**Standard inputs used without a node** (textbook algebraic topology and group
cohomology):
- cellular homology of CW complexes;
- the Hurewicz theorem;
- Whitehead's theorem that a CW complex with all homotopy groups trivial is
  contractible;
- a group with a finite-dimensional `K(G,1)` is torsion-free. Cohomological
  dimension passes to subgroups, and a nontrivial finite cyclic group has
  nonzero integral cohomology in infinitely many degrees.

Notation: `X = {x_1, ..., x_n}`, `R = {r_1, ..., r_m}`, `G_w = (G * <t>)/<<w>>`.

**Step 0: presentations.** The group of `<X, t | R, W>` is
`(F(X) * <t>)/<<R, W>> = (G * <t>)/<<w>> = G_w`.
- Its presentation complex `L` has one 0-cell, `n+1` 1-cells and `m+1` 2-cells.
- `K` is the subcomplex obtained by omitting the 1-cell `t` and the 2-cell `W`.
- `K` is connected, since it has a single 0-cell.

**Step 1: item 1.** `H_1(G_w) = H_1(L; Z)` is `Z^{n+1}` modulo the span of the
`m+1` exponent-sum vectors of `R` and `W`. So its rank is at least
`(n+1) - (m+1) = n - m`. If `m < n`, the rank is positive and `G_w` is
infinite.

**Step 2: unimodularity for any `G`.** `deg_t` is well defined on `G * <t>`
through the retraction killing `G`. The composite
`H_1(G) (+) Z -> Z -> Z/deg_t(w)`, projection to the second coordinate then
reduction, is surjective. It kills the image `(ab(w), deg_t(w))` of `w`, so it
factors through `H_1(G_w)`. If `G_w = 1`, then `Z/deg_t(w) = 0`, so
`deg_t(w) = +-1`. This uses no hypothesis on `G`.

**Step 3: item 2(a).** If `G_w = 1`, then `H_1(G_w) = 0`. Step 1 gives
`m >= n`, so `m = n`; Step 2 gives `deg_t(w) = +-1`.

**Step 4: item 2(b).**
- `L` is a finite connected 2-complex with `pi_1(L) = G_w = 1`, so
  `H_1(L) = 0`.
- Its Euler characteristic is `1 - (n+1) + (n+1) = 1`.
- `H_2(L) = ker(d_2)` is a subgroup of `Z^{n+1}`, hence free abelian.
- `chi(L) = rank H_0 - rank H_1 + rank H_2 = 1 + rank H_2(L)`, so
  `H_2(L) = 0`.
- `L` is simply connected with vanishing reduced homology. By the Hurewicz
  theorem every `pi_k(L)` vanishes, and by Whitehead's theorem `L` is
  contractible.

**Step 5: item 2(c).**
- Suppose `K` were aspherical. Then `K` is a finite 2-dimensional `K(G,1)`, so
  `G` is torsion-free.
- `deg_t(w) = +-1` by Step 3, so `klyachko-kl-holds-for-torsion-free` makes
  `G -> G_w` injective. But `G_w = 1` and `G != 1`, a contradiction.
- The same contradiction shows `G` is not torsion-free.
- So `K` is not aspherical. Its universal cover `K~` is a simply connected
  2-complex that is not contractible. By the argument of Step 4 (Hurewicz plus
  Whitehead), `H_2(K~) != 0`, and `pi_2(K) = pi_2(K~) = H_2(K~)` by Hurewicz.
- Hence `pi_2(K) != 0`, and `Y = L`, `K` witness
  `nonaspherical-subcomplex-of-contractible-2-complex-exists`.

**Step 6: item 2(d).** By `kervaire-laudenbach-holds-for-hyperlinear` and
`kervaire-laudenbach-holds-for-mf`, a hyperlinear or MF coefficient group injects
into `G_w` whenever `deg_t(w) != 0`. Here `G != 1`, `G_w = 1` and
`deg_t(w) = +-1`, which excludes both.

**Step 7: item 3.**
- The inclusion `G * <t> -> H * <t>` fixes `w` and induces `G_w -> H_w`,
  compatible with `G -> H -> H_w`.
- `G_w = 1`, so `G -> H_w` is trivial. The kernel of `H -> H_w` contains `G`,
  hence `<<G>> = H`.
- So `H_w` is the quotient of `<t>` by the image of `w`, which is
  `t^{deg_t(w)}`. Step 2 gives `deg_t(w) = +-1`, so `H_w = 1`.
- `H != 1` because it contains `G`. Item 2 therefore applies to `H`.
