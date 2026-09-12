---
rg: 2
id: bounded-blockwise-inner-realizers-fail-off-kernel
kind: claim
title: Off the kernel, no sofic approximation realizes an element blockwise by boundedly many kernel elements times block centralizers
distinct_from:
  kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient: that shows the ambient group preserves the kernel's expander blocks when the quotient is sofic-invisible; this shows that on blocks an element outside the kernel is not a kernel element from a finite set times an exact block centralizer, on any non-negligible mass, whenever the kernel has trivial centralizer.
  realized-relative-twists-embed-in-outer-twist-group: that embeds realized relative twists of a rigid pair in a fixed outer twist group; this is the absolute statement for the normal kernel itself, and forces blockwise inner realizers of elements outside the kernel to leave every finite set.
  leavitt-cover-finite-quotients-split-over-the-kernel: that gives genuine inner realizers in every finite quotient of the Leavitt cover; this shows that in sofic approximations such realizers cannot stay in a finite set, so that splitting does not transfer with bounded realizers.
---

**ESTABLISHED.** Let `1 -> N -> G -> Q -> 1` be exact with `G` countable,
`N` Kazhdan with finite symmetric generating set `S`, and `C_G(N) = 1`. Let
`sigma_n : G -> Sym(X_n)` be a sofic approximation along `U`, and fix a
uniform-Cheeger edit of the `S`-graphs of `sigma_n|N` into blocks `B`
(`kun-expander-decomposition-formalized`), with edited block permutations
`s_B` for `s in S`.

For `g in G \ N`, a finite set `F ⊂ N` and `0 <= eps < 1/2`, call a block `B`
**(F, eps)-realized** if there are `n in F` and an exact permutation `c` of
`B` with `c s_B = s_B c` for all `s in S` such that `sigma_n(g)` and
`sigma_n(n) c` agree on at least `(1 - eps)|B|` points of `B`. Then

```text
sum of |B| over the (F, eps)-realized blocks   =   o(|X_n|)   along U.
```

So an element outside `N` is not, on non-negligible mass, a kernel element
from a fixed finite set times an exact block centralizer. Blockwise
inner-times-centralizer realizers of `g`, where they exist, must leave every
finite subset of `N` along `U`.

Derivation: `bounded-blockwise-realizers-proof`.

**Instance.** The Leavitt cover `hyperbolic-kazhdan-cover-of-leavitt-unit-group`
has `C_G(N) = 1` (`leavitt-cover-finite-quotients-split-over-the-kernel`).
By `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient` every
element preserves most blocks in every sofic approximation. So each
`g not in N` acts on invariant blocks by twists whose inner realizers diverge.
The genuine inner realizers of the finite quotients `G/L = N/L x K_L` do not
transfer to sofic approximations with bounded size.

**Scope.**
- Elementary: it uses trace zero and `C_G(N) = 1` only, plus the block
  partition. It proves nothing about soficity of the cover.
- It closes one repair of the hinge recorded on
  `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`: a blockwise
  conjugacy correction by a *bounded* kernel-valued cocycle is impossible. The
  unbounded case stays open.
