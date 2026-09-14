---
rg: 2
id: two-level-kl-violations-need-torsion-in-an-extreme-block
kind: claim
title: A two-level Kervaire--Laudenbach violation over a torsion-free subgroup of finite cyclic index needs a finite-order level-changing coefficient in the middle of an inverse-palindromic extreme block
distinct_from:
  kl-two-level-words-over-torsion-free-by-cyclic: that is the open injectivity statement for all two-level words; this locates where any counterexample to it must carry torsion, and proves injectivity for every two-level word whose finite-order coefficients miss that position.
  kl-pivot-letter-words-inject-over-torsion-free-by-finite: that settles words with one base-level letter by Tietze elimination and allows torsion anywhere; this allows any number of letters at both levels and constrains only where the torsion sits.
  kl-holds-when-extreme-height-blocks-have-infinite-order: that is the general theorem over every group; this is its specialization to coefficient groups with a torsion-free normal subgroup of finite cyclic index, where it becomes a statement about coset levels.
artifacts:
  - research/artifacts/hl-kl-two-level-words-2026-09-14.md
---

Setting of `kl-two-level-words-over-torsion-free-by-cyclic`:
- `P` is a group and `H <= P` is torsion-free.
- `a in P` normalizes `H`, and `n >= 2` is minimal with `a^n in H`.
- `w = W(t, a t a^(-1))` with `W in H * F(u, v)` and `deg W = ±1`.

Normalize to degree `1` by inverting if needed. Take a cyclically reduced
normal form of `w` over `P`, its canonical cut, and its constrained blocks as in
`kl-holds-when-extreme-height-blocks-have-infinite-order`.

1. **Screen.** Suppose `P -> (P * <t>)/<<w>>` is not injective. Then some
   constrained block of the canonical cut is an odd inverse palindrome whose
   middle coefficient has finite order. That coefficient lies outside `H`, in a
   coset `a^j H` with `j != 0 mod n`, so it changes coset level between the two
   letters it separates. For `n = 2`, finite-order elements of `aH` are
   involutions, since `(ha)^2 in H` is torsion-free.
2. **Injectivity.** Suppose no constrained block is an odd inverse palindrome
   around a coefficient of finite order. Then `P` embeds, and so does every
   `G >= P`. In particular this holds when every coefficient at the two extreme
   indices lies in `H`, or has infinite order, and each constrained block with
   at least two marks has mutually non-inverse end coefficients.
3. **The level-one coefficients.** A coefficient between two letters at the same
   level lies in `H` and is either trivial (then absent from the normal form) or
   of infinite order. So torsion is possible only at level changes. Inside a
   constrained block, level-changing finite-order coefficients are harmless except
   at the middle of an inverse palindrome.

**What stays open.** Two-level words in which, at the canonical cut, a
constrained block is an odd inverse palindrome around a finite-order
level-changing coefficient. The simplest are words with a single finite-order
level-changing coefficient at the global maximum or minimum of the height walk.
This covers every `n`, not only `n = 2`. The repeated-base-letter case of the
open claim is settled whenever its torsion avoids those positions.

**ESTABLISHED** through `two-level-kl-extreme-block-screen-proof`. Elementary
given the general theorem. Not independently reviewed; no novelty claimed.
