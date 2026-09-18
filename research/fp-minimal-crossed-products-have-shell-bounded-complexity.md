---
rg: 2
id: fp-minimal-crossed-products-have-shell-bounded-complexity
kind: claim
title: A finitely presented crossed product of an infinite minimal subshift has pattern counts bounded by shell size, so it has zero entropy over amenable groups, is impossible over virtually cyclic groups, and has log-complexity at most C N^(d-1) over Z^d
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that is Z^2 and all SFTs; this is every amenable acting group, for minimal subshifts, with a quantitative bound by the shell rather than only zero entropy.
  minimal-subshift-crossed-product-is-not-finitely-presented: that is P = Z through LEF; this covers every virtually cyclic P, including torsion, through bounded shells, with no LEF argument.
  fp-minimal-crossed-products-have-no-homoclinic-pairs: that is the qualitative shell determination; this is its counting consequences.
  fp-crossed-products-force-connected-differences: parts 2 and 3 of that node, landed concurrently on another lane, give the same counting consequences from the same wall argument, with the bound written over the inner boundary layer ∂F rather than the outer shell N_r(F) \ F; the two are equivalent up to the choice of layer, and the zero-entropy and virtually-cyclic corollaries coincide.
artifacts:
  - research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md
---

**ESTABLISHED (unreviewed).** Let `P` be finitely generated, `X ⊆ A^P` an infinite minimal subshift and
`k` a field. Suppose `LC(X,k) ⋊ P` is finitely presented, and `X` has SFT radius `r`. Then:
1. **Shell bound.** `|L_F(X)| <= |A|^(|N_r(F) \ F|)` for every finite `F ⊆ P`.
2. **Amenable `P`.** `h_top(X) = 0`.
3. **Virtually cyclic `P`.** This never happens: `LC(X,k) ⋊ P` is not finitely presented for any infinite
   minimal `X`.
4. **`P = Z^d`.** `log|L_(B_N)(X)| <= C N^(d-1)`.

**Why it matters.** For `decidable-group-algebras-have-fp-cantor-crossed-hosts` over `Z^2`, a host's ball
complexity is at most exponential in the perimeter `N`. Growth counting for hosting `F_2` gives the
matching lower bound `e^(cN)`, so the complexity is pinned to `Θ(N)`. That is sharper than `e^(o(N^2))`:
hard languages must live in which one-dimensional boundary data occur, not in bulk. Over every amenable
acting group, positive-entropy minimal hosts die with no measure-theoretic input.

DERIVATION
fp-minimal-crossed-products-have-shell-bounded-complexity-proof
