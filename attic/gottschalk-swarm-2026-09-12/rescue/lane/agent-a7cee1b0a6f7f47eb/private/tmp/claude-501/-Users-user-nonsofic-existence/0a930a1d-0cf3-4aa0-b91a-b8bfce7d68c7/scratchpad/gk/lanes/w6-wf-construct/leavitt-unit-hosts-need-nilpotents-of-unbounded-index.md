---
rg: 2
id: leavitt-unit-hosts-need-nilpotents-of-unbounded-index
kind: claim
title: Characteristic-p hosts of Leavitt unit groups must contain nilpotents of unbounded index
distinct_from:
  binary-complement-corner-has-no-weakly-finite-image: that says no weakly finite host exists at all; this rules out every host, weakly finite or not, whose nilpotent elements have bounded index, and says nothing about hosts with nilpotents of unbounded index.
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**ESTABLISHED** on paper. Verification is requested from w4-vf-linear-b.

Let `p` be prime, `G = L_(F_p)(1,2)^x`, and `W` a nonzero ring with `p·1 = 0` whose nilpotent elements all
satisfy `x^N = 0` for one fixed `N`.
1. For `p = 2`, every homomorphism `G -> W^x` is trivial.
2. For `p = 3`, no homomorphism `G_3 -> W^x` sends the central element `z = -1` to `-1`. This part assumes every
   normal subgroup of `G_3` lies in `{±1}` or equals `G_3`.

**Sharper form.** Let `ρ : G -> W^x` be nontrivial into any characteristic-`p` ring, or for `p = 3` have
`ρ(z) = -1`. Then for every `k` and every `p^k`-cycle `x ∈ V ≤ G`, the element `ρ(x) - 1` is nilpotent of index
greater than `p^(k-1)`.

**Why.** `V` contains `S_n` for every `n`, through permutations of complete prefix codes. In characteristic `p`,
`x^(p^k) = 1` gives `(ρ(x) - 1)^(p^k) = 0`. A bound `N` on nilpotent index then kills `x^(p^j)` once `p^j >= N`,
which is a nonidentity element. Simplicity finishes the argument.

**Consequences (dead hosts).** None of these receives a nontrivial `ρ`, and for `p = 3` none receives one with
`z ↦ -1`:
- division rings;
- matrix rings `M_n(D)` over division rings, and their subrings with bounded matrix sizes;
- prime or semiprime Goldie rings (Goldie's theorem, statement level);
- reduced rings;
- finite-dimensional algebras;
- algebraic ultraproducts of matrix algebras of bounded size.

A weakly finite host, if one exists, must contain nilpotents of unbounded index. Rank ultraproducts of matrix
algebras of growing size have them.
