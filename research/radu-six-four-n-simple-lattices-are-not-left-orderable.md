---
rg: 2
id: radu-six-four-n-simple-lattices-are-not-left-orderable
kind: claim
title: For every n >= 2 the simple subgroup of Radu's torsion-free (6,4n)-group is its index-4 parity kernel and is not left-orderable, an infinite family of simple non-left-orderable lattices of type F
distinct_from:
  radu-simple-six-six-lattices-are-not-left-orderable: that kills Radu's 160 (6,6)-lattices using Radu's own GAP computation of the quotient by the simple subgroup; this computes that quotient (not recorded by Radu) uniformly for his infinite (6,4n) family through one n-independent window presentation, validates the square datum against his printed local actions and corrects a misprint in them
  irreducible-tree-product-lattices-are-not-left-orderable: that is an OPEN class-wide statement; this settles one explicit infinite family, pairwise non-quasi-isometric, not the class
artifacts:
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/README.md
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/fig64n.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/g64n.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/xcheck64n.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/bmw.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mktc.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mkperf.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mkelim.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mkwin.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/verwin.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/relators-64n.txt
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/run.log
---

**ESTABLISHED (computer-certified by coset enumeration and Reidemeister–Schreier in GAP; imports
Radu's virtual-simplicity theorem and the Γ_{4,4}' certificate).** Proof:
`radu-six-four-n-simple-lattices-are-not-left-orderable-proof`.

**Setting.** N. Radu, *New simple lattices in products of trees and their projections*
(arXiv:1712.01091), Theorem `maintheorem:64n`.
- For each n ≥ 2 there is a torsion-free `(6,4n)`-group `Γ_{6,4n}`. Its letters are `a_1,a_2,a_3`
  and `b_1,…,b_{2n}`, and it has `6n` geometric squares (Figure `picture:64n`).
- `Γ_{6,4n}` contains `Γ_{4,4}` and is virtually simple.
- Radu does not record the index of the simple subgroup `Γ_{6,4n}^{(∞)}`.

**Theorem.** For every n ≥ 2:
1. `Γ_{6,4n}/⟨⟨[a_1^3,a_2^4],[a_2^3,a_1^4]⟩⟩ ≅ (C_2)^2`. Hence
   `Γ_{6,4n}^{(∞)} = Γ_{6,4n}' = Γ_{6,4n}^+`, the type-preserving subgroup of index 4.
2. `Γ_{6,4n}^{(∞)}` is not left-orderable.
3. `Γ_{6,4n}^{(∞)}` is a simple, torsion-free, finitely presented group of type F. It is `π_1` of a
   finite nonpositively curved square complex with 4 vertices and `24n` squares, whose universal
   cover is `T_6 × T_{4n}`.

**How n is removed.** The *window group* `W(5,2)` has generators `a_1,a_2,a_3,b_3` and 14 relators.
- The relators are the squares of `Γ_{6,4n}` around `b_1,…,b_5` and around `b_{2n},b_{2n-1},b_{2n-2}`,
  with every other letter eliminated.
- Its relators are squares of `Γ_{6,4n}` for every n ≥ 3. So `W(5,2)` maps onto every `Γ_{6,4n}`,
  n ≥ 3.
- In `W(5,2)/⟨⟨c,d⟩⟩`, coset enumeration closes with `[⟨a_1⟩] = 2` (26 s).
- Reidemeister–Schreier shows that the index-4 kernel of `W(5,2)/⟨⟨c⟩⟩` is perfect.

Both properties pass to all quotients, which forces the collapse for every n ≥ 3. The case n = 2 is a
direct computation.

**Independent per-n confirmation.** For each n = 2,…,24 separately, the 4-generator Tietze reduction
of the full `6n`-square presentation gives:
- `Γ^{ab} = (C_2)^2`;
- `[Γ/⟨⟨c,d⟩⟩ : ⟨a_1⟩] = 2`;
- a perfect index-4 kernel of `Γ/⟨⟨c⟩⟩`.

For n = 2, `Γ_{6,8}/⟨⟨[a_1^3,a_2^4]⟩⟩` has order 4, by enumeration over the trivial subgroup.

**Consequence for Zaremsky Problem 1.22.**
- Part 2 kills an *infinite* family of explicit simple lattices of type F: `Γ_{6,4n}^{(∞)}` for
  n ≥ 2.
- They are pairwise non-quasi-isometric, and none is quasi-isometric to the 160 `(6,6)`-lattices of
  `radu-simple-six-six-lattices-are-not-left-orderable`. The degrees of a product of two trees
  (each ≥ 3) are quasi-isometry invariants, and here they are `{6,4n}`.

**Also found.**
- *A misprint in Radu's proof of Theorem 64n.* The printed local permutation of `b_3` is
  `(a_1 a_3 a_1^{-1})(a_2 a_2^{-1} a_3^{-1})`. The figure's squares induce `(a_1 a_3 a_1^{-1})`.
  - With the printed permutation, no reading convention gives a valid VH datum (`g64n.py n`, 0
    conventions).
  - With the corrected one, the printed permutations reconstruct exactly the figure's datum, for
    n = 2,…,8 (`g64n.py n corrected`, `xcheck64n.py n corrected`).
  - The correction does not change the local action group of the b-letters (it is still `Sym(6)`),
    so Radu's theorem stands.
- *Negative results.* The enumeration of `⟨a_1⟩` does not close in the smaller n-free groups.
  - These are D = `W(4,1)` on 7 letters (12M cosets), and `W(3,1)` and `W(4,0)` (10^5 cosets).
  - The full `6n`-letter presentation exceeds 2 GB for n ≥ 6.
  - The window needs the second square of each chain on both sides.

**What it does not settle.**
- **Problem 1.22 for other lattice families.** The route needs three ingredients:
  - a copy of `Γ_{4,4}`, or another certified non-left-orderable seed;
  - an abelian quotient by the finite residual;
  - Radu-type simplicity.
  Lattices without a copy of `Γ_{4,4}`, such as Rattaggi's or Janzen–Wise's, need their own seed.
- **The class-wide statement** `irreducible-tree-product-lattices-are-not-left-orderable` stays
  OPEN.
