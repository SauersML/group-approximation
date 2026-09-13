---
rg: 2
id: higher-rank-p-adic-lattices-are-not-left-orderable
kind: claim
title: Irreducible lattices in p-adic semisimple groups of rank at least two have no nontrivial action on the line
distinct_from:
  higher-rank-real-lattices-are-not-left-orderable: that imports the real case (real rank at least two, finite center); this imports the p-adic case, which covers lattices acting on products of Bruhat–Tits trees such as irreducible lattices in SL(2,Q_p) x SL(2,Q_p)
---

**ESTABLISHED (literature import).** Let `G` be a `p`-adic semisimple Lie group with
`rank_{Q_p} G ≥ 2`, and let `Γ` be an irreducible lattice in `G`. Then every homomorphism
`Γ → Homeo_+(R)` is trivial. In particular no such `Γ` is left-orderable, and neither is
any finite-index subgroup of `Γ` (which is again an irreducible lattice).

Source: D. Witte Morris, *Non-left-orderability of lattices in higher-rank semisimple Lie
groups (after Deroin and Hurtado)*, arXiv:2407.09742v1, Theorem 1.11, quoted in
`higher-rank-p-adic-lattices-are-not-left-orderable-citation`. Witte Morris attributes it
to Deroin and Hurtado (arXiv:2008.10687).

**Products of trees.** Witte Morris names `G = SL(2,Q_p) × SL(2,Q_p)` as a model case
(Remark 3.4(2)), and remarks that the same proof applies to finite products of `p`-adic
semisimple groups for various primes (Remark 3.4(4)). `SL(2,Q_p)` acts on the
`(p+1)`-regular Bruhat–Tits tree with compact open vertex stabilizers and without
inversions. So a torsion-free irreducible cocompact lattice in `SL(2,Q_p) × SL(2,Q_p)`
acts freely and cocompactly on a product of two trees and is not left-orderable. These are
arithmetic lattices, so they are residually finite and never simple.

**Trust surface.**

- Note 1.12 of the source: "although Theorem 1.11 is not stated in [13], it follows
  directly from the methods there, so it can be considered to be implicit in the paper and
  should be attributed to Deroin and Hurtado."
- The exposition proves Theorem 1.11 under the simplifying assumption `G = KΓ`
  (Assumption 3.6, p. 8) and only sketches, in its Section 5, the harmonic-function tool
  that removes it.
- The product-over-primes extension is a remark, not a stated theorem.

Consumer: `irreducible-tree-product-lattices-are-not-left-orderable` (calibration case).
