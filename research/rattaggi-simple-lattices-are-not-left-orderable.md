---
rg: 2
id: rattaggi-simple-lattices-are-not-left-orderable
kind: claim
title: Rattaggi's explicit torsion-free simple lattices in products of trees are not left-orderable, by finite sign-choice certificates
distinct_from:
  irreducible-tree-product-lattices-are-not-left-orderable: that is an OPEN class-wide statement for all lattices with boundary-2-transitive dense projections; this proves non-left-orderability for two explicit simple lattices, unconditionally, by a verified finite certificate
  promislow-group-is-not-left-orderable: that is a four-term hand argument in a virtually abelian group; this concerns simple lattices in products of trees and uses certificates of 301 and 207 product relations
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports Deroin–Hurtado for algebraic p-adic lattices; the groups here are non-residually-finite, hence non-linear, tree-product lattices
artifacts:
  - experiments/lo-certificate-tree-lattices-2026-09-17/bmw.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/test_bmw.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/lo_sat.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/lo_search.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/calib_promislow.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/verify_certificate.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/certificate-incoherent-kernel-L4.txt
  - experiments/lo-certificate-tree-lattices-2026-09-17/certificate-sigma-kernel-L4.txt
  - experiments/lo-certificate-tree-lattices-2026-09-17/run-L4-kernel.log
  - experiments/lo-certificate-tree-lattices-2026-09-17/certificate-a6-kernel-L6.txt
  - experiments/lo-certificate-tree-lattices-2026-09-17/run-a6-L6-kernel.log
  - experiments/lo-certificate-tree-lattices-2026-09-17/README.md
---

**ESTABLISHED (computer-certified).** Proof: `rattaggi-simple-lattices-are-not-left-orderable-proof`.

For a one-vertex complete VH square complex with a-generators `a_1..a_m`, b-generators `b_1..b_n`
and fundamental group `Γ`, let `Γ_0 = ker(Γ → Z/2 × Z/2)`, where `a_i ↦ (1,0)` and `b_j ↦ (0,1)`.
Neither of the following groups admits a left-invariant total order.

1. **Rattaggi's incoherent simple group** `Λ = Γ_0` (D. Rattaggi, *An incoherent simple group*,
   arXiv:math/0507363, Theorem 1). Here `Γ < Aut(T_12) × Aut(T_10)` is the `(12,10)`-group with
   30 geometric squares, as listed in `bmw.py` (`RATTAGGI_INCOHERENT`).
2. **Rattaggi's torsion-free simple group** `Σ_0` (D. Rattaggi, *A finitely presented torsion-free
   simple group*, arXiv:math/0411546, Theorem ThSimple). Here `Σ < Aut(T_12) × Aut(T_8)` is the
   `(12,8)`-group with 24 squares, containing Wise's non-residually-finite group `D`
   (`RATTAGGI_SIGMA`).

Both groups are simple, torsion-free, finitely presented and of type F: each is `π_1` of a finite
nonpositively curved square complex, a 4-fold cover of the one-vertex complex. So both are
*specific candidates killed* for Zaremsky Problem 1.22, and for
`some-simple-lattice-in-a-product-of-trees-is-left-orderable`. They are unconditional instances
of the conclusion of `irreducible-tree-product-lattices-are-not-left-orderable`.

**Also certified.** Rattaggi's A6 `(6,6)`-group has index-4 kernel `Λ_0`
(`RATTAGGI_A6`, loc. cit. math/0411546). It is an irreducible torsion-free cocompact lattice in
`Aut(T_6) × Aut(T_6)` satisfying the normal subgroup theorem, and it is conjectured simple there.
It is not left-orderable: a certificate of 412 triples on the radius-6 parity ball. If `Λ_0` is
simple, it too is killed.

**What it rules out, precisely.** It rules out these groups, together with every group that
contains one of them, including `Γ` and `Σ`. It does not rule out other simple tree-product
lattices. At radius 4 the parity balls give no certificate for A6 (one first appears at
radius 6) or for Wise's `D_0` (`run-L4-kernel.log`).

**Certificate form.** A finite list of triples `(p, q, r)` of nontrivial words in `Γ_0` with
`p q = r` in `Γ`, such that no function `P` from those elements to `{0,1}` satisfies both
- `P(g^-1) = 1 - P(g)`, and
- `P(p) ∧ P(q) ⇒ P(r)` for every triple.

Sizes:
- A6 kernel: 412 triples on 300 inverse-pairs, radius 6;
- Λ: 301 triples on 199 inverse-pairs of elements;
- Σ_0: 207 triples on 123 inverse-pairs.
Elements have Bridson–Wise length at most 4 (Λ, Σ_0) or 6 (A6).
