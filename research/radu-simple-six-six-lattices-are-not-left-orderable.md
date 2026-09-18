---
rg: 2
id: radu-simple-six-six-lattices-are-not-left-orderable
kind: claim
title: The commutator subgroup of Radu's non-residually-finite (4,4)-group is not left-orderable, so none of Radu's 160 simple (6,6)-lattices is left-orderable
distinct_from:
  irreducible-tree-product-lattices-are-not-left-orderable: that is an OPEN class-wide statement; this proves non-left-orderability for one explicit index-12 subgroup and transfers it to every group containing it with abelian quotient, which covers 160 explicit simple lattices unconditionally
  promislow-group-is-not-left-orderable: that is a hand argument in a virtually abelian group; this is a verified 124-triple certificate in a non-residually-finite irreducible lattice in a product of trees
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports Deroin–Hurtado for algebraic p-adic lattices; every group here contains the non-residually-finite, hence non-linear, group Gamma_{4,4}
artifacts:
  - experiments/lo-certificate-radu-lattices-2026-09-17/README.md
  - experiments/lo-certificate-radu-lattices-2026-09-17/bmw.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/lo_sat.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/lo_search.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/ab_search.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/verify_certificate.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/derived_check.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/certificate-gamma44-derived-L6.txt
  - experiments/lo-certificate-radu-lattices-2026-09-17/certificate-gamma44-kernel-L6.txt
  - experiments/lo-certificate-radu-lattices-2026-09-17/certificate-gamma662-kernel-L4.txt
  - experiments/lo-certificate-radu-lattices-2026-09-17/run.log
---

**ESTABLISHED (computer-certified, with Radu's published GAP computation as the only imported
input).** Proof: `radu-simple-six-six-lattices-are-not-left-orderable-proof`.

**Setting.** N. Radu, *New simple lattices in products of trees and their projections*
(arXiv:1712.01091), §6.1. `Γ_{4,4}` is the torsion-free `(4,4)`-group with letters
`a_1, a_2, b_1, b_2` and the four geometric squares
`a_1b_1a_2^{-1}b_1`, `a_1b_2a_2b_2^{-1}`, `a_1b_2^{-1}a_2^{-1}b_1^{-1}` and `a_1b_1^{-1}a_2^{-1}b_2`.
It is irreducible and not residually finite (Radu, Proposition `nonrf`; Bondarenko–Kivva;
Caprace–Wesolek). Its abelianization has order 12, and the commutator subgroup
`Γ_{4,4}' = [Γ_{4,4}, Γ_{4,4}]` lies in the parity kernel `Γ_{4,4}^+`.

**Theorem.**
1. `Γ_{4,4}'` is not left-orderable. The certificate has 124 product relations on 69
   inverse-pairs of elements of Bridson–Wise length at most 6.
2. **Transfer.** Let `Γ` be any `(d_1,d_2)`-group whose geometric squares contain the four above,
   and let `S ≤ Γ` be a subgroup that contains a normal subgroup `N ⊴ Γ` with `Γ/N` abelian.
   Then `S` is not left-orderable.
3. **Kill.** For each `k ∈ {1,…,160}`, the simple subgroup `Γ_{6,6,k}^{(∞)}` of Radu's
   `(6,6)`-group `Γ_{6,6,k}` (Radu, Theorem `maintheorem:simple66-45`(i), Tables 6–10) is not
   left-orderable. Each is simple, torsion-free, finitely presented and of type F. Radu shows
   they are pairwise non-isomorphic, so these are 160 distinct candidates killed for Zaremsky
   Problem 1.22 and for `some-simple-lattice-in-a-product-of-trees-is-left-orderable`.

Why part 3 follows. Radu computes `Γ_{6,6,k}/Γ_{6,6,k}^{(∞)} ≅ (C_2)^2` for 158 values of `k`,
and `≅ (C_2)^2 × C_3` for `k ∈ {104, 116}`. Both quotients are abelian, so part 2 applies with
`S = N = Γ_{6,6,k}^{(∞)}`. `S ≤ Γ^+` acts freely and cocompactly on `T_6 × T_6` (Radu's lemma in
§3: type-preserving simply-transitive groups are torsion-free). So `S` is `π_1` of a finite
nonpositively curved square complex, which gives type F.

**Also certified.**
- `Γ_{4,4}^+` is not left-orderable: 70 triples on the radius-6 parity ball. At radius 4
  the ball is SAT.
- `Γ_{6,6,2}^+` is not left-orderable directly: 169 triples at radius 4. This is the explicit
  6-generator, 10-relator group of Radu's Corollary C(i).
- Every `(d_1,d_2)`-group containing `Γ_{4,4}` has non-left-orderable `Γ^+`. This includes
  Radu's torsion-free `(6,8)`- and `(8,6)`-groups and the infinite family `Γ_{6,4n}` (n ≥ 2).

**What it does not settle.**
- For `Γ_{6,4n}` and the `(6,8)`/`(8,6)` groups, the simple subgroup `Γ^{(∞)}` is killed
  whenever `Γ/Γ^{(∞)}` is abelian. Radu does not record that quotient for them.
- A universal kill of every group containing `Γ_{4,4}` would need `Γ_{4,4}^{(∞)}` itself to be
  non-left-orderable. The naive search in the normal closure of `[a_1^3,a_2^4]` and
  `[a_2^3,a_1^4]` finds no certificate: conjugators of radius 2, products of two conjugates,
  19492 elements, SAT (`ncl_search.py`, `run.log`).
- It says nothing about lattices that do not contain `Γ_{4,4}`, such as Burger–Mozes's original
  groups.

**Mechanism.** Radu builds his simple lattices by enlarging `Γ_{4,4}`, because its failure of
residual finiteness forces virtual simplicity through the normal subgroup theorem. That same
seed carries a finite positive-cone contradiction in an index-12 subgroup. Every construction
in this pattern (non-RF seed, abelian top) inherits non-left-orderability of its simple core.
