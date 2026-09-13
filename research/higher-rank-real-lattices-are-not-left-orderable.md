---
rg: 2
id: higher-rank-real-lattices-are-not-left-orderable
kind: claim
title: Irreducible lattices in real semisimple Lie groups of real rank at least two with finite center are not left-orderable
---

**ESTABLISHED (literature import).**  Let `G` be a connected real semisimple
Lie group with finite center and real rank at least two, and let `Gamma` be an
irreducible lattice in `G`.  Then `Gamma` is not left-orderable, and every
homomorphism `Gamma -> Homeo_+(R)` is trivial.

Source: Deroin--Hurtado, *Non left-orderability of lattices in higher rank
semi-simple Lie groups*, arXiv:2008.10687v1, Theorem 1.3, quoted in
`higher-rank-real-lattices-are-not-left-orderable-citation`.

**Special case used downstream.**  For `n >= 3`, no finite-index subgroup of
`SL_n(Z)` is left-orderable.
- `SL_n(R)` is connected, has finite center, and has real rank `n - 1 >= 2`.
- `SL_n(Z)` is a lattice in it (Borel--Harish-Chandra), and it is irreducible because `SL_n(R)` is simple.
- A finite-index subgroup of a lattice is a lattice.

For finite-index subgroups of `SL_n(Z)` this is the earlier theorem of Witte
Morris, as quoted in Navas, arXiv:1712.06462v2, p. 3.

**Scope.**  The theorem covers lattices in real Lie groups of real rank at least two.
- Lattices in `p`-adic groups are not covered, for example torsion-free `A~_2` groups.
- Rank-one lattices are not covered.
- On p. 2, Deroin--Hurtado write that for `Sp(n,1)` and `F_4^(-20)` "no examples are known". They tie this to "a well known question in the theory of left-orderable groups asking whether there exists a left-orderable group with Kazhdan's Property (T)", which is `infinite-left-orderable-kazhdan-group`.

Consumer: `finite-index-subgroups-of-el-n-are-not-left-orderable`.
