---
rg: 2
id: compression-triples-avoid-proper-cat0-groups
kind: claim
title: No compression triple with an infinite commuting factor lives in a proper CAT(0) polyhedral group whose finitely generated torsion subgroups are finite
distinct_from:
  kazhdan-compression-instances-have-infinite-vcd: that proves the nesting J^n <= Gamma and excludes groups of finite virtual cohomological dimension; this excludes groups of bounded flat rank even with infinite torsion subgroups, which covers lattices with unbounded finite p-subgroups such as Kac--Moody lattices over finite fields.
  openai-expander-matching-criterion: that is the criterion; this shows its hypotheses have no instance with a non-LEF factor in the groups described here.
  hyperlinear-fp-infinite-simple-kazhdan-group: that is the open existence question; this explains why a nonsoficity proof for its geometric candidates cannot be a compression triple inside them.
---

**ESTABLISHED.** Let `G` act properly by cellular isometries on a finite-dimensional CAT(0)
polyhedral complex with finitely many shapes, and assume every finitely generated torsion
subgroup of `G` is finite. Let `Gamma, J <= G` and `t in G` satisfy

```text
t Gamma t^(-1) <= Gamma,   [Gamma, J] = 1,   Gamma ∩ J = 1,   t J t^(-1) <= Gamma,    (CT1)
```

the hypothesis of `openai-expander-matching-criterion` for one compressor. If `J` is finitely
generated, then `J` is finite. So that criterion, whose conclusion is that `J` is LEF, is vacuous
inside `G`.

**Why this is not covered by finite dimension.** `kazhdan-compression-instances-have-infinite-vcd`
excludes groups of finite virtual cohomological dimension. A Kac--Moody group over `F_q` with
infinite Weyl group contains infinite groups of exponent `p` (Remy, arXiv:math/0402300,
Theorem 8, read at source), hence `(Z/p)^n` for every `n`, and has infinite virtual cohomological
dimension. What survives is bounded rank of free abelian subgroups, and that is what this claim
uses.

**Instances.**
- *The `(2,4,6)` Kac--Moody lattices* `Lambda_q/Z`
  (`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`). They act properly and cellularly on
  the product of their two 2-dimensional buildings, which has finitely many shapes. The torsion
  hypothesis is **not verified here**. It would follow from a fixed-point theorem for finitely
  generated torsion groups acting on 2-dimensional CAT(0) complexes, applied to each factor,
  because the stabilizer of a pair of points is finite. Norin--Osajda--Przytycki announce such a
  theorem ("Torsion groups do not act on 2-dimensional CAT(0) complexes"). This lane did not read
  it, so the instance is conditional on its hypotheses covering Davis realizations.
- *Torsion-free cases* (Titz Mite--Witzel kernels, lattices in products of trees) are already
  covered by `kazhdan-compression-instances-have-infinite-vcd`.

**What it says for the roots.** A nonsoficity proof for the Kac--Moody candidates of
`hyperlinear-fp-infinite-simple-kazhdan-group` needs a mechanism other than a compression triple
inside the group, once the torsion hypothesis is checked.

**Model test.** The binary Leavitt unit group is an instance of the criterion. It contains `V`,
hence `Z^n` for every `n`, so it acts properly on no finite-dimensional CAT(0) complex and the
claim says nothing about it. `SL_3(Z) x BS(2,3)`, the calibration in
`openai-expander-matching-criterion`, has no compressor.

**Credit.** Bridson's semisimplicity of cellular isometries (Proc. Amer. Math. Soc. 127, 1999)
and the Flat Torus Theorem (Bridson--Haefliger II.7.1), applied to the nesting of the vcd node.
No novelty is claimed.

Proof: `compression-triples-avoid-proper-cat0-groups-proof`.
