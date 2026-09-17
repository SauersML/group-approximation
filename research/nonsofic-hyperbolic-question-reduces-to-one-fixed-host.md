---
rg: 2
id: nonsofic-hyperbolic-question-reduces-to-one-fixed-host
kind: claim
title: A nonsofic hyperbolic group exists iff a nonsofic local limit of hyperbolic groups exists iff one fixed Kazhdan hyperbolic group has a nonsofic finite-quotient-free hyperbolic quotient
distinct_from:
  hyperbolic-rf-question-reduces-to-one-fixed-host: that fixes the host for residual finiteness, where the counterexample is itself finite-quotient-free; this fixes the host for soficity and hyperlinearity, where the bad subgroup must be pushed into the quotient injectively on a ball and the defect carried by closedness, and adds the equivalence with local limits
  nonsofic-free-burnside-gives-nonsofic-hyperbolic-group: that is the one implication from free Burnside groups; this is the equivalence for every group locally embeddable into hyperbolic groups, with the free Burnside groups as one instance, and it adds the fixed-host direction
  local-approximation-properties-are-marked-closed: that is the closedness theorem; this is the reduction of the flagship built from it together with Olshanskii's quotient theorem and Kapovich--Wise
---

**ESTABLISHED** through `nonsofic-hyperbolic-question-reduces-to-one-fixed-host-proof`.

Let `P` be soficity, hyperlinearity, or any local approximation property
`P_M` of `local-approximation-properties-are-marked-closed` that every finite
group has. Let `T` be any non-elementary word-hyperbolic group with trivial
maximal finite normal subgroup. The following are equivalent.

1. Some word-hyperbolic group fails `P`.
2. Some group that is locally embeddable into hyperbolic groups (LEH) fails
   `P`. The definition is in
   `hyperbolic-local-embedding-kills-compression-certificates`. Marked limits
   of hyperbolic groups, lacunary hyperbolic groups and `B(m,N)` in the Coulon
   range are LEH.
3. For every finite `M subset T` there is a surjection `pi : T -> Q`,
   injective on `M`, with the following properties:
   - `Q` is a non-elementary word-hyperbolic group;
   - `Q` fails `P`;
   - `Q` has no nontrivial finite quotient.
4. `T` has a word-hyperbolic quotient that fails `P`.

**Kazhdan host.** Take `T` torsion-free, non-elementary, hyperbolic and
Kazhdan (`torsion-free-hyperbolic-kazhdan-partner-exists`). Then the
following hold.
- A nonsofic hyperbolic group exists iff this one fixed group has a nonsofic
  hyperbolic quotient.
- Every such quotient in (3) is Kazhdan and has no nontrivial finite quotient.
- A counterexample makes `T` a marked limit of nonsofic, finite-quotient-free
  Kazhdan hyperbolic quotients of itself.

**How it combines.** Condition (2) enlarges the search space from hyperbolic
groups to every local limit of hyperbolic groups. The companion obstruction
`hyperbolic-local-embedding-kills-compression-certificates` shows that every
compression-defect and commuting-non-LEF certificate in the graph vanishes
on this larger class. So the certificate must be of a different kind.
Condition (3) shows that no generality is lost by searching only among
finite-quotient-free quotients of one fixed linear Kazhdan lattice.

No literature survey for novelty was done. Not Lean-verified.
