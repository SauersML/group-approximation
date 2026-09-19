---
rg: 2
id: sofic-stages-give-torsion-free-quotientless-sofic-kazhdan
kind: claim
title: If the torsion-free hyperbolic quotients of one Sp(n,1) lattice are sofic, its torsion-free Tarski monster is a sofic Kazhdan group without finite quotients
distinct_from:
  hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan: that assumes residually finite stages and concludes LEF; this assumes only sofic stages and concludes soficity, so its contrapositive reaches a nonsofic hyperbolic group rather than a non-residually-finite one.
  nonsofic-hyperbolic-question-reduces-to-one-fixed-host: that pushes nonsoficity into some hyperbolic quotient of a fixed host, possibly with torsion; this produces a torsion-free nonsofic quotient, and only from the failure of the quotientless Kazhdan gate.
  kazhdan-torsion-free-tarski-monster-satisfies-kk: that constructs the monsters and proves trivial projections; this adds soficity from sofic stages.
  torsion-free-sofic-kazhdan-group-without-finite-quotients: that is the open gate; this is a conditional supply of a member of it.
artifacts:
  - research/local-approximation-properties-are-marked-closed.md
  - research/hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof.md
---

**ESTABLISHED** by `sofic-stages-give-torsion-free-quotientless-sofic-kazhdan-proof`.

## Statement

Let `Γ` be a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2`, and let `Q` be its
Olshanskii--Osin--Sapir torsion-free Tarski monster quotient. Assume

```text
(S_Γ)  every torsion-free hyperbolic quotient of Γ is sofic.
```

Then `Q` is a nontrivial torsion-free, sofic, Kazhdan group with no nontrivial finite quotient.
So `Q` lies in the gate `torsion-free-sofic-kazhdan-group-without-finite-quotients`. `Q` is also
simple.

The same holds with "sofic" replaced by "hyperlinear", or by any local approximation property of
`local-approximation-properties-are-marked-closed`.

**Contrapositive (the calibration).** If the gate fails, then every such `Γ` has a torsion-free
hyperbolic quotient that is not sofic. In particular `nonsofic-hyperbolic-group` holds. So:
- the gate cannot be refuted without answering Gromov's soficity question for hyperbolic groups;
- neither can the flagship `torsion-free-sofic-exact-mf-radical-over-z` by any argument that uses
  only the intrinsic properties of its kernel.

(S_Γ) follows from (RF_Γ), and also from "every hyperbolic group is sofic". It is not known to be
equivalent to either.

**Consequence for witnesses with kernel `Q`.** Assume (S_Γ). For every `ψ ∈ Aut(Q)`, the group
`P = Q ⋊_ψ Z` is torsion-free and sofic, since it is sofic-by-amenable (Elek--Szabó). This moves the
soficity part of item (iii) of `tarski-monster-tori-evade-compression-and-stage-lifts` from
`(RF_Γ)` down to (S_Γ). By items (i) and (ii) of that node, `P` is a flagship witness iff three
conditions hold, each of which can fail on its own:
1. `[ψ]` has infinite order in `Out(Q)`;
2. `P` is finitely presented, i.e. `(Q, ψ)` has a finite automorphic presentation;
3. `P` is not operator MF.

`Q` is simple, so `Rad_MF(Q)` is `1` or `Q`. Condition 3 lies in (IO-int) if `Q` is not MF, and in
(IO-ext) if `Q` is MF. By route section 4, `Q` itself is never finitely presented (unconditional). So condition 2
already forces condition 1. If `[ψ]` had finite order, then `P` would contain `Q × Z` with finite
index. That subgroup would be finitely presented, and so would its retract `Q`.
