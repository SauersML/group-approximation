---
rg: 2
id: haagerup-hosts-blind-full-group-kazhdan-certificate
kind: claim
title: Kazhdan groups acting through the full group of a free action of a Haagerup group have finite orbits, so Theorem C certificates never fire for Haagerup hosts such as F2 x F2
distinct_from:
  irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups: that treats bounded (finite-range) cocycles and gets infinite stabilizers, then uses IRS rigidity; this treats the whole full group with unbounded cocycles, gets finite orbits for every Kazhdan group, and applies it to Kun--Thom fixed algebras
  kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions: that kills Theorem C for subgroups of a mixing acting group; this kills it for every Kazhdan pair acting through full-group elements when the acting group is Haagerup, with no mixing assumption
  compact-extension-kazhdan-fixed-algebras-are-blind: that kills Theorem C on compact extensions; this kills it on the orbit relation itself for a class of acting groups
---

**ESTABLISHED.** Let `G` be a countable group with the Haagerup property and `G ↷ (X,μ)` an essentially free
p.m.p. action with orbit relation `R_G`. Let `Γ` be a countable group with property (T) and `ρ : Γ → [R_G]` a
homomorphism into the full group. Then:

1. **Finite orbits.** Almost every `ρ(Γ)`-orbit is finite. The cocycle is not assumed to have finite range.
2. **Blind certificate.** Let `Γ <= L` with `L` Kazhdan and `Γ` infranormal in `L`, and let `ρ : L → [R_G]` be a
   homomorphism. Then `L^∞(X)^(ρ(Γ))` is `ρ(L)`-invariant.

So the certificate `full-group-kazhdan-pair-noninvariant-fixed-algebra-is-nonsofic` never fires on a free action of a
Haagerup group. By the same argument, every Bernoulli extension of such an action over the orbit subrelation of
`ρ(Γ)` has an invariant fixed algebra for the lifted pair, because the lifted `ρ(L)` still has finite orbits on the
base. Theorem C then does
not apply to any Haagerup group in any of these forms:

* restricted to subgroups;
* on factors and restrictions;
* on compact extensions;
* through piecewise group elements.

**Class killed.** Hosts covered: amenable groups, free groups, `F_2 × F_2`, surface groups, lattices in `SO(n,1)` and
`SU(n,1)`, and CAT(0) cubical groups. For `f2xf2-admits-mixing-nonsofic-action`, every Kazhdan infranormal pair acting
through the full group of a free `F_2 × F_2`-action has an invariant fixed algebra. A Kun--Thom style obstruction for
`F_2 × F_2` must use something other than Theorem C on the action's own crossed product, for example Theorem C on an
extension that is neither compact nor Bernoulli over a subrelation. A host for the full-group certificate must contain
a non-Haagerup subgroup, and the Kazhdan copy `ρ(L)` must have infinite orbits on a set of positive measure.

**Calibration.** For `G` amenable, the free actions are sofic (Elek--Lippner, Păunescu), so the certificate cannot
fire. The claim reproduces this through clause 2. For `G = L` Kazhdan and `ρ = id`, orbits are infinite. The
Haagerup hypothesis is necessary, since an infinite Kazhdan group is not Haagerup.

**Credit.** Bounding cocycles from Kazhdan groups into Haagerup groups is standard. The route through positive
definite functions is chosen because it needs no integrability of the cocycle. Clause 2 and its use against the
certificate are new to this graph.

Proof: `haagerup-hosts-blind-full-group-kazhdan-certificate-proof`.
