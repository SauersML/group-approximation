---
rg: 2
id: residually-li-amenable-groups-are-torus-surjunctive
kind: claim
title: Over residually-(locally indicable amenable) groups, including every Baumslag-Solitar group, injective torus automata have regular degree and are surjective
distinct_from:
  lef-groups-are-torus-surjunctive: that uses exact finite models and a small-fibre lemma, so it needs LEF; this uses a division ring that dominates the augmentation, needs no finite models, and covers finitely presented non-LEF groups such as BS(2,3).
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that needs residual finiteness (or d = 1 over a domain); this is proved at every d for groups that are typically not residually finite, and uses only the N = G case of its periodic-point lemma.
  torus-degree-regular-on-prime-power-residual-support: that needs <supp D> residually prime-power, hence residually finite; this needs <supp D> residually-(LI amenable), a class with non-Hopfian finitely presented members.
  abelian-groups-are-torus-surjunctive: abelian torsion-free groups are a special case here; groups with torsion are not covered by this method at all (artifact Section 5.1).
  injective-torus-automata-have-regular-degree: that is C2 for every group; this proves it when <supp D> is RLA, and reduces the locally indicable case to one ring-theoretic condition (AD).
  every-group-is-torus-surjunctive: that is the statement for every group; this is the RLA case.
  flat-weak-bass-holds-exactly-for-locally-indicable-groups: that concerns flat weak Bass conditions and cites universality for all LI groups; this uses universality only where it is published (RLA groups) and applies it to torus automata.
artifacts:
  - research/artifacts/residually-li-amenable-torus-2026-09-18.md
---

Call a group **RLA** if it is residually-(locally indicable and amenable). Let `G` be a
countable group, `d >= 1`, and `tau: (T^d)^G -> (T^d)^G` an injective, continuous,
`G`-equivariant map with degree matrix `D in M_d(Z[G])` (`tau^*(xi) = xi D` on
`H^1 = Z[G]^d`). Put `H = <supp D>`.

1. **Criterion.** Suppose `Q[H]` embeds in a division ring `E` so that every square matrix over
   `Q[H]` whose augmentation is invertible over `Q` becomes invertible over `E`. Then
   `xi -> xi D` is injective on `Q[G]^d`, which is C2
   (`injective-torus-automata-have-regular-degree`) for `tau`, and `tau` is a homeomorphism.
2. **Hosts.** If `H` is RLA, the criterion holds with `E = D_{Q[H]}`. So every countable group
   whose finitely generated subgroups are RLA is torus-surjunctive at every `d`.
3. **Free-by-(LI amenable) groups are RLA.** In particular every `BS(m,n)` with `mn != 0` is
   RLA. This includes `BS(2,3)`, which is finitely presented and non-Hopfian, so neither
   residually finite nor LEF nor amenable.

Other hosts: every LI amenable group, every amenable left-orderable group, every free-by-cyclic
group, and every residually torsion-free nilpotent group (free groups, surface groups, RAAGs).

**Limits** (artifact Section 5):
- The criterion forces `H` torsion-free.
- For a general locally indicable `H`, the criterion with `E = D_{Q[H]}` is the condition
  (AD): Cohn specialization from `D_{Q[H]}` to `epsilon`. It is open.
- For Thompson's `F`, every proper quotient is abelian. So `F` is RLA if and only if `F` is
  amenable, and then `F` is torus-surjunctive.
- RLA groups are sofic, so Gottschalk's conjecture was already known over them. The gain is in
  the torus lane, C2.

**ESTABLISHED 2026-09-18** by [[residually-li-amenable-groups-are-torus-surjunctive-proof]].
The proof is not yet independently reviewed.

## Attempts

- 2026-09-18 (swarm-0917-w11-w11-gs-follow): proof in artifact Sections 2–4, limits in
  Section 5.
  - It closes the w10 "first open instance" `d = 2` over `BS(2,3)`, at every `d`.
  - The attempt to cover all locally indicable groups died at universality (see lease
    `locally-indicable-groups-are-torus-surjunctive`, dead).
