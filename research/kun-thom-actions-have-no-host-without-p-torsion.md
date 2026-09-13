---
rg: 2
id: kun-thom-actions-have-no-host-without-p-torsion
kind: claim
title: No free action of a group without infinite elementary abelian p-subgroups has a restricted orbit relation containing the Kun--Thom action of a Theorem E pair over a field of characteristic p
distinct_from:
  kun-thom-action-soe-class-is-rigid: that shows an embedding of the diffuse Kun--Thom relation is a virtual conjugacy when every invariant finite subrelation of the host lies in the copy; this drops that hypothesis for hosts with no infinite elementary abelian p-subgroup, where no embedding exists at all
  rigid-bernoulli-seed-relations-embed-their-group-in-the-host: that treats Bernoulli seeds of nonsofic groups, which have no sofic host; this treats the nonsofic generalized Bernoulli actions of the sofic Kun--Thom group, which do have sofic hosts such as the group itself, and excludes hosts without p-torsion
  groups-containing-kun-thom-pair-have-nonsofic-actions: that uses these actions to reach hosts that contain the pair, all of which have infinite elementary abelian p-subgroups; this shows that containment cannot reach hosts without them
---

**ESTABLISHED (unreviewed).** Let `q` be a power of the prime `p`, `r,d >= 3`, and `Γ = EL_r(R_+) < G = EL_r(R) ⋊ SL_d(Z)`
the Theorem E pair of `kun-thom-nonsofic-wreath`. Let `(Y,ν)` be a nontrivial standard probability space. Let `σ_Y` be the
generalized Bernoulli action of `G` on `(Y,ν)^K` over the `G`-set `K = G/Γ ⊔ G`. With `Y = {0,1}` this is the
free nonsofic action of `kun-thom-free-nonsofic-action`, and with `Y = [0,1]` it is the diffuse action of
`kun-thom-action-soe-class-is-rigid`.

Let `G'` be a countable group with no infinite elementary abelian `p`-subgroup. Let `G' ↷ (X,μ)` be an essentially
free p.m.p. action, and `A ⊆ X` measurable with `μ(A) > 0`. Then no measure-space isomorphism
`θ : (Y,ν)^K → (A,μ_A)` carries the orbit relation of `σ_Y` into `R_(G')|_A`. The same holds for any free action of
any countable group containing `G` whose restriction to `G` is some `σ_Y`.

**Hosts covered.** Two kinds:

* virtually torsion-free groups, in which a torsion subgroup injects into a finite quotient;
* groups linear over a field of characteristic `≠ p`, in which an elementary abelian `p`-subgroup of `GL_n` has
  order at most `p^n`.

In particular: `SL_3(Z)` and every lattice of `SL_3(R)`, every finitely generated linear group in characteristic
`0`, `F_2 × F_2`, and torsion-free lattices in products of trees.

**Use.** `kun-thom-action-soe-class-is-rigid` left one design for a mixing host containing this relation: glue a
`G`-invariant finite subequivalence relation onto the copy. For the hosts above nothing can be glued, because there
is no copy.

So by containment, the nonsofic relations of Theorem E pairs cannot seed `sl3z-admits-nonsofic-action`, a lattice
of a characteristic-zero Howe--Moore group (`simple-group-lattice-admits-nonsofic-action`), or `F_2 × F_2`
(`mixing-free-nonsofic-action-of-sofic-group`). Hosts with infinite elementary abelian `p`-subgroups are not
covered, and `G` itself is one.

Proof: `kun-thom-action-host-via-root-group-ergodicity`.
