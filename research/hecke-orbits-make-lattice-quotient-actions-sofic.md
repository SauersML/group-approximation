---
rg: 2
id: hecke-orbits-make-lattice-quotient-actions-sofic
kind: claim
title: A Zariski-dense sofic subgroup acting on a lattice quotient of a simple Lie group is sofic as soon as it has infinitely many finite orbits
distinct_from:
  sl3-split-class-lattice-quotient-actions-are-sofic: that treats pairs in the commensurability class of SL3(Z) through duality, restriction and a Howe-Moore Hecke theorem; this gives every simple real Lie group and every commensurability class at once from Benoist-Quint equidistribution of finite orbits
  finite-equidistributed-orbits-give-sofic-action: that is the soficity criterion from equidistributed finite invariant sets; this supplies the equidistribution for all lattice quotients, so the criterion applies whenever finite orbits are infinite in number
---

**ESTABLISHED (unreviewed).** Let `G` be a connected real Lie group with simple Lie algebra, `Λ <= G` a
lattice, and `Γ <= G` a countable sofic subgroup that is Zariski dense (`Ad(Γ)` Zariski dense in `Ad(G)`).
If `Γ ↷ G/Λ` has infinitely many finite orbits, then `Γ ↷ (G/Λ, Haar)` is sofic (Păunescu Definition 1.4).

**Instances.**
1. *Same-class pairs, any `G`.* Let `Γ_1` and `Γ_2` be lattices such that `Γ_1` is commensurable with
   `hΓ_2h^(−1)`, and suppose `[Comm_G(Γ_1) : Γ_1] = ∞`. For `g ∈ Comm_G(Γ_1)h`, the point `gΓ_2` has a finite
   `Γ_1`-orbit, and there are infinitely many such orbits. Examples: `SL_n(Z)`, and the norm-one groups
   `SL_1(O_D)` of maximal orders in division algebras of degree `3` split over `R`, acting on quotients
   by commensurable conjugates. Their commensurators contain the dense groups `SL_n(Q)` and
   `SL_1(D)(Q)`.
2. *`SL_3(R)`.* This recovers `sl3-split-class-lattice-quotient-actions-are-sofic` and gives the same
   conclusion inside every commensurability class of arithmetic lattices, cocompact ones included.
3. *Rank one.* For arithmetic lattices in `SO(n,1)`, `SU(n,1)` and `Sp(n,1)`, the action of `Λ` on `G/Λ` is
   sofic. The `Sp(n,1)` case is a property (T) instance. This uses only that the commensurator of an
   arithmetic lattice contains the dense group of rational points of its `Q`-form, so it has infinite
   index (recalled, not imported).

**Where it stops.** Two cases give only finitely many finite orbits: pairs from different
commensurability classes (for example `sl3z-on-cocompact-lattice-quotient-is-not-sofic`), and lattices
with commensurator of finite index. By Margulis' commensurator criterion (recalled, not imported) the
latter are the non-arithmetic lattices, such as the Gromov--Piatetski-Shapiro lattices in `SO(n,1)`.
For such `Λ`, `Λ ↷ G/Λ` is a free mixing action beyond the reach of this mechanism
(`simple-group-lattice-admits-nonsofic-action`).

Proof in `hecke-orbits-make-lattice-quotient-actions-sofic-proof`.
