---
rg: 2
id: sl3z-nonuniform-outer-form-quotient-wc-in-finite-actions
kind: claim
title: Is SL3(Z) on SL3(R)/SU(h,O_E), a non-uniform lattice of an outer form, weakly contained in finite actions?
distinct_from:
  sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions: that is the cocompact case, where the flat-label normal form and uniform distance hold; this is the non-uniform case outside the SL3(Z) class, where cusp excursions carry holonomy without bad pairs
  sl3z-every-cocompact-quotient-far-from-finite-actions: that settles exact finite models for every cocompact lattice; this is the complementary family of lattices, where even exact finite models are undecided
---

**OPEN (two-sided).** Let `E` be a real quadratic field and `h` an isotropic hermitian form in three variables
over `E`. Put `Λ = SU(h, O_E)`, which is (recalled) a non-uniform lattice in `SU(h)(R) ≅ SL_3(R)`, of
`Q`-rank `1`. Is `SL_3(Z) ↷ (SL_3(R)/Λ, Haar)` weakly contained in finite actions? A second, stronger
question: for some scale `ε > 0`, is there a finite `SL_3(Z)`-set with marks that are `ε`-equivariant at
every vertex?

**Facts (recalled).** `SU(h)` is an outer `Q`-form of type `A_2` and `SL_3` the split inner one. So `Λ` is not
commensurable with any conjugate of `SL_3(Z)`. As in `sl3z-on-cocompact-lattice-quotient-is-not-sofic`, the
action is essentially free and mixing, and has no finite orbits.

**Why it matters.** Every lattice commensurable with a conjugate of `SL_3(Z)` has exact finite models
(Hecke orbits). No cocompact lattice has models with every vertex good
(`sl3z-every-cocompact-quotient-far-from-finite-actions`). This family is the remaining complement.
* *A positive answer* gives a higher-rank, essentially free, mixing lattice-quotient action with no
  periodic orbits that is weakly contained in finite actions, hence sofic: a new soficity mechanism.
* *A negative answer* would show that uniform distance, or even the weak-containment exclusion, depends
  only on commensurability, cusp or no cusp.

## Attempts

* **Hecke orbits.** Dead: there are no finite orbits.
* **Theorem E.** Dies at the cusp. Lemma 1.1 of the flat-labels artifact needs lifts in a compact set:
  labels are unique only when conjugation by the lift distorts `ε` by less than `r_Λ`. Deep in a cusp,
  `Λ` has elements, from the unipotent radical of a rational parabolic, that move the point by less
  than `ε`. There labels are not unique, and good relator cycles need not be flat. So a finite model
  can carry nontrivial holonomy through cusp cells *without any bad pair*. Norm drift is not the
  obstacle: it applies to good pairs anywhere, but it needs a finite invariant labelled set, which
  exists only when the labels are flat.
* **Holonomy of honest flat labellings.** Still finite: the Remark in
  `sl3z-maps-to-cocompact-lattices-have-finite-image` (superrigidity plus the classification of
  automorphisms of `SL_3(R)`, recalled) forbids infinite-image homomorphisms from finite-index subgroups
  of `SL_3(Z)` into lattices outside the class. So a model must break flatness, either at bad pairs or at
  cusp cells.
* **Separable models.** The proof of `sl3z-cocompact-not-factor-of-bernoulli-times-profinite` goes
  through with that Remark in place of step 5, so Bernoulli-times-profinite models are excluded here too
  (sketch).
* **Cusp seams (heuristic, positive).** Route the holonomy needed to escape norm drift through
  excursions into cusp neighbourhoods of vanishing Haar measure. Marks can stay good there, because many
  labels are admissible. The seams have to be placed consistently with an honest congruence action of
  `SL_3(Z)`, and no construction is known.
