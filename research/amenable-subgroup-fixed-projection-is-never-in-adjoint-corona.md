---
rg: 2
id: amenable-subgroup-fixed-projection-is-never-in-adjoint-corona
kind: claim
title: In a delta_e-profile adjoint corona, an amenable subgroup with an infinite conjugacy class never has its fixed-vector projection in the corona, so no transport through an amenable subgroup of EL_5(J) can exclude the regular MF character
distinct_from:
  root-column-fixed-projection-is-not-in-root-pair-cstar: that excludes P_N only from C*(sigma~(K)), needs a centralizing root with amenable centralizer and relative (T) bookkeeping, and leaves P_N in B open; this excludes P_L from all of B, for every amenable L with one infinite conjugacy class, using only the conjugation representation on l^2 of that class. In particular it refutes the single prerequisite that claim's What-is-left reduced the column route to.
  corona-fixed-projection-membership-is-finite-markov-gap: that is the general saturation equivalence for any subgroup; this supplies, for amenable subgroups in delta_e-profile models, the almost-invariant vectors orthogonal to Fix(L) that rule the equivalent uniform gap out.
  window-average-kazhdan-substitute-forces-trivial-corona-rep: that kills norm limits of window averages over one locally finite root subgroup in any model; this kills every element of B at once, for every amenable subgroup, in the delta_e-profile models.
  model-spectral-gap-quantifier-ladder: that shows representation-generic proofs of (MSG) for a nonamenable L are Kazhdan theorems; this is the complementary amenable half, where (MSG) is false outright in every delta_e-profile model, not merely unprovable generically.
  jacobson-regular-character-not-mf-without-property-t: that is the open hole on the live route; this shows which transport arguments cannot close it.
artifacts:
  - research/amenable-fixed-projection-not-in-adjoint-corona-proof.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED KILL (written proof; not Lean-verified).** Notation is that of
`corona-fixed-projection-membership-is-finite-markov-gap`: `(V_n)` is an
operator-norm asymptotic representation of a countable group `G`,
`sigma~=[Ad V_n]` maps into the adjoint corona `B`, `H_B=direct_sum_omega
H_omega`, and `P_L` is the projection onto `Fix pi(sigma~(L))`.

**Theorem A (amenable conjugacy obstruction).** Let `L<=G` and `g in G`, and
put `O={lgl^(-1): l in L}`. Assume:
- (A1) `L` is amenable, meaning that `L` has a left Folner sequence;
- (A2) `O` is infinite;
- (A3) `tr V_n(x)->0` for every `x != e` in `<L,g>`.

Then:
- in every `H_omega` there are unit vectors in `Fix(L)^perp` that are
  `epsilon`-invariant under any given finite `F subset L`;
- consequently `P_L notin pi(B)`.

More generally, without (A1), `P_L in pi(B)` forces a finite `F subset L`
and `c>0` with `sup sp(lambda_(L/C_L(g))(h_F)) <= 1-c`. This holds for every `g`
such that `tr V_n -> delta_e` on `<L,g>` and the `L`-class of `g` is infinite. So the conjugation action
of `L` must be **uniformly non-amenable on all its infinite classes**.

**Invariant.** The conjugation representation of `L` on `l^2(O)`.
- It embeds isometrically and equivariantly in `H_omega` by
  `delta_o -> [V_n(o)]`.
- It lies in `Fix(L)^perp`, because `O` is an infinite transitive `L`-set.
- It is amenable, via the Folner pushforward.

**Corollary B (the column prerequisite is false).** Take `J=F_2<S,T|TS=1>`,
`G=St_5(J)=EL_5(J)`, `N=X_13(J)X_23(J)` and `g=x_21(1)`. Then
`x_13(a) x_21(1) x_13(a)^(-1) = x_21(1) x_23(a)`, so the class is infinite.
So in every model with `tr V_n -> delta_e` on `K=<X_12(J),X_21(J),N>`, the
projection `P_N` is not in `B`. The prerequisite "`P_N in B`" is therefore
**false** in every `delta_e`-profile model. That is the one prerequisite to
which `root-column-fixed-projection-is-not-in-root-pair-cstar` reduced the
(T)-free column transport. So the route is not merely unreachable from
`A_K`: it has no witness at all.

**Corollary C (every amenable subgroup of `EL_5(J)`).** `Z(EL_5(J))=1`, and
`EL_5(J)` is finitely generated. So every infinite subgroup `L` has an
element of infinite `L`-class, because a finite-index subgroup of `L`
centralizing a finite generating set would be central. Hence, in every
operator-norm asymptotic representation of `E=EL_5(J)` with traces tending
to `delta_e` (these are exactly the witnesses that
`jacobson-regular-character-not-mf-without-property-t` must exclude),
**no infinite amenable subgroup `L<=E` has `P_L in B`**. This covers the root
column, the finitary kernel `GL_fin`, the `SL_fin` certificate of the
rank-pigeonhole attempt, every root subgroup and every locally finite
window.

**Class killed.** Every argument of the form "run `thm:transport` or
`cor:defect-hs` through a subgroup `L` whose fixed projection is obtained
somewhere in `B`", with `L` amenable. Relative (T), Markov functional
calculus, Folner averages, carrier projections and corona modules are all
covered, by `corona-fixed-projection-membership-is-finite-markov-gap`.
- *Step where every member dies:* producing `P_L in B`.
- *Invariant:* the amenable conjugation representation on `l^2` of an
  infinite `L`-class.
- *Scope:* this is a statement about the models the live route must exclude,
  not about their absence. Calibration: in such a model, if one existed, the
  projection is genuinely absent.

**What is left for transport.** Together with `model-spectral-gap-quantifier-ladder`,
transport-based (T)-free proofs of the head collapse are squeezed into one
form. One needs a **nonamenable** `L<=EL_5(J)` whose conjugation action is
uniformly non-amenable on all its infinite classes, and a model-specific
(non-generic) proof of `(MSG)` for a finite subset of `L`. Such a proof
must use the `delta_e`-profile, the operator-norm structure, or the
finite-dimensionality of the coordinates, because a representation-generic
proof would be a Kazhdan theorem.

Proof route: `amenable-fixed-projection-not-in-adjoint-corona-proof`.
