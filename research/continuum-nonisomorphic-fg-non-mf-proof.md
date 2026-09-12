---
rg: 2
id: continuum-nonisomorphic-fg-non-mf-proof
kind: route
title: Subgroup heredity plus abelianization rank, then Neumann's continuum family
target: continuum-nonisomorphic-fg-non-mf
requires: [mf-positive-controls, literal-group-fails-mf-conventions, constructed-continuum-of-finitely-generated-groups]
artifacts:
  - GroupApproximation/Sofic/ProductMultiplicity.lean
  - GroupApproximation/Sofic/ProductMultiplicityRank.lean
  - GroupApproximation/Algebra/TorsionFreeRank.lean
  - GroupApproximation/Sofic/ContinuumMultiplicity.lean
  - GroupApproximation/Sofic/ContinuumMultiplicityCore.lean
---

# Subgroup heredity plus abelianization rank, then Neumann's continuum family

Recovered proof, transcribed verbatim from the deleted manuscript subsection at
`git show c3501887:non_mf_groups_exist.tex`, lines 2095-2129. The first two
`requires` are the graph nodes supplying its two inputs: subgroup heredity of MF
(`mf-positive-controls`) and non-MF-ness of `E` (`literal-group-fails-mf-conventions`).
The third, [[constructed-continuum-of-finitely-generated-groups]], is the
continuum family part (2) needs; it was an external citation when this route was
written and is now a theorem of the development.

## The two inputs

Subgroup heredity, still live in the manuscript at line 1907 and Lean-verified:

> **Lemma (subgroups).** Every subgroup of an MF group is MF.
> `\leanverified{Sofic/OperatorMFPositiveControls}{GroupApproximation.IsOperatorMF.subgroup}`
>
> *Proof.* Restrict an injective corona representation to the subgroup:
> injectivity and the homomorphism law are preserved.

Equivalently: a group containing a non-MF subgroup is not MF. Combined with
`E` non-MF, every group containing an isomorphic copy of `E` is non-MF.

## The proof, verbatim

> Every group in sight contains an isomorphic copy of $E$, hence is
> non-MF by Theorem~\ref{thm:A} and Lemma~\ref{lem:subgroupMF}.
>
> (1) $E\times\Z^k$ is finitely presented because $E$ is.  Its
> abelianization is $E^{\mathrm{ab}}\times\Z^k$; since $E$ is finitely
> generated, $E^{\mathrm{ab}}$ is a finitely generated abelian group,
> of some torsion-free rank $r_0<\infty$, so the abelianization of
> $E\times\Z^k$ has torsion-free rank $r_0+k$, an isomorphism
> invariant that separates distinct $k$.
>
> (2) By a classical construction of B.\,H.~Neumann \cite{Neumann}
> there is a family $(N_i)_{i\in I}$ with $|I|=2^{\aleph_0}$ of
> pairwise non-isomorphic $2$-generator groups.  Put
> $G_i=E\times N_i$, a finitely generated non-MF group.  For a fixed
> countable group $G_1$, the set $\{i\in I:G_i\cong G_1\}$ is
> countable: a countable group has only countably many finitely
> generated subgroups (each is determined by a finite generating
> subset), hence countably many isomorphism classes of such; if
> $G_i\cong G_1$ then $N_i$ embeds into $G_1$ as $\{1\}\times N_i$;
> and the $N_i$ are pairwise non-isomorphic, so
> $i\mapsto[N_i]$ is injective on the set in question.  A map from a
> set of cardinality $2^{\aleph_0}$ with countable fibres has image of
> cardinality $2^{\aleph_0}$; apply this to $i\mapsto[G_i]$.

## The external citation, verified — and then removed

B. H. Neumann, *Some remarks on infinite groups*, J. London Math. Soc. **s1-12**
(1937) 120-127 — continuum many pairwise non-isomorphic 2-generator groups.

**It is no longer an input.** The development now constructs its own continuum
family — [[constructed-continuum-of-finitely-generated-groups]], the alternating
lamplighters `A5 wreath_{F2/markedSubgroup S} F2` — which is finitely generated
rather than two-generator, and that is all the counting step consumes. The
citation stays in the manuscript's prior-work discussion; nothing in this route
rests on it.

## Remarks on the argument

The cardinality step is the only delicate one, and it is elementary: it shows
the fibres of `i |-> [G_i]` are countable, not that the map is injective. Two
distinct `N_i` can in principle give isomorphic products; what cannot happen is
that uncountably many do, because all of them would then embed as finitely
generated subgroups of one fixed countable group, of which there are only
countably many up to isomorphism.

Part (1) is strictly stronger than part (2) in one respect and strictly weaker
in another: its witnesses are finitely *presented* (since `E` is), but there are
only countably many of them. Part (2) reaches the continuum at the cost of
dropping to finitely generated, because Neumann's family is not a family of
finitely presented groups — there are only countably many finite presentations.
No argument in the corpus produces continuum many finitely presented non-MF
groups, and none can: that cardinality is an absolute bound.

## Lean status of the two parts

**Part (1) is machine-checked twice, and the second time with the invariant the
manuscript actually printed.**

* `Sofic/ProductMultiplicity` proves it with a *substitute* invariant: it counts
  homomorphisms into `Z/2`, which is the torsion-free rank read modulo `2`.  The
  count separates the same groups, so the conclusion is right, but the printed
  argument does not go that way.
* `Sofic/ProductMultiplicityRank.manuscriptInfiniteMultiplicityRank` runs the
  printed argument, through `Algebra/TorsionFreeRank`: the torsion-free rank of
  an abelian group is `dim_Q (Q ⊗_Z A)` — tensoring with `Q` is what kills the
  torsion, and this is checked rather than assumed
  (`torsionFreeRank_eq_zero_of_forall_zsmul_eq_zero`); rank is additive over
  products (`torsionFreeRank_prod`) and `rk Z = 1`; abelianization commutes with
  binary products, which Mathlib lacks and `abelianizationProd` supplies, giving
  `(E x Z^k)^ab ≅ E^ab x Z^k`; `E` finitely presented makes `rk E^ab` *finite*
  (`torsionFreeRank_lt_aleph0`), which is what makes `rk E^ab + k` determine
  `k`; and equal invariants on isomorphic groups finish.  The counting proof
  stays in place as an independent second route.

**Part (2) is now formalized too, and unconditionally.**
`Sofic/ContinuumMultiplicity.manuscriptContinuumMultiplicity` states all three
printed sentences with no premises: the deduction (for any continuum-sized
pairwise nonisomorphic family of finitely generated `N`, the products `E x N`
have continuum many isomorphism types, all non-MF), the existence of such a
family, and the conclusion.  The middle conjunct is
`NeumannContinuum.neumann_continuum_of_finitely_generated_groups`, so the family
is *built* rather than quoted; `Sofic/ContinuumMultiplicityCore` carries the
counting step and `Sofic/ContinuumFamilyCriterion` the reduction that made the
construction cheap to supply.

Note the shape of the third conjunct: the products `E x N` need not be pairwise
nonisomorphic even when the `N` are, so what is exhibited is a transversal of
the isomorphism classes of the products — which is exactly what the counting
step produces, and is stronger than applying the deduction blindly.

This is also the answer to the remark in the claim body about
`scaling-family-pairwise-nonisomorphic`: the abelianization-rank invariant is
now not merely "cheap to compute" but *available as a Lean API*
(`abelianizationRank`, with congruence, additivity and finiteness), so trying it
on the `E_m` is a matter of computing one abelianization, not of building
machinery.
