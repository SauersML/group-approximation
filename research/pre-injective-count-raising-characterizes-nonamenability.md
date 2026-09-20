---
rg: 2
id: pre-injective-count-raising-characterizes-nonamenability
kind: claim
title: A group is non-amenable exactly when some pre-injective automaton with a never-created quiescent letter raises the count of a finite configuration
distinct_from:
  finite-injective-charge-noncreation-forces-surjectivity: that is the primal statement, where noncreation of a charge plus injectivity on finite configurations forces surjectivity over every group; this is the dual direction, where noncreation of a letter plus pre-injectivity forces count preservation over exactly the amenable groups.
  reversible-automata-that-never-lower-rest-counts-preserve-them: that is for reversible automata over every group; this drops invertibility to pre-injectivity and shows the dual then fails at every non-amenable group.
  capobianco-kari-taati-dual-surjunctivity-toolkit: that imports Bartholdi's Theorem 1.1 as a Garden-of-Eden statement; this augments the automaton of its proof by a support flag and adds the amenable converse.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that is the Moore--Myhill equivalence of surjectivity and pre-injectivity; this is a statement about supports of images, which it is one input for.
artifacts:
  - experiments/pre-injective-count-raising-2026-09-17/verify_flag_bartholdi.py
---

**ESTABLISHED.** The route is `pre-injective-count-raising-nonamenability-proof`.

Call a cellular automaton `τ : A^G -> A^G` **letter-dual** for a letter `0 ∈ A` if `τ(0^G) = 0^G` and `τ` never creates
`0`, meaning `x(g) ≠ 0` implies `τ(x)(g) ≠ 0`. For every group `G` the following are equivalent.

1. `G` is amenable.
2. Every pre-injective letter-dual automaton over `G`, for every finite alphabet, satisfies `supp τ(x) = supp x` for every
   `x ∈ A^G`.
3. No pre-injective letter-dual automaton over `G` raises the number of non-`0` sites of a finite configuration.

(2) and (3) are equivalent over every group, since a letter-dual automaton has `supp τ(x) ⊇ supp x` and its local rule is
witnessed on a finite configuration.

**The automaton at a non-amenable group.** Take the linear automaton `Θ` from the proof of Bartholdi's Theorem 1.1. It is
injective on finitely supported configurations, and its values lie in a proper coordinate subspace `K^{∪X_s}` of
`A = K^Y`. Fix `y0 ∈ Y \ ∪X_s` and set

    τ(φ)(g) = Θ(φ)(g) + [φ(g) ≠ 0] e_{y0}.

- `τ` is letter-dual, because the `y0`-coordinate of `τ(φ)(g)` is the support flag.
- `τ` is pre-injective, because deleting the `y0`-coordinate gives `Θ`.
- `τ` raises the count of the single-site configuration `aδ_h`, for any `a` with `α_s(a) ≠ 0` for some `s ≠ 1`. Such a pair
  exists because `α_1` alone cannot be injective.

`τ` is injective exactly when `Θ` is (when `|K| >= 3`). So it is never a dual counterexample without first being a
Gottschalk counterexample.

**Consequence: a whole method class dies.** Let the *finite-difference class* be every argument for the dual charge
theorem (need `ebb50f1d` on `nonsurjunctive-alphabet-sizes-are-upward-closed`) that uses injectivity only through pairs of
configurations differing at finitely many sites. Such arguments include finite-configuration counting, wandering finite
supports, and the Moore--Myhill route.

- A failure of the dual at `G` makes `G` non-surjunctive, hence non-sofic, hence non-amenable. At every such host, the
  automaton above satisfies every hypothesis these arguments use, and it violates their conclusion.
- The step where every member dies is the first use of injectivity. Replacing it by pre-injectivity leaves an automaton
  for which the conclusion is false.
- The kill covers torsion hosts with no free subgroup, such as free Burnside groups of large odd exponent and Tarski
  monsters, which are non-amenable. The free-subgroup calibration recorded in wave w23 (pre-injective automata on
  groups containing `F_2`) does not reach them.
- A proof of the dual must use injectivity on pairs that differ at infinitely many sites.

The contrast is with the primal `finite-injective-charge-noncreation-forces-surjectivity`, which needs only finite
injectivity over every group.

**Instance on `F_2`.** Take `A = GF(2)^{u,v}` and

    τ(x)(h) = (u(h) + u(ha^{-1}) + v(h) + v(hb^{-1}), [x(h) ≠ 0]).

The script checks injectivity of the first coordinate on all balls up to radius 6. The first coordinate is the mod-2
boundary of a finite edge set of the Cayley tree. That boundary is nonzero, because a nonempty finite forest has a leaf. The constants `(1,1)^G` and
`(1,0)^G` collide, so `τ` is not injective.
