---
rg: 2
id: ce-covariant-models-force-solvable-kernel-closure
kind: claim
title: Q1 makes hyperlinearity closed under extensions with solvable or finite kernel, so Q1 excludes every solvable-by-hyperlinear candidate for a non-hyperlinear group
distinct_from:
  free-action-covariant-models-contain-the-crossed-product: that proves Q1 is equivalent to CE of all crossed products and draws the Kun--Thom consequence; this proves that Q1 forces permanence of hyperlinearity under abelian, solvable and finite kernels, and excludes whole lanes of candidates.
  unrestricted-algebraic-envelope-equals-nonhyperlinearity: that equates a non-CE algebra in some compact-abelian crossed product, with any actor, to NH; this fixes the actor, proves the equivalence with abelian-kernel closure over that actor, and ties it to Q1.
  amenable-quotient-preserves-metric-approximability: that is unconditional permanence for amenable quotients; this is conditional permanence for abelian, solvable and finite kernels over arbitrary hyperlinear quotients.
  abelian-by-virtually-free-groups-are-sofic: that is an unconditional theorem for virtually free quotients; this is conditional on Q1 and has an arbitrary hyperlinear quotient.
  hyperlinear-shadow-schur-cokernel-criterion: that compiles groups to non-hyperlinear central extensions of hyperlinear shadows; this shows that any success of that compiler refutes Q1.
---

**ESTABLISHED** by `ce-covariant-models-force-solvable-kernel-closure-proof`.

Q1 = `hyperlinear-group-actions-have-ce-covariant-models`. For a countable group `Lambda`, write
`Q1(Lambda)` for Q1 at the one group `Lambda`. By `free-action-covariant-models-contain-the-crossed-product`
this is the statement that every pmp crossed product of `Lambda` is CE. All groups are countable.

1. **Algebraic Q1 equals abelian-kernel closure, group by group.** For a fixed `Lambda` the
   following are equivalent:
   - (a) every group `G` with an abelian normal subgroup `A` and `G/A ≅ Lambda` is hyperlinear;
   - (b) every split extension `C ⋊ Lambda`, for a countable abelian `Lambda`-module `C`, is hyperlinear;
   - (c) `AQ1(Lambda)`: for every compact metrizable abelian group `K` with a continuous action of
     `Lambda` by automorphisms, `L^infinity(K, Haar) ⋊ Lambda` is CE.
2. **Q1 gives it.** `Q1(Lambda)` implies `AQ1(Lambda)`. Hence, under Q1, every abelian-by-hyperlinear
   group is hyperlinear, and in particular every central extension of a hyperlinear group.
3. **Solvable and finite kernels.** Assume Q1. Suppose `N ⊲ G` and `G/N` is hyperlinear. Then `G` is
   hyperlinear if `N` is solvable, and also if `N` is finite. More generally the same holds whenever
   there is a chain `N = N_0 ≥ N_1 ≥ ... ≥ N_k = 1` of normal subgroups of `G` with each
   `N_i/N_(i+1)` abelian or finite.
4. **Class exclusion (mutual exclusion with Q1).** The invariant is *hyperlinearity of the top
   quotient `G/N` together with a solvable-or-finite kernel `N`*. Every route whose candidate
   non-hyperlinear group has this shape refutes Q1. It does so at the step where the candidate is
   declared non-hyperlinear: by item 1, that candidate's group factor sits inside a Haar crossed
   product `L^infinity(K) ⋊ Lambda'` of a hyperlinear group `Lambda'`. Members of this class in the
   graph are:
   - the Kun--Thom wreath `W` and double (already found in w11);
   - every compact-abelian algebraic envelope with a hyperlinear actor. Examples are
     `algebraic-envelope-principle`, `non-ce-relation-admits-algebraic-action-envelope` and
     `algebraic-compact-action-envelope-for-non-ce-relation`, whenever the actor is hyperlinear. This
     covers residually finite and linear actors, and `Gamma × SL_3(Z)` with `Gamma` hyperlinear. A
     Haagerup actor is covered only once it is known to be hyperlinear;
   - the Mihailova coset wreath `W_N = (⊕_(L/N) C_2) ⋊ SL_3(Z)` of
     `mihailova-envelope-forces-one-sl3-coset-wreath`;
   - the finite-module witness `A_0 ⋊ SL_3(Z)` of `mixed-envelope-finitely-extracts-sl3-module-witness`;
   - every central-extension or `Z/p` witness, as in `hyperlinear-shadow-schur-cokernel-criterion`
     item (a') and `divisible-gap-bases-repel-hyperlinear-finite-covers`.

   So both covariant routes (`nonhyperlinear-via-full-subgroup-covariant-models` and
   `hyperlinear-nonsofic-via-ce-covariant-models`) are incompatible with all of these lanes at once.
   At most one side can succeed.
5. **The second covariant prerequisite collapses under the first.** Let QF be the statement "some
   essentially free pmp action of some countable group has a non-CE crossed product". Then
   `QF ⟺ NH ∨ ¬Q1`, where NH = `non-hyperlinear-group`. Also Q2 = `dense-full-subgroup-without-ce-covariant-model`
   implies QF. So, under Q1, QF is equivalent to NH, and every QF witness group is itself
   non-hyperlinear. The route `nonhyperlinear-via-full-subgroup-covariant-models` uses Q2 only through
   its consequence "`L^infinity(X) ⋊ Gamma_0` is not CE", which is a QF witness after Bernoulli
   padding. Its only content that is not circular is therefore the full-group structure (items 1--3
   of Q2). That structure has to produce a non-CE crossed product, and no route in the graph does this.

Scope. Item 3 does not extend to amenable kernels by this method. The countable reduction of an
amenable kernel lands in a subgroup of an unrestricted power `N^Lambda`, and countable subgroups of
products of amenable groups need not be amenable. Nothing here decides Q1. Items 1, 3 and 5 are
unconditional statements about implications.
