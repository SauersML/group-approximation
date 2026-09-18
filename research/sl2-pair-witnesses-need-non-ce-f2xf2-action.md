---
rg: 2
id: sl2-pair-witnesses-need-non-ce-f2xf2-action
kind: claim
title: If every p.m.p. action of F2 x F2 has a Connes-embeddable crossed product, every pair-transfer group over a subgroup of SL2(Z[1/p]) is hyperlinear
distinct_from:
  tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce: that makes lattices in products of trees hyperlinear under the same hypothesis; this moves the hypothesis along a measure-equivalence coupling to the non-lattice arithmetic host SL2(Z[1/p]), and then through the coset Bernoulli wreath to the HNN groups, doubles and relative embeddings of all its subgroup pairs.
  dyadic-bruhat-tits-vertex-action-is-sofic: that is soficity of one vertex action, reached from f2xf2-in-paunescu-class along the same coupling; this moves Connes embeddability of all crossed products and ends at hyperlinearity of pair-transfer groups, which soficity of one action does not give.
  paunescu-class-is-measure-equivalence-invariant: that is measure-equivalence invariance of Paunescu's sofic class; item 1 here is the Connes-embeddable analogue, proved by a corner argument across the stable orbit equivalence.
  sl2-half-stability-excludes-hnn-hyperlinearity: that is the dichotomy between non-hyperlinearity of G_2 and failure of flexible stability; this says the first horn forces a non-CE crossed product of F2 x F2.
  arithmetic-pair-is-not-relatively-embeddable: that asks for non-relative-embeddability of the arithmetic pairs; this shows the SL2 half would give F2 x F2 a non-CE action.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that notes that a CE coset Bernoulli crossed product refutes commutant collapse; this derives that Connes embeddability from a hypothesis about F2 x F2 alone.
  binary-free-and-ordinary-coset-wreaths-share-hyperlinearity: that is the seven-way equivalence for one pair; this supplies item 3 of it for every pair inside a host measure equivalent to F2 x F2.
  f2xf2-crossed-products-are-connes-embeddable: that is the open hypothesis; this is the implication from it.
---

**ESTABLISHED (unreviewed).** Let `𝒜` be the class of countable groups `Γ` such that
`L^∞(X, μ) ⋊ Γ` is Connes embeddable (CE) for every p.m.p. action `Γ ↷ (X, μ)`.

1. **Measure-equivalence invariance.** `𝒜` is closed under subgroups and under measure
   equivalence.
2. **Arithmetic hosts.** For a finite nonempty set `S` of primes, `SL_2(Z[1/S])` is measure
   equivalent to `F_2^(|S|+1)`, so `SL_2(Z[1/S]) ∈ 𝒜` iff `F_2^(|S|+1) ∈ 𝒜`.
3. **Pair transfer.** If `F_2^(|S|+1) ∈ 𝒜`, then for every subgroup `C <= A = SL_2(Z[1/S])` all
   seven equivalent statements of `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`
   hold:
   - `(⊕_(A/C) C_2) ⋊ A`, `A *_C (C × C_2)`, `A *_C A`, `A *_C (C × Z)` and
     `(A × Z) *_C A` are hyperlinear;
   - `L(C) ⊂ L(A)` is relatively embeddable over the scalars.

**The class this kills.** Read contrapositively, and applied through the dichotomies already in
the graph, item 3 gives the following.

- **(K1)** If `G_2 = <SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1>` is not hyperlinear, then some essentially
  free p.m.p. action of `F_2 × F_2` has a non-CE crossed product.
- **(K2)** By `sl2-half-stability-excludes-hnn-hyperlinearity`, if `SL_2(Z[1/2])` is flexibly
  HS-stable (`iwahori-local-global-defect-question`), then `F_2 × F_2 ∉ 𝒜`. The same holds for the
  SL2 half of `arithmetic-pair-is-not-relatively-embeddable`.
- **(K3)** For `(SL_2(Z[1/pq]), SL_2(Z[1/p]))` in `non-hyperlinear-from-hnn-over-codense-kazhdan`,
  flexible stability of `SL_2(Z[1/pq])` gives `F_2^3 ∉ 𝒜`.
- **(K4)** Every current route to `non-hyperlinear-group` whose witness is a pair-transfer group
  over a subgroup pair of `SL_2(Z[1/S])` therefore produces, when it closes, a non-CE crossed
  product of a finite product of free groups. That covers:
  - `non-hyperlinear-from-hnn-over-sl2-z`
  - `non-hyperlinear-from-sl2-amalgamated-free-exclusion`
  - `non-hyperlinear-from-exact-quasi-regular-leak`
  - `non-hyperlinear-from-relative-commutant-collapse`
  - `nonhyperlinear-coset-wreath-from-commutant-collapse`
  - `non-hyperlinear-from-iwahori-unitary-commutant-transfer`
  - `nonhyperlinear-from-canonical-iwahori-projection-transfer`
  - the `SL_2(Z[1/pq])` instance of `non-hyperlinear-from-hnn-over-codense-kazhdan`

  Conversely, if `f2xf2-crossed-products-are-connes-embeddable` holds (together with its
  `F_2^k` versions), each of these routes has a false prerequisite.

**Invariant and failing step.**
- **Invariant.** The invariant is membership of the host's measure-equivalence class in `𝒜`. It
  does not see congruence structure, the `(τ)` gap, Iwahori defects, or co-density: `F_2 × F_2`
  has none of these, and it is Haagerup.
- **Failing step.** Every member of the class fails at the step that turns stability or
  commutant collapse into non-existence of canonical microstates for the witness. That step is
  at least as strong as showing that one explicit action has a non-CE crossed product. The action
  is the essentially free action of `F_3 × Π_p F_(r_p)` on `X_Z ≅ D_H × {±1}^(A/C) × B` from
  Step 3 of the proof route, induced up to `F_2^(|S|+1)`.

**What escapes.**
- Property (T) is a measure-equivalence invariant (Furman), and products of free groups do not
  have it. So hosts with (T) are not covered: the `SL_3(Z[1/2])` half of the arithmetic pair,
  Kun–Thom pairs, Leavitt and Kac–Moody lattices.
- The obstruction also says nothing about witnesses that are not pair-transfer groups over a
  rank-one `S`-arithmetic host, for example central extensions of hyperbolic Kazhdan groups.

Proof: `sl2-pair-witnesses-need-non-ce-f2xf2-action-proof`.

## Heretic reading

The HOT SL2 families share three unstated assumptions.

- **H1: rigidity of the host is the source of non-approximability.**
  - Denial: replace the arithmetic host by anything in its measure-equivalence class.
  - Result: the denial does not die. It is this node. The approximation content of every
    pair-transfer witness over `SL_2(Z[1/S])` is already a statement about crossed products of
    `F_2^(|S|+1)`, where the arithmetic structure is invisible.
  - Consequence for prioritization: an SL2 route is no cheaper than a non-CE action of a product
    of free groups. Hosts with (T) are the only arithmetic hosts not reduced this way.
- **H2: certification is universal over microstates of the regular trace.**
  - Denial: certify against a restricted or externally generated family of traces.
  - Where it dies: at the idempotent / Diracization gap for external MIP* traces, and at marked
    closedness for limit and generic constructions.
- **H3: the witness is tested through its own regular trace, with transfer along trace-preserving
  inclusions.**
  - Denial: embed non-trace-preservingly into `U(M)` with a generic `t ∈ U(π(C)' ∩ M)`.
  - Where it dies: relative commutants in free crossed products with `C` ergodic are trivial, and
    the free Bernoulli model is circular.
  - Pushing this denial led to the Bernoulli coupling argument here.
