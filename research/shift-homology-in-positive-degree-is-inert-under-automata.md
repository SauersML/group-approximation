---
rg: 2
id: shift-homology-in-positive-degree-is-inert-under-automata
kind: claim
title: Every automaton acts as the identity on positive-degree rational group homology with full-shift coefficients, unlike the strict BS(1,2) coset-shift automaton
distinct_from:
  measure-conjugacy-invariants-cannot-certify-surjectivity: that shows conjugacy invariants of the measured shift cannot separate strict from bijective automata; this computes the automaton pullback on equivariant homology of the coefficient module and shows it is the identity in positive degree for every automaton.
  surjunctivity-iff-automaton-monoid-directly-finite: that reformulates surjunctivity as direct finiteness of the automaton monoid; this kills one family of Hopfian sizes, functorial group homology of the shift coefficient module.
  site-pullbacks-strict-iff-stabilizer-self-compressed: that characterizes when coset site pullbacks are strict; this measures such a strict pullback on group homology, where it acts by the compression index.
  end-fixing-tree-symmetries-carry-strict-automata: that builds a strict automaton on a tree over a non-unimodular locally compact group; this uses its discrete coset-shift form as a calibration for homological invariants.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the measure-preservation statement equivalent to the goal; this shows the degree-zero part of the homological approach reduces to it and the positive-degree part is blind.
  injective-measure-preserving-ca-is-surjective: that is the elementary full-support argument; this is an inertness theorem for homology with shift coefficients, reusing that argument only in the degree-zero remark.
artifacts:
  - research/artifacts/shift-homology-inertness-and-coset-calibration-2026-09-17.md
  - experiments/cohopfian-shift-homology-2026-09-17/check.py
---

**ESTABLISHED 2026-09-17** by [[shift-homology-in-positive-degree-is-inert-under-automata-proof]].

Let `G` be a group and `A`, `B` finite alphabets. Let `C(X, R)` be the `G`-module of
continuous `R`-valued functions on `X` with `(g f)(x) = f(g^-1 x)`.

1. **Inertness.** For `n >= 1`, the inclusion of constants `Q -> C(A^G, Q)` induces an
   isomorphism on `H_n(G; -)`. It does so over `Z` when `G` is torsion-free. So every
   automaton `tau : A^G -> B^G` induces the canonical identification
   `tau^* : H_n(G; C(B^G,Q)) -> H_n(G; C(A^G,Q))`. In particular every self-automaton,
   strict or not, acts as the identity there. The same holds for every map
   `Y × A^G -> Y × A^G` over `id_Y`, for a compact totally disconnected `G`-space `Y`. This
   includes the strict hotel maps of `nonamenable-groups-carry-arrow-shift-strict-automata`.
2. **Calibration.** Let `G = BS(1,2) = Z[1/2] x| Z`, `K = <a>`, `V = G/K` (the tree `T_3`),
   and `p(gK) = g t^-1 K`. The strict parent-copy automaton `tau(x)(v) = x(p(v))` on
   `{0,1}^V` acts on the summand `H_1(G; Q[V]) = H_1(K; Q) = Q` of `H_1(G; C({0,1}^V, Q))`
   as multiplication by `2 = [G_{p(v)} : G_v]`.

## What this kills

Co-Hopfian ("full shifts admit no proper self-embedding") proofs through a functorial size built
from `H_*(G; C(A^G, Z))` are dead as a family.
- **Positive rational degree.** The size is constant on all automaton maps over groups.
  - It dies at the step "constants include isomorphically". That step uses finiteness of
    setwise stabilizers of finite site sets, which makes the permutation module of patterns
    projective.
  - The calibration shows this is exactly the step that fails on a coset shift. There the size
    moves by the compression index.
- **Degree 0.** The coinvariants carry the unit, the cone and the Bernoulli trace, and `tau^*`
  kills every Garden-of-Eden cylinder class.
  - A state compatible with `tau^*` is precisely a `G`-invariant, `tau`-invariant probability
    measure.
  - So this degree reduces to `every-injective-ca-preserves-uniform-bernoulli-measure` through
    `injective-measure-preserving-ca-is-surjective`.
  - For `G = F_n`, Pimsner–Voiculescu identifies `K_0` and `K_1` of `C(A^G) x| F_n` with
    `H_0` and `H_1`, so the crossed-product `K`-class candidate falls under the same verdict.
    This is a remark, not a prerequisite.
- **Type-semigroup class of the one-site partition.** It is not a conjugacy invariant.
  - Over any nontrivial group, the marker involution `x(g) -> swap_{1,2} x(g)` when `x(gs) = 0`
    moves the site marginal of a Bernoulli measure from `(1/2,1/2,0)` to `(1/2,1/4,1/4)`.
  - The strict calibration automaton fixes every one-site class.

## Attempts

- **Surviving candidate.** Cohomology `H^1(G; C(A^G, Z))`, which is end or boundary data, is
  not covered by the inertness proof. It is recorded as a spark: it would still need a
  Hopficity principle.
- **Integral torsion.** For groups with torsion, integral torsion in positive degree sits in
  `⊕ H_n(G_{F,c}; Z)` over finite pattern stabilizers. Its automaton action was not computed.
