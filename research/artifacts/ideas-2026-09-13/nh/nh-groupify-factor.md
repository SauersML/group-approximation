# Idea lane nh-groupify-factor (2026-09-13)

Target: `non-hyperlinear-group`.  Lens: turn the MIP* = RE non-`R^U` object
into a model inside a group factor, i.e. attack the open hole
`non-ru-bcs-is-satisfiable-in-a-group-factor` (`A(B_*) -> p L(Lambda) p`).

**State of the lens on main.**  This region is dense.  The hole's Attempts
already fence:
- abelian and amenable hosts;
- monomial cocycle realisations over a normal subgroup;
- closure operations;
- free and Bernoulli envelopes, which are exact equivalences;
- Haar tags, which reduce to the cancellation kernel;
- inverse-semigroup globalization;
- finite-subgroup Hecke literals;
- common-corner unitary dilation;
- Bass--Serre algebraic projections;
- projectively closed symmetry bases.

Separate nodes fence:
- finite-phase Pauli dilations, which are twisted group-factor compilers;
- trace-functorial groupification;
- full-group subgroups.

Each approach below was checked against those nodes first.  Four die against
recorded fences or permanence theorems.  One is a weak restatement.  One uses
a host class that main does not cover (A6).  Nothing here is claimed
established.

## A1. Exact hosts as algebraic ultraproducts of approximate hosts: killed (new fence)

- **Idea.**  Take groups `Lambda_n` whose group factors carry better and
  better approximate models of `B_*`.  Pass to the algebraic ultraproduct
  `G = prod_U Lambda_n` and a countable subgroup `Lambda <= G` carrying an
  exact model in `L(Lambda)`.
- **Would prove.**  An exact group-factor model obtained from approximate
  ones, hence a nonhyperlinear `Lambda`.
- **Kill test.**  Locality of hyperlinearity.
- **Result (hand proof).**
  - Hyperlinearity of a countable group is decided on finite subsets: it only
    needs approximately multiplicative unitary maps on finite partial
    multiplication tables.
  - By Łoś's theorem, every finite subset of `Lambda`, with its partial
    multiplication table, occurs in `Lambda_n` for U-most `n`.
  - So if U-almost every `Lambda_n` is hyperlinear, `Lambda` is locally
    embeddable into hyperlinear groups, hence hyperlinear, so `L(Lambda)` is
    Connes embeddable and cannot host.
  - Countable subgroups of algebraic ultraproducts of finite groups are LEF,
    hence sofic, which is the special case.
- **Verdict.**  Killed.  Any limit construction of an exact host must already
  use nonhyperlinear `Lambda_n` on a U-large set, so the limit contributes
  nothing.  This fence does not appear on main as a node.

## A2. Locally finite nonabelian bases, the "noncommutative Pontryagin compiler": killed

- **Idea.**  Generalize `algebraic-compact-action-group-factor-compiler` from
  compact abelian duals to locally finite nonabelian `H`, such as Hall's
  universal locally finite group, with `Lambda` acting by automorphisms.
  - Then `L(H) rtimes Lambda = L(H rtimes Lambda)` with hyperfinite base.
  - The BCS involutions are placed as non-monomial elements, sums over
    `Lambda`, to dodge the monomial relocation Attempt.
- **Would prove.**  `H rtimes Lambda` is nonhyperlinear.
- **Kill tests and results.**
  1. **Free actors.**
     - `amenable-edge-graph-corners-cannot-groupify-a-nonce-game`
       (ESTABLISHED): fundamental groups of finite graphs of hyperlinear
       groups with amenable edge groups are hyperlinear.
     - `H rtimes F_n` is a multiple HNN extension of the amenable `H` over
       `H`, so no free actor ever hosts.
     - A web search summary of the Capraro--Lupini survey arXiv:1309.2034
       also states closure of hyperlinear groups under amalgamation over
       amenable subgroups.  I saw only the summary.
  2. **Monomial elements.**  Monomial realisations only relocate the non-CE
     trace to a normal subgroup (the hole's second Attempt).
  3. **Actors with relations.**  The base-level picture is exactly the
     recorded `finite-phase-pauli-dilation-is-twisted-group-factor-compiler`
     and the Kun--Thom Clifford crossed-product chain
     (`kun-thom-clifford-crossed-product-ce` =>
     `kun-thom-clifford-relative-wall` => `bare-relative-wall-exists`).
- **Verdict.**  Killed for free actors.  For actors with relations it
  duplicates recorded lanes.

## A3. The circle of multipliers of a Z-central extension: killed (duplicate)

- **Idea.**  For an integral cocycle `c` on `Gamma`, the twisted fibres
  `L_{exp(2 pi i t c)}(Gamma)`, `t in T`, disintegrate the group factor of the
  Z-central extension.
  - Connes-embeddable traces form a weak*-closed set, the closure of the
    matricial traces, so non-CE traces form an open set.
  - One non-CE fibre would therefore give an interval of non-CE fibres, hence
    a nonhyperlinear extension.
- **Kill test.**  Repository search.
- **Result.**  Already on main, and stronger:
  - `nonce-twisted-factor-gives-nonhyperlinear-group` makes a single non-CE
    twisted factor yield a nonhyperlinear central extension, with no openness
    needed;
  - `twisted-factor-existence-is-equivalent-to-nonhyperlinearity` makes the
    twisted root exactly equivalent to the goal;
  - `maslov-ce-parameter-set-is-a-closed-subgroup` already uses the closedness
    on the Maslov circle.
- **Verdict.**  Killed as a duplicate.

## A4. Orbit-sum algebras and association-scheme compilers: killed (restatement)

- **Idea.**  For a finite `K <= Aut(Lambda)`, the fixed-point algebra
  `L(Lambda)^K` has a hypergroup-like orbit-sum basis whose structure
  constants are orbit intersection counts.  Design `Lambda` so that the BCS
  projections are finite combinations of orbit sums, in the manner of a
  coherent configuration.
- **Would prove.**  `Lambda rtimes K` is nonhyperlinear.
- **Kill test.**  For finite `K`,
  `L(Lambda)^K ~= p_K L(Lambda rtimes K) p_K` with the averaging projection
  `p_K`.  This is the standard identification of fixed points with a corner
  of the crossed product; I did not re-derive it.
- **Result.**
  - This is a finite-subgroup Hecke corner.
  - Single literals fall under `finite-subgroup-hecke-literals-cannot-block-escape`.
  - Finite-support non-literal models are exactly the `(AEG2)`-type maps
    `B -> qQ[Pi]q`. These are excluded for amenable-edge graphs, and stably
    vertex-induced for graphs of finite groups by
    `bass-serre-algebraic-projections-are-stably-vertex-induced`.
- **Verdict.**  Killed as a restatement.  The combinatorial structure
  constants add no mechanism beyond the recorded frame.

## A5. Cartan-transverse group subalgebras of the non-CE relation factor: unclear (weak)

- **Idea.**  Take the non-CE relation factor `L(R)` of
  `non-ce-property-t-equivalence-relation-exists` and an essentially free
  countable `Lambda <= [R]`.  Then `L(Lambda) -> L(R)` is trace-preserving.
  Ask only that the subalgebra `W*(Lambda)` be non-CE, not that it be all of
  `L(R)`.
- **Would prove.**  `Lambda` is nonhyperlinear.
- **Kill tests.**
  - `full-group-subgroup-trace-generation-dichotomy`: non-free `Lambda` has
    the wrong trace; free `Lambda` has image meeting the Cartan only in
    scalars, so never all of `L(R)`.
  - `non-ce-relation-is-not-treeable`: `R` is not generated by free-group
    actions.
- **Result.**  The dichotomy fences only the whole-algebra version.  The
  subalgebra version is not excluded, but nothing forces non-CE-ness into a
  Cartan-transverse group subalgebra, and `Lambda` cannot be free.
- **Verdict.**  Unclear, weak: it is the hole with the host restricted to
  full-group subgroups.

## A6. Hecke-pair lattice transfer from totally disconnected groups: unclear (best survivor)

- **Idea.**  Replace discrete hosts by a unimodular totally disconnected
  locally compact group `G` with a compact open subgroup `K` and a cocompact
  lattice `Gamma`.
  1. Put the BCS model into the Hecke von Neumann algebra `p_K L(G) p_K`,
     with the BCS projections given as finite combinations of double-coset
     indicators `1_{KgK}`.
  2. Transfer to the lattice.  `L(G)` sits inside `L^infty(G/Gamma) rtimes G`.
     By imprimitivity that crossed product is `L(Gamma) (x) B(L^2(G/Gamma))`.
     At the C*-level, `C_0(G/H) rtimes G ~= C^*(H) (x) K` is Green's
     imprimitivity theorem, as summarized from Williams' crossed-product
     book (search summary only); the von Neumann version with the trace match
     is not re-derived.
  3. The canonical trace restricts to covolume times the Plancherel weight,
     and `p_K` has finite weight.  So the model lies in a finite corner of
     `L(Gamma) (x) B(H)`, and `Gamma` is nonhyperlinear.
- **Would prove.**  A nonhyperlinear lattice.
- **Why it is not a duplicate.**  The recorded Hecke fences concern finite
  subgroups of discrete groups.  A compact open `K` in a non-discrete `G` is
  not covered.  Grepping main for imprimitivity or Schlichting finds only the
  far-defect formula proofs and imprimitivity artifacts, not this transfer.
- **Kill tests and results.**
  1. **Trees.**  By the same transfer read backwards, every Hecke algebra of a
     closed subgroup of `Aut(T)` with a uniform lattice is CE.  Uniform tree
     lattices are virtually free, hence hyperlinear.  So single trees are
     killed.
  2. **Amenable `G`.**  Gives CE, so killed.
  3. **Products of trees and buildings.**  The irreducible lattices
     (Burger--Mozes, Radu) have open hyperlinearity; main's
     `radu-bmw-lattice-sofic` root is open.  No transfer obstruction is
     known there.
  4. **The transfer itself.**  It needs the von Neumann imprimitivity
     isomorphism with the trace match, which is standard but not checked
     against a source here.
- **Verdict.**  Unclear, and the best survivor of this lane.
  - **Concrete hosts:** closed subgroups of `Aut(T_1) x Aut(T_2)` with
    irreducible lattices, or Kac--Moody groups over finite fields.
  - **What is needed:** a Hecke-level BCS model built from double-coset
    combinatorics of the building.
  - **Next tests:** pin the von Neumann imprimitivity statement against a
    source.  Then compute the smallest Hecke algebras of a Burger--Mozes
    product with small local actions, and test whether they can carry
    anticommuting projection pairs across contexts.

## Summary

| # | Approach | Verdict |
|---|---|---|
| A1 | algebraic ultraproduct hosts | killed (new locality fence) |
| A2 | locally finite nonabelian bases | killed (free actors), duplicate (with relations) |
| A3 | circle of multipliers | killed (duplicate) |
| A4 | orbit-sum / association-scheme algebras | killed (restatement) |
| A5 | Cartan-transverse full-group subalgebras | unclear, weak |
| A6 | Hecke-pair lattice transfer | unclear, best survivor |

Sources consulted in this lane:
- repository nodes named above, read at origin/main;
- search summaries of [arXiv:1309.2034](https://arxiv.org/pdf/1309.2034) and
  [Williams, Crossed Products of C*-Algebras (draft)](https://math.dartmouth.edu/~dana/cpcsa/draft-31Jan06.pdf);
- [arXiv:math/0509291](https://arxiv.org/pdf/math/0509291) (Hecke algebra
  imprimitivity; title and summary only).
