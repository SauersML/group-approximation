---
rg: 2
id: stw99-problem-xci-cstar-simple-selfless
kind: claim
title: The reduced C*-algebra of every C*-simple group is selfless (STW Problem XCI)
root: true
distinct_from:
  stw99-problem-xc-cstar-simple-strict-comparison: that asks for strict comparison; this asks for Robert's selflessness, which implies strict comparison (Robert, Theorem 3.1) and is the refinement STW record as Problem XCI.
artifacts:
  - research/artifacts/stw91-graph-component-selflessness-audit-2026-08-30.md
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
  - research/artifacts/stw91-cograph-product-permanence-audit-2026-08-30.md
  - research/artifacts/stw91-finitary-permutation-wreath-audit-2026-08-30.md
  - research/artifacts/stw91-anchored-free-product-permanence-audit-2026-08-30.md
  - research/artifacts/stw91-php-crossed-product-selflessness-audit-2026-08-30.md
  - research/artifacts/fkop-graph-product-selflessness-v3-audit-2026-08-30.md
  - research/artifacts/stw91-locally-finite-permutation-wreath-audit-2026-08-30.md
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
  - research/artifacts/stw91-universal-vertex-absorption-audit-2026-08-30.md
  - research/artifacts/stw91-complete-graph-anchor-audit-2026-08-30.md
---

**Problem XCI of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026)** (Robert).  Is `C*_r(F₂)` selfless?  If `G` is a
countable discrete C\*-simple group, is `C*_r(G)` selfless?

Selflessness (Robert, *Selfless C\*-algebras*, Definition 2.1): `(A, τ)` is
selfless when `A != C`, `τ` has faithful GNS representation, and the
first-factor embedding

```text
i_1:(A,τ) -> (A,τ) * (A,τ)
```

is existential.  Equivalently, for some ultrafilter `ω` there is a
trace-preserving embedding `σ:(A,τ)*(A,τ) -> (A^ω,τ^ω)` with
`σ i_1=Δ_A`; Robert's Theorem 2.6 gives the analogous equivalent formulation
with the infinite reduced free product.  Thus the splitting map runs **from
the free product to the ultrapower**, not conversely.  Selfless tracial
algebras are simple, have stable rank one and strict comparison, and their
trace is the unique trace and unique normalized 2-quasitrace (Robert,
Theorem 3.1).

Gould, arXiv:2606.09654v2, Theorem 2 and Corollary 3, completes the structural
dichotomy beyond the tracial setting: every selfless C-star algebra is pure;
a selfless probability space is simple, with the stable-rank-one package in
the tracial case and pure infiniteness in the nontracial case.  Theorem 2.5
settles the formerly missing nonfaithful-state case by proving pure
infiniteness and simplicity.  This is recorded as
`gould-selfless-dichotomy-and-purity`; it gives consequences of selflessness
and does not prove the universal group assertion in XCI.

The first part is solved: `C*_r(F_n)` is selfless for `n ≥ 2`
(Amrutam--Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2412.06031, published
in *Inventiones* 242 (2025)).  The universal C\*-simple-group question remains
open as of 30 August 2026.  Subsequent primary-source advances include
Ozawa's topologically-free extreme-boundary/PHP criterion
(arXiv:2508.07938), Vigdorovich's theorem for all nontrivial linear groups
with trivial amenable radical (arXiv:2602.10616v3), and the relative
selflessness machinery of Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert
(arXiv:2607.20361); none asserts the universal statement above.

## Attempts

- `stw91-directed-unions-of-selfless-groups` proves a local-to-global
  permanence principle and supplies new positive examples.
- `stw91-countable-free-direct-sum-is-selfless` applies it to the countable
  restricted direct sum of `F_2`, then proves this group is neither linear nor
  acylindrically hyperbolic.
- `stw91-zero-dimensional-step-amplification-preserves-selflessness` proves
  that every exact selfless group remains selfless after amplification to
  locally constant functions on any compact metrizable zero-dimensional
  space.  The proof iterates exact tensor permanence over finite clopen
  partitions and then passes to their directed union.
- `stw91-reduced-free-products-preserve-selflessness` proves that the reduced
  free product of any two selfless C*-probability spaces is selfless, without
  exactness.  It places the two factor splittings in a common Fubini
  ultrapower, verifies freeness of the factor ultrapowers, and regroups the
  resulting four free copies.  Hence free products of groups already known
  to satisfy XCI again satisfy XCI.
- `stw91-anchored-arbitrary-free-products-are-selfless` needs only one
  selfless factor: an arbitrary reduced free product is selfless when every
  other factor is separable with faithful-GNS state.  It iterates Robert's
  one-selfless-factor binary theorem over finite packets and then applies his
  directed-union theorem.  Thus a countable free product of countable groups
  satisfies XCI as soon as one free factor does, with no hypothesis on the
  remaining groups.
- `stw91-php-approximately-inner-crossed-products-are-selfless` combines the
  2026 relative crossed-product theorem with unique-trace scalarization.  If
  a PHP group acts by approximately inner automorphisms on a simple unital
  uniquely tracial algebra, then the reduced crossed product is tracially
  selfless and has Robert's full regularity package.  In particular, this
  holds for every action of a PHP group on the Jiang--Su algebra.
- `stw91-cograph-products-preserve-selflessness` combines reduced-free-product
  permanence with exact tensor permanence and directed unions.  If a
  countable commutation graph has no induced `P_4` and every vertex group has
  exact selfless reduced algebra, then its graph product has exact selfless
  reduced algebra.  Finite cographs recursively alternate disjoint
  union/free product and join/direct product; countable graphs are exhausted
  by finite induced cographs.  General graph products remain outside this
  argument because vertex removal introduces amalgamation over link
  subgroups.
- `graph-products-connected-complement-are-selfless` imports the final August
  2026 theorem of Flores--Klisse--O Cobhthaigh--Pagliero.  A countable graph
  with at least three vertices and connected complement, with arbitrary
  nontrivial countable vertex groups, has completely selfless reduced group
  algebra.  This uses neither exactness nor prior selflessness of the vertex
  algebras.
- `stw91-finitary-permutation-wreaths-are-selfless` proves that
  `P^(X) rtimes L` is selfless whenever `P` is a nontrivial countable linear
  C*-simple group, `X` is countably infinite, and
  `L <= Sym_fin(X)`.  Each finite semidirect packet is linear, and a direct
  support argument proves that its amenable radical is trivial before
  Vigdorovich's theorem is applied.  The full wreath is a directed union, yet
  it is nonlinear over every field and not acylindrically hyperbolic.
- `stw91-locally-finite-permutation-wreaths-are-selfless` removes the
  finite-support hypothesis on the top action.  Every finite subgroup of a
  faithful permutation group has a finite invariant faithful witness set;
  these sets produce the same radical-free linear packets and form a
  directed exhaustion.  Thus `P^(X) rtimes L` is selfless for every
  countable locally finite `L <= Sym(X)`.  In particular, regular wreath
  products by infinite locally finite groups are covered even though every
  nontrivial top element has infinite support.
- `stw91-finite-subgroup-projection-obstruction` gives a concrete negative
  certificate in ordered `K_0` using averaging projections of finite
  subgroups.

- `graph-products-no-universal-vertex-selfless-criterion` gives an exact
  solution for graph products with no universal vertex: C-star-simplicity is
  equivalent to selflessness, and the sole obstruction is a two-vertex
  complement component labelled by `C_2,C_2`.  For C-star-simple vertex
  groups the resulting algebra is completely selfless, with no exactness or
  prior vertex-selflessness assumption.

- `graph-products-noncomplete-selfless-criterion` settles every graph-product instance whose defining graph is noncomplete, including graphs with arbitrarily many universal vertices labelled by arbitrary C-star-simple groups. One nonsingleton complement component supplies a completely selfless tensor anchor that absorbs the entire remaining C-star-simple factor without exactness. The complete-graph case is the exact residual boundary; a one-vertex complete graph is the universal problem itself.

- `complete-graph-products-selfless-anchor` settles the complementary complete-graph class whenever one vertex reduced algebra is completely selfless: the other countably many vertex groups may be arbitrary C-star-simple groups, even nonexact. For finite complete graphs with all vertex factors completely selfless, the product is completely selfless. The anchor hypothesis is not automatic and therefore does not close the universal root.

- `paired-selflessness-witnesses-do-not-tensor` gives an exact fourth-moment obstruction to the naive tensoring of two ordinary selflessness witnesses. The paired copies contain crossed-coordinate centered elements whose alternating fourth moment is strictly positive, so separate free-product splittings do not become a splitting for the tensor product. This does not refute tensor permanence; it isolates the need for a genuinely entangling or completely selfless construction.
