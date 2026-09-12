---
rg: 2
id: serre-class-from-unimodular-integral-realizability
kind: claim
title: Expected root spectral measures of unimodular integer-weighted networks obey every Serre inequality
distinct_from:
  integral-group-ring-spectra-are-integral-limits: that asks for integer-matrix approximation of group-ring spectra; this asks for the Serre inequalities themselves on the larger class of unimodular integral networks, with no approximation in the statement
  determinant-conjecture-iff-serre-class-spectra: that is the exact reformulation at one group; this is a network-level statement that implies it for every group at once
  root-measures-of-integer-matrices-can-violate-serre: that shows the inequalities fail at a single root without averaging; this asks whether unimodular averaging restores them in general
---

**OPEN.**

**Statement.** Let `(Gr, o)` be a unimodular random rooted network with integer
symmetric edge weights `w(u,v) in Z`, loops allowed, and weighted degree
`sum_v |w(u,v)| <= D` almost surely. Let `A` be its weighted adjacency operator
and `mu = E[ <E_A(.) delta_o, delta_o> ]` the expected root spectral measure.
Then for every nonzero `Q in Z[x]`,

```text
integral_(Q != 0) log|Q| d mu >= 0.
```

It is enough to treat `Q = x`. The operator `Q(A)` is again the adjacency
operator of a unimodular integral network on the same vertex set: its weights
are integer path sums of length at most `deg Q`, and its degree is bounded.

**Why it implies the determinant conjecture.** Take a self-adjoint
`A in M_n(Z[G])`.
- **Network:** vertex set `G x {1..n}`, weights `w((g,i),(h,j)) = A_ij(g^-1 h)`, root `(e,i)` with `i` uniform.
- **Hypotheses:** left translation by `G` preserves the network and acts transitively on each fibre, so the root distribution is unimodular by mass transport. The weights are integers and the degree is bounded.
- **Measure:** the expected root measure is `mu_A / n`.
With `determinant-conjecture-iff-serre-class-spectra` this gives `det >= 1` for
every group (route `determinant-via-unimodular-integral-networks`).

**Known case: sofic networks.** Suppose `(Gr, o)` is a Benjamini–Schramm limit of
finite integral networks with degree at most `D`.
- **Finite approximants:** the uniformly rooted root measure is the normalized trace
  measure of a finite symmetric integer matrix of norm at most `D`.
- **Limit:** `integral-spectral-limits-satisfy-serre-inequalities` then gives the
  claim at the limit.

**Equivalent form: the Lück--Sauer--Wegner conjecture.** This claim is
equivalent to `measure-theoretic-determinant-conjecture` (arXiv:0903.2925):
every measured equivalence relation `R` has `det_N(R)(A) >= 1` for every matrix
`A` over its integral groupoid ring `ZR`. See Theorem 1 of the artifact
`research/artifacts/unimodular-networks-mdc-2026-09-12.md`.
- **Network to relation** (route `unimodular-network-serre-via-mdc`).
  - i.i.d. uniform labels make the network rigid.
  - Mass transport is exactly what makes the root-moving relation on labeled
    rooted networks a measured equivalence relation.
  - The weights form a self-adjoint element of `ZR` whose spectral measure is `mu`.
- **Relation to network** (route `mdc-via-unimodular-network-serre`). A
  self-adjoint `B in M_n(ZR)` is a unimodular integral network on
  `orbit x {1..n}`, and its expected root measure is the spectral measure of
  `B`.

Elek--Lippner prove MDC for sofic relations (arXiv:0906.3619) by the same
approximation mechanism as the sofic case above. So a counterexample needs a
nonsofic relation.

## Attempts

- **Measure-level invariants of trace measures (dead).** Any invariant preserved by
  positive-preserving integer combinations admits `mu = 23 nu - sigma`
  (`euler-integral-measure-violates-serre-inequality`,
  `necklace-realizable-measures-can-violate-serre`). Such an invariant would prove too much.
- **Integral realizability at finitely many roots (dead).**
  `root-measures-of-integer-matrices-can-violate-serre`: integer coordinates
  without unimodular averaging admit Serre violators, even atomless ones. So a
  proof must use unimodularity, not only integrality.
- **Integral approximation (covers sofic networks only).**
  - It gives the sofic case above.
  - It cannot be the whole proof, because nonsofic unimodular networks exist:
    Bowen–Chapman–Lubotzky–Vidick refuted the Aldous–Lyons conjecture.
  - Cayley networks of nonsofic groups, such as `openai-leavitt-unit-nonsofic`, are not limits of finite networks.
- **A determinant built from mass transport (exists; the bound is open).**
  - The finite proof uses a global integer: the product of the nonzero
    eigenvalues of an integer matrix. An infinite network has no such object.
  - A mass-transport determinant does exist: the Fuglede--Kadison determinant
    of `N(R)` for the relation of the labeled network (route
    `unimodular-network-serre-via-mdc`). The bound `det >= 1` for it is exactly
    `measure-theoretic-determinant-conjecture`.
  - This determinant cannot be integer valued, so no Jensen-type or
    multiplicativity formula can force integrality. Sofic integral networks
    have determinants `sqrt 5` and `4^p`
    (`unimodular-averaging-loses-determinant-integrality`).
- **Integrality of necklace numbers under mass transport (dead).**
  - Root moments are averages over roots. A two-vertex network has
    `N_1 = 5/2` (`unimodular-averaging-loses-determinant-integrality`).
  - So the integer necklace numbers of
    `torsion-free-integral-zeta-is-an-integer-euler-product` have no network
    analogue. Mass transport equates averages but never makes them integers.
- **A nonsofic counterexample (not built).**
  - By Elek--Lippner and the equivalence above, a counterexample's labeled
    relation is nonsofic.
  - Main records a nonsofic relation,
    `non-ce-property-t-equivalence-relation-exists`. It is not Connes
    embeddable, hence not sofic by Elek--Lippner's embedding theorem.
  - But that relation is a property (T) envelope of a non-co-hyperlinear IRS,
    and none of its groupoid-ring elements has a computable spectral measure.
    The Bowen–Chapman–Lubotzky–Vidick networks are not explicit either.
