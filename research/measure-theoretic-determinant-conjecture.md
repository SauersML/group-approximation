---
rg: 2
id: measure-theoretic-determinant-conjecture
kind: claim
title: Every measured equivalence relation satisfies the Lück--Sauer--Wegner determinant bound over its integral groupoid ring
distinct_from:
  determinant-conjecture: that bounds determinants over integral group rings; this bounds them over the integral groupoid rings of all measured equivalence relations, which contain the group rings of free actions, so this implies that
  serre-class-from-unimodular-integral-realizability: that is the Serre-inequality form for unimodular integral networks; this is the literature conjecture in determinant form for relations, equivalent to it by the two routes between them
  determinant-conjecture-holds-for-sofic-groups: that is the proved sofic case over group rings; this is the open bound for every relation, whose proved sofic case is due to Elek--Lippner
artifacts:
  - research/artifacts/unimodular-networks-mdc-2026-09-12.md
---

**OPEN.** Conjectured by Lück, Sauer and Wegner (arXiv:0903.2925). The
statement and known cases were read from the TeX source (artifact Section 0).

**Statement.** Let `R` be a measured equivalence relation: a countable Borel
equivalence relation on a standard probability space `(X, mu)` with `mu`
invariant. Its integral groupoid ring `ZR` consists of the bounded Borel
functions `R -> Z` with uniformly finitely many nonzero entries in each row and
column, with the convolution product and trace `tr(f) = integral f(x,x) d mu`.
The conjecture is that `det_N(R)(A) >= 1` for every `A in M_(m x n)(ZR)`.

**Known cases (cited, read from source).**
- **Sofic relations** (Elek--Lippner, arXiv:0906.3619). These include treeable
  relations and Bernoulli shifts of sofic groups.
- **Group actions** (Lück--Sauer--Wegner):
  - essentially free actions of amenable groups;
  - the class of groups all of whose free actions satisfy MDC is closed under subgroups, amenable extensions, quotients by finite normal subgroups, and directed colimits;
  - Bernoulli actions of residually amenable groups.

**Place in the graph.**
- **Equivalent** to `serre-class-from-unimodular-integral-realizability`, by
  routes `mdc-via-unimodular-network-serre` and
  `unimodular-network-serre-via-mdc` (artifact Theorem 1). A labeled unimodular
  integral network is a measured relation carrying a self-adjoint element of
  `ZR`. Conversely, an element of `M_n(ZR)` is a unimodular integral network on
  orbits.
- **Implies** `determinant-conjecture`: for an essentially free action of `G`,
  `Z[G]` sits inside `ZR` with the same trace.
- **A counterexample must be nonsofic.** Main records a nonsofic relation,
  `non-ce-property-t-equivalence-relation-exists`: it is not Connes embeddable,
  hence not sofic by Elek--Lippner's embedding theorem. MDC for it is open.

## Attempts

- **Sofic approximation (covers sofic relations only).** This is Elek--Lippner's
  proof. Nonsofic relations exist, so approximation cannot be the whole proof.
- **Network form (equivalent, not weaker).** The Serre form for unimodular
  networks is the same statement, so moving to networks gains no leverage. It
  does isolate the missing input: mass transport together with integrality,
  with no finite approximants.
- **An integer-valued determinant, or integer moments (dead).**
  `unimodular-averaging-loses-determinant-integrality`: sofic integral networks
  have determinants `sqrt 5` and `4^p`, and root moments `5/2`. No Jensen-type
  or multiplicativity formula can force integrality; only the bound can hold.
- **A counterexample (not built).** The nonsofic relations on main come from
  property (T) envelopes of non-co-hyperlinear IRSs, and the nonsofic
  Aldous--Lyons networks are not explicit. None gives an element of `ZR` with a
  computable spectral measure.
