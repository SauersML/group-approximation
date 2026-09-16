---
rg: 2
id: semidirect-seed-radical-is-ce-dual-measure-test
kind: claim
title: A module element escapes the hyperlinear radical iff some invariant dual measure seeing it has a Connes-embeddable crossed product
distinct_from:
  algebraic-envelope-principle: that uses the Haar measure on the dual, where the crossed product is the group factor itself; this allows every invariant dual measure and tests one module element at a time.
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: that computes the sofic radical of one explicit wreath pair; this is a general criterion for hyperlinear-radical membership of module elements in abelian-by-hyperlinear semidirect products.
  hyperlinear-radical-presentation-compactness: that characterizes radical membership through finite relator windows; this characterizes it through invariant measures and Connes embeddability of commutative crossed products.
  measure-full-group-subgroups-hyperlinear-if-crossed-product-ce: that transfers Connes embeddability of a Cantor crossed product to topological full groups; this identifies the hyperlinear radical of a semidirect product with a dual-measure condition.
  algebraic-compact-action-group-factor-compiler: that compiles a non-CE subalgebra of a Haar crossed product into a non-hyperlinear semidirect product; this is an elementwise equivalence over arbitrary invariant dual measures, and its converse direction constructs the measure from a matrix model.
artifacts:
  - research/artifacts/seed-radical-transfer-2026-09-16.md
---

**ESTABLISHED** by route `semidirect-seed-radical-dual-measure-proof`. No novelty is claimed. The ingredients
are standard Gelfand, Riesz, GNS and ultraproduct arguments, and no published source for this exact statement
was located.

Let `M` be a countable abelian group and `A` a countable group acting on it, `G = M rtimes A`, and `m_0 in M`. Let
`A` act on the dual `M^` by `(a.chi)(m) = chi(a^(-1).m)`. For an `A`-invariant Borel probability measure `nu` on
`M^`, put `N_nu = L^infinity(M^, nu) rtimes A` and `S_0 = {chi : chi(m_0) != 1}`.

**Theorem.**

- **(B1)** If some `A`-invariant `nu` has `nu(S_0) > 0` and `N_nu` Connes embeddable, then `m_0 notin Rad_hyp(G)`.
  In this case `A` is hyperlinear.
- **(B2)** If `A` is hyperlinear and `m_0 notin Rad_hyp(G)`, such a `nu` exists.

So for hyperlinear `A`:

```text
m_0 in Rad_hyp(M rtimes A)
  iff
every A-invariant probability measure on M^ with Connes-embeddable crossed product
is carried by the annihilator {chi : chi(m_0) = 1}.
```

The measure in (B2) is the spectral measure of `tau o theta|_M` for a homomorphism `theta` not killing `m_0`.
Tensoring with a regular-trace representation of `A` makes the trace of `theta(m,a)` equal to
`delta_(a,1) int chi(m) d nu`, which is the trace of `e_m u_a` in `N_nu`. The GNS construction then embeds `N_nu`.

No freeness, ergodicity or soficity of the dual action is used.
