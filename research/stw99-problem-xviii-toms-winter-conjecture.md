---
rg: 2
id: stw99-problem-xviii-toms-winter-conjecture
kind: claim
title: Strict comparison forces Jiang--Su stability (STW Problem XVIII, Toms--Winter)
root: true
refuted_by: [stw18-strict-comparison-non-z-stable-algebra-exists]
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that asks whether every stably finite algebra in the class has uniform property Gamma; uniform Gamma together with strict comparison is a sufficient route to this problem, but the two assertions are not equivalent.
  stw99-problem-xxv-unique-trace-sr1-z-stable: that assumes unique trace and stable rank one instead of strict comparison.
  stw99-problem-xxvi-cu-regularity-z-stability: that assumes Jiang--Su absorption at the level of the Cuntz semigroup, a stronger regularity input than strict comparison alone.
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

**Problem XVIII of Schafhauser--Tikuisis--White, _Nuclear C*-algebras:
99 problems_, arXiv:2506.10902.**  Let `A` be a simple, separable, nuclear,
non-elementary C*-algebra with strict comparison.  Must

```text
A ~= A tensor Z?
```

This is the remaining strict-comparison-to-Jiang--Su-stability direction of
the Toms--Winter conjecture.  It remains open in this generality.

## Attempts and established boundaries

- The converse implications are known: Jiang--Su stability gives finite
  nuclear dimension in the simple nuclear setting, and Jiang--Su stability
  gives strict comparison.
- In the unital stably finite case, strict comparison together with uniform
  property Gamma implies Jiang--Su stability.  Toms's 2026 counterexample to
  universal uniform Gamma therefore closes that proposed universal
  intermediate statement, not Problem XVIII itself.
- The compact finite-dimensional tracial-boundary cell is explicitly closed
  by `stw18-finite-trace-boundary-toms-winter`,
  which imports the Toms--White--Winter theorem.  This includes finitely many
  extremal traces and the unique-trace case.  Other known subclasses include
  AH algebras and crossed products of free minimal `Z^d`-actions in the cited
  STW survey.
- `stw99-xviii-implies-xxvi` records the exact conditional implication from a
  positive solution here to Winter's Cuntz-semigroup problem XXVI.
- Unital simple AH algebras and Lin's condition (C) tracial strata are
  closed positively: `simple-ah-strict-comparison-is-z-stable` and
  `lin-condition-c-boundary-strict-comparison-z-stable`.
- **K1 route to a counterexample (2026-09-11).** The negation root is
  `stw18-strict-comparison-non-z-stable-algebra-exists`. A strict-comparison
  algebra that is not K1-injective would refute this problem (Jiang). The
  LIX algebras fail strict comparison
  (`stw59-lix-algebras-fail-strict-comparison`), and every AH upgrade is dead.
  `stw18-k1-witness-constraints` shows any witness has stable rank at least
  two, a rank gap refuting Problem XXIII, no pureness, and a trace simplex
  outside condition (C). See
  `research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md`.
- **Dimension threshold for Bauer witnesses (2026-09-17, proposed established).**
  - `rsh-multiplicity-count-sharp-rigidity-threshold`: a Bauer strict-comparison
    counterexample with rigidity level `ε_0` has, in every unital RSH subalgebra, a block with
    `ε_0 n < √(d+2)`. The source is von Neumann–Wigner codimension `k² − 1` plus relative general
    position.
  - A unital simple exact Bauer strict-comparison algebra with unital RSH subalgebras of arbitrarily small `√(d+2)/n` has a divisible unit
    and is pure. For ASH limits it is `Z`-stable.
  - At `d = k² − 1` the only certificates are `n`-primary torsion classes of projective bundles.
    They vanish on `End(E)` blocks, and the bound is sharp on the Moore-space `SO(3)`-bundle and
    on the Pauli tower. Tensored with `M_t`, the Pauli tower is `1/t`-rigid at the threshold, so
    the inequality is attained at every level `1/t`.
  - Linear-growth designs die at the first finite stage.
