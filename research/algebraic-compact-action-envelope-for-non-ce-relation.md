---
rg: 2
id: algebraic-compact-action-envelope-for-non-ce-relation
kind: claim
title: Embed the explicit non-CE relation factor in an effective compact-abelian algebraic crossed product
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that supplies the Manzoor relation factor inside another property-T relation factor; this requires the target relation to come from a compact-abelian algebraic action so its crossed product is a canonical semidirect-product group factor.
  perfect-zpc-irs-quantum-gap-game: that strengthens a game-value separation inside a restricted IRS strategy class; this asks for a trace-preserving von Neumann embedding into one Haar algebraic process and uses no finite-dimensional robust decoder.
---

For the explicit non-Connes-embeddable relation factor `N` supplied by
`non-ce-property-t-equivalence-relation-exists`, construct:

- a compact second-countable abelian group `K`;
- an effectively presented finitely generated group `Lambda` acting on `K`
  by continuous automorphisms; and
- a trace-preserving embedding

```text
N -> L^infinity(K) rtimes Lambda,                       (ACAE1)
```

such that `K-hat rtimes Lambda` is finitely generated and recursively
presented.  A preferred concrete form is a Haar linear subshift

```text
K <= (F_p^m)^Lambda
```

defined by effective finite-type or recursively enumerable linear local
constraints.  Then `algebraic-compact-action-group-factor-compiler` produces
a non-hyperlinear group, and Higman produces a finitely presented one.

The inclusion in `(ACAE1)` is essential: a non-CE quotient of an embeddable
crossed product gives no contradiction because Connes embeddability is not
known to pass to arbitrary quotients.

## Attempts

- **Haar is load-bearing.** An arbitrary shift-invariant measure does not
  Fourier-transform to a group von Neumann algebra.  The witness process must
  be linear-algebraic enough that the invariant measure is Haar.
- **Relation envelope is not yet algebraic.** The
  Chifan--Drimbe--Ioana/Manzoor property-T relation envelope gives an inclusion
  into a relation factor but does not provide a compact abelian base or an
  algebraic action.  No consequence for a discrete group follows until this
  extra structure is installed.
- **ZPC/LCS opportunity and risk.** Finite-field constraints naturally define
  closed linear subshifts, avoiding the current robust groupification decoder.
  The unresolved step is to embed the non-CE GNS/relation algebra, not merely
  reproduce its scalar correlations.  Fourier-positivity identities of Haar
  algebraic processes give an early falsification test for each candidate
  game witness.
- **Finite cocycles allowed.** If the natural Pauli/LCS envelope is twisted by
  a finite scalar cocycle, `thom-central-corner-criterion` converts the
  selected twisted sector to a corner of a finite central extension.  This
  relaxes `(ACAE1)` without creating a separate compiler theorem.
- **Universal action-factor algebraization is false.**
  `haar-algebraic-actions-have-permutation-koopman-spectrum` proves that the
  Koopman representation of a Haar compact-abelian automorphism action is the
  permutation representation on `K-hat`; every measurable action factor has
  Koopman representation contained in that permutation representation.  For
  `Z`, this already excludes irrational rotations because the only point
  eigenvalues of a permutation unitary are roots of unity.  Thus one cannot
  obtain `(ACAE1)` by putting an arbitrary compact group structure on the
  existing atomless relation base.
- **Direct Haar-IRS realizations have an arithmetic fence.** For a finite set
  `F subset Lambda`, Haar probability that all elements of `F` fix the random
  point is either zero or the reciprocal of the index of the closed fixed
  subgroup.  For the preferred `F_p`-linear subshifts it is exactly zero or a
  power `p^(-r)`.  The Manzoor IRS must pass all of these cylinder tests before
  it can be realized directly as a Haar-linear stabilizer process.  No
  violating cylinder is currently known, so this is a falsification test, not
  a refutation.

These fences isolate the smallest live theorem more accurately.  It is not a
universal algebraization of p.m.p. actions.  One must either construct a
special non-CE Haar algebraic action natively, or produce a genuinely
non-Cartan/non-base-equivariant inclusion `(ACAE1)` in which the original
relation action is not a measurable factor of `K` and its normalizers are not
identified with the global `Lambda`-unitaries.
