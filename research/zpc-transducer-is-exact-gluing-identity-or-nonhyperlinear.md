---
rg: 2
id: zpc-transducer-is-exact-gluing-identity-or-nonhyperlinear
kind: claim
title: A ZPC context transducer is an exact marked gluing identity or already a nonhyperlinear group
distinct_from:
  finite-subgroup-type-exclusion-is-already-nonhyperlinearity: that evaluates one primitive character idempotent of a finite subgroup; this evaluates the cross-context decoded-mismatch energy of the transducer, whose payload words need not lie in any finite subgroup, and splits every transducer into an exact case and a matrix-specific case.
  regular-trace-blocks-exact-local-predicate-return: that forbids exact trace-level exclusion of a selector atom; this is the complementary statement for the gluing term and identifies which matrix-specific gluing estimates are circular.
  zpc-context-mismatch-transducer: that is the open quantitative context-consistency inequality; this classifies every possible witness of it by whether its gluing energy vanishes in the marked group algebra.
  priority-decoder-lipschitz-under-selector-gate-alignment: that is the analytic estimate once matched labels exist; this is a structural dichotomy about the presentation that must supply them.
---

**ESTABLISHED.**  Let `L` be a finite binary LCS with solution group
`Gamma_L` and marked central involution `J`, carrying predication contexts as
in `zpc-context-mismatch-transducer`.  Assume every decoded copy `U_(c,q)` is
a fixed element of `C[Gamma_L]`:

- the priority projections `Q_(c,a)` are polynomials in the selector
  variables of context `c`;
- the predicated branch copies are words in the LCS variables;
- any corner identifications used to compare copies are fixed words.

Write the gluing energy as

```text
D_glue = sum_(c,d,q) w_(c,d,q) ||U_(c,q) - U_(d,q)||_2^2,     w_(c,d,q) > 0,
```

a fixed finite sum of group-algebra words.  If `(CTX')` holds for every
finite-dimensional strategy of `L`, then at least one of the following holds:

```text
(a) (U_(c,q) - U_(d,q)) (1-J) = 0  in C[Gamma_L]  for every incident pair;
(b) Gamma_L is nonhyperlinear.                                   (TGD1)
```

If `J = 1` in `Gamma_L`, then (a) holds vacuously and the transducer is not
perfectly complete, so the content is the case `J != 1`.  The proof is
`zpc-transducer-dichotomy-proof`.

## Consequences

- **Matrix-specific soundness is circular.**  A transducer for which (a)
  fails is by itself a finitely presented nonhyperlinear group.  It uses
  neither the tailored game of `perfect-zpc-irs-quantum-gap-game` nor that
  game's quantum gap.  As a step toward `non-hyperlinear-group` it is not a
  reduction: proving it already solves the root.
- **Exact identities are the only non-circular transducers.**  For type (a),
  the gluing term of `(CTX')` follows from the finite derivation of the
  identity with a dimension-free constant, and all soundness comes globally
  from the source gap, as the ZPC compiler intends.
- **What an exact identity must look like.**
  `selector-gated-equality-is-not-affine-pp-definable` rules out exact
  identities built from commuting parity auxiliaries while preserving the
  singleton menu.  A non-circular transducer therefore needs an exact
  projective central-sign gluing identity in `C[Gamma_L](1-J)` with no
  relevant scalar sector.
- **A one-line screen for gauge-lock candidates.**  The open input
  `zpc-controlled-pauli-and-hs-shared-gauge-lock` is required *not* to be a
  universal identity.  Evaluate any candidate in the left regular
  representation of its output solution group.
  - If the selector-active payload-mismatch carrier has positive canonical
    trace on the `J=-1` corner there, (a) fails and the candidate is of type
    (b): proving its lock is already nonhyperlinearity-strength.
  - If that trace is zero, the gluing is an exact identity and the lock is not
    needed for the gluing term.

  No dimension-free matrix estimate can change which case a candidate is in.

## Scope

The dichotomy needs the comparison maps to be fixed words.  A construction
whose corner identifications are chosen model by model, by rounding inside
each finite-dimensional strategy, is not covered.  Such a transducer must be
audited against `local-exactification-invariants-cannot-close-gluing-holes`
instead.
