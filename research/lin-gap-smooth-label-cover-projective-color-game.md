---
rg: 2
id: lin-gap-smooth-label-cover-projective-color-game
kind: claim
title: Lin's explicit commuting-versus-tensor gap lowers to one edge-oracular smooth-label-cover game
artifacts:
  - research/artifacts/cmps-smooth-label-monomial-audit-2026-08-23.md
distinct_from:
  lin-explicit-synchronous-bell-gap-game: that supplies the effective general synchronous source; this lowers it to smooth-label-cover edge predicates.
  culf-mastel-oracular-2csp-perfect-gap-family: that is a HALT-oriented finite-dimensional/CE family from a different paper; this freezes Lin's known nonhalting loop and retains perfect commuting rather than CE completeness.
  smooth-label-cover-edges-are-finite-phase-projective-color: that is a syntax theorem for every smooth-label instance; this also transports the commuting-versus-finite-dimensional separation to a particular instance.
---

**ESTABLISHED HYBRID-MODEL COROLLARY.**  For every rational `0<s<1`,
Lin's fixed unconditional-loop game can be transformed effectively into a
finite smooth-label-cover instance `S_(loop,s)` whose synchronous game has

```text
omega_co(S_(loop,s))=1,
omega_q^s(S_(loop,s))<=s.                               (LSG1)
```

Moreover, the perfect commuting model may be chosen **edge-oracularizable**:
in its one-player tracial realization,

```text
[P_v^a,P_w^b]=0  for every edge (v,w) and labels a,b.    (LSG2)
```

In particular its synchronous game algebra has a tracial state and no
nonzero homomorphism into `R^omega`.  Every edge predicate is the
projective-color relation `(SLC1)` from
`smooth-label-cover-edges-are-finite-phase-projective-color`.

The commuting-completeness statement in `(LSG1)` is not stated as a theorem
in Culf--Mastel--Paddock--Spirig: they explicitly say that they do not work
with the commuting-operator value.  It is nevertheless an exact corollary of
their displayed constructions.  Their completeness maps use only PVM
functional calculus, finite tensor products, copying observables, and a
tracial state, so they apply without change to a synchronous commuting model.
Their soundness maps use finite-dimensional PVMs and therefore retain the
quantum gap in `(LSG1)`.  Lemma 20's radius-two commutators and Theorem 19's
displayed PVM calculation are likewise algebraic and give `(LSG2)` in that
chosen tracial model.

This does not give one monomial matrix pair.  Edgewise projective-color
syntax neither supplies the column relations of a square quantum-reflection
matrix nor proves a trace-preserving full-corner completion.
