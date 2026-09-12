---
rg: 2
id: exact-switch-mf-recognition-completeness-proof
kind: route
title: Classify MF exactly on the explicit finite-event ray switch
target: mf-recognition-recursive-presentations-is-second-level-complete
requires:
  - exact-literal-e-fin-inf-switch
  - literal-central-mark-corona-invisible
---

# Exact switch MF-recognition completeness: unconditional proof

## Result

For the uniformly code-indexed exact switch family `S_c`, actual weak-MF
recognition is `Π⁰₂`-complete and actual non-MF recognition is
`Σ⁰₂`-complete.  Moreover, neither predicate is r.e. or co-r.e.; neither is
decidable; and neither admits a sound and complete finite computably checkable
certificate system.

The non-MF side is always witnessed by survival of the same fixed
MF-invisible element of the same fixed finitely presented group `E`.

## Exact semantic classification

The event-ray theorem has only two branches.

* If the program domain is infinite, first-halting events are unbounded and
  every switch generator dies.  Thus `S_c` is trivial, hence finite and
  weak-MF.
* If the program domain is finite, there is a last event.  The surviving tail
  is explicitly isomorphic to `E`.  Its fixed MF-invisible mark remains
  nontrivial, so `S_c` is not weak-MF.

Therefore

```text
IsWeakMF(S_c)     iff InfiniteDomain(c),
not IsWeakMF(S_c) iff FiniteDomain(c).
```

Equivalently, on this family the fixed marked queries are complete semantic
detectors rather than merely one-way obstructions:

```text
KILL(S_c) iff IsWeakMF(S_c),
SURV(S_c) iff not IsWeakMF(S_c).
```

## Second-level completeness

The internal finite-prefix compiler proves `InfiniteDomain` is
`Π⁰₂`-complete and `FiniteDomain` is `Σ⁰₂`-complete.  The displayed exact
equivalences preserve both the upper bounds and every computable many-one
reduction.  Hence actual weak-MF and non-MF recognition on the switch family
have the claimed complete complexities.

## Strict first-level separation without a hierarchy oracle

Encode programs numerically and let `NH(n)` mean that the decoded program does
not halt on input zero.  A bounded evaluator check shows `NH` is `Π⁰₂`.
Writing `NH` as the complement of the r.e. halting predicate also places it in
`Σ⁰₂` under the repository's normal-form convention.  Mathlib's formal
non-enumerability theorem for nonhalting gives `NH ∉ RE` with no assumption.

Since both complete target predicates accept computable reductions from
`NH`, neither target predicate is r.e.  Each is the complement of the other,
so neither is co-r.e.  A computable predicate is r.e.; therefore neither is
computable.

## No finite certificate systems

Suppose weak-MF on the family had a sound and complete certificate system with
a computable Boolean verifier `V(c,π)`.  Then weak-MF would be the existential
projection

```text
exists π, V(c,π)=true,
```

which is r.e., contradicting the strictness result.  The same argument applies
to non-MF.  Thus neither side has a complete finite checkable proof system.

No external hierarchy-separation theorem, Higman theorem, Chiodo theorem, or
new assumption is used.  The sole group-theoretic seed is the already proved
non-MF marked group, as permitted by the theorem's scope.
