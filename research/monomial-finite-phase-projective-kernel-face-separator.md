---
rg: 2
id: monomial-finite-phase-projective-kernel-face-separator
kind: claim
title: Extract a testable finite-phase projective-kernel face gap from the monomial extreme trace
refuted_by: factor-split-projective-kernel-face-meets-fd-closure
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
distinct_from:
  monomial-gap-phase-safe-toric-groupification: that asks for the finished toric gap; this is the smaller surviving state-face certificate after direct Fourier-clause groupification is excluded.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that gives counterexamples for arbitrary non-CE traces; this asks whether the extra finite-phase monomial linking structure supplies the missing face exclusion and testability.
  bcs-projective-kernel-phase-compilation: that engineers one nonlinear predicate phase in a BCS gadget; this may use any finite-phase normal subgroup of the monomial question group and asks for exclusion of the entire finite-dimensional face.
---

**REFUTED.**  The proposed target began with an `s`-monomial game algebra
`A_mon` with a trace and no
nonzero homomorphism into `R^omega`.  Choose an extreme trace `tau`, let `G`
be the full two-player question group in its standard tracial realization,
and let `pi_tau` be that group representation.

Find a normal subgroup `K normal G` and a conjugation-invariant character

```text
chi:K -> mu_q                                              (MPK1)
```

such that `pi_tau(k)=chi(k)I` and

```text
F_(K,chi) intersect closure(S_fd(G))=empty.                (MPK2)
```

Then realize a finite subset supplied by
`projective-kernel-face-gap-compactifies-phase-safely`
as a determining set of an explicitly finite two-player game, with every
finite-dimensional perfect state decoding to the face in `(MPK2)`.

The first condition is stronger than non-Connes-embeddability of `tau`:
unrelated finite-dimensional states of the same projective-kernel quotient
must all be excluded.  The second condition is a testability requirement:
arbitrary group binomials are not automatically the determining clauses of a
one-round two-player game.

This target no longer asks the toric clauses to carry the monomial Fourier
projections.  Those projections must remain in the noncentral decoded
algebra, while `(MPK1)` supplies only central/projective-kernel shadows.  A
solution gives a finite phase-safe normal closure by `(PKC4)` and retains the
full `qc/qa` gap by `(MPK2)`.

The stronger alternative `monomial-finite-phase-ce-kernel-face-gap` replaces
finite-dimensional vector-state exclusion and game testability by exclusion
of every CE trace.  Its compact quotient gives a nonhyperlinear group
directly, but proving that stronger face exclusion is already the group-level
obstruction rather than a formal consequence of the monomial gap.

The fatal obstruction is
`factor-split-projective-kernel-face-meets-fd-closure`.  In the standard
representation of an extreme trace, `pi_tau(a,b)=L(A_a)R(B_b)` on a factor.
If this is scalar, the left and right components are scalar separately.
The product of the two restricted source states therefore lies in
`F_(K,chi)`, and separate one-player RFD puts that product state in
`closure(S_fd(G))`.  Hence `(MPK2)` fails for every choice of `K,chi` of the
stated form, before finite extraction or testability is considered.
