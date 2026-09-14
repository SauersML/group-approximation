---
rg: 2
id: surjunctivity-recognition-has-a-pi2-upper-bound
kind: claim
title: Surjunctivity of presented groups is Pi-zero-two, and its failure is Sigma-zero-one on decidable hosts
distinct_from:
  weak-soficity-recognition-has-a-pi2-upper-bound: that certifies weak soficity with finite groups and bounded-area non-membership; this certifies non-surjunctivity with strict rectangle data, derivable premise equations and underivable conclusion equations.
  leavitt-unit-certificate-predicates-are-decidable: that decides certificates over one group with decidable word problem; this is the uniform bound on every presentation syntax, together with the Sigma-zero-one bound on every decidable host.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that is the axiomatization; this counts its quantifiers.
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

**ESTABLISHED** by `surjunctivity-recognition-has-a-pi2-upper-bound-proof`.

Let `q` code a presentation `<X | R>` of `K` with `R` recursively enumerable: a
finite presentation (`fp`), a finitely generated recursive presentation (`rec`), or
a countably generated enumerated presentation (`enum`). Then `K` is not surjunctive
iff there are strict rectangle data `D`
(`surjunctivity-is-axiomatized-by-rectangle-clauses`) and words `w_a` in `X^(±1)`,
with both labels `1` given the empty word, such that

    w_s w_m  = w_s' w_m'   in K   for all (s,m) T_f (s',m'),          [Sigma^0_1]
    w_m w_s != w_m' w_s'   in K   for all pairs not T_r-related.       [Pi^0_1]

Hence `NONSURJ_fp`, `NONSURJ_rec` and `NONSURJ_enum` are `Sigma^0_2`, and
`SURJ_fp`, `SURJ_rec` and `SURJ_enum` are `Pi^0_2`, uniformly in the code.

**Decidable hosts.** If `K` is finitely generated and a total program `e` decides
its word problem, both brackets are decidable. So non-surjunctivity of `K` is
`Sigma^0_1`, uniformly in `(q, e)`. For the binary Leavitt unit group this is
`leavitt-unit-certificate-predicates-are-decidable`.

**Reading.** A counterexample is a finite object modulo the inequalities in the
second bracket. Those can be certified only inside a group that is itself not
surjunctive: a homomorphism into a surjunctive group preserving them would
realize the data there. So no residually finite, sofic or other surjunctive
quotient can ever witness them.
