---
rg: 2
id: literal-mark-conjugacy-width-unbounded
kind: claim
title: The literal mark has unbounded relator-conjugacy width across finite quotients
distinct_from:
  unsquared-defect-finite-model-invisible: that says every finite quotient kills the mark, i.e. the lift lies in the profinite closure of the whole relation subgroup; this says the lift lies in the profinite closure of no FIXED bounded product of relator conjugacy classes, which is the sharper and opposite-signed fact
  literal-central-mark-corona-invisible: that is the operator-norm corona obstruction that makes `E` non-MF; this is a profinite-topology statement about the same word, proved from soficity of `E`, and it says the finite-quotient side of the story cannot be strengthened
  literal-group-sofic: that is the input, soficity of `E`; this is the consequence drawn from it via the weak-soficity criterion, and it is a statement about the presentation rather than about the group's approximability
  literal-mark-quotient-finite-residual: that computes the finite residual of the marked quotient `E/<w>`; this is about the mark itself in `E` and counts conjugacy factors rather than identifying a subgroup
  literal-mark-quotient-not-mf: that is an operator-norm result about the quotient `E/<w>`, placing the unsquared defect in its MF radical; this is a profinite-topology result about `E` itself, counting how many relator conjugates a finite quotient needs, and no matrix or radical appears in it
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
  - GroupApproximation/Sofic/LiteralFiniteDimensionalObstruction.lean
  - GroupApproximation/Sofic/LiteralNonMFPresentation.lean
---

Write the literal group as `E = F/N` with `F` free on the eight generators
`Generator = Fin 6 ⊕ Fin 2` and `N = N(R)` the normal closure of the explicit
relator `Finset` `relators`; let `wt in F` be `markedWord` and `w = wt N` the
mark.  For `m >= 0` put

```text
P_m := union over j <= m, over (a_1,...,a_j) in (R ∪ R^(-1))^j
         of  [a_1]^F ... [a_j]^F          (the j = 0 product is {1}),
```

the elements admitting a relator expression of conjugacy width at most `m`.
Then

```text
(a)  wt  in  closure_prof(N)  \  N                     -- N is not profinitely closed
(b)  wt  not-in  closure_prof(P_m)      for EVERY fixed m
(c)  for every fixed m there is a finite quotient q_m with q_m(wt) not-in q_m(P_m),
     while for every finite quotient q one has q(wt) in q(N).
```

So the minimum number of relator conjugates needed to express `q(wt)` inside
`q(N)` is **unbounded** as `q` ranges over finite quotients.

## Why this is the interesting direction

`unsquared-defect-finite-model-invisible` is a strong negative: the mark has
no detector in any finite quotient at all.  It is tempting to read that as
the beginning of a non-weak-soficity argument, since
`non-weakly-sofic-word-certificate` also asks for a word that every finite
quotient absorbs into the relators.  It is not.  The certificate needs the
absorption to happen at a **fixed** conjugacy width, and (b) says that for
`E` no fixed width works — not "we have not proved one works", but no width
works, because `E` is sofic and hence weakly sofic and hence subject to
`glebsky-rivera-w-sofic-criterion` in the positive direction.

Statement (a) together with (b) also exhibits the exact set-theoretic failure
behind the temptation: `N = union_m P_m` is an increasing union, and

```text
closure_prof( union_m P_m )   strictly contains   union_m closure_prof(P_m)
```

with `wt` in the left side and in no term of the right.  Profinite closure
does not commute with increasing countable unions, and `E` is a concrete
witness that it does not, in precisely the configuration where one would want
it to.  Glebsky--Rivera Remark 4.8 says the same thing from the completion
side: the normal closure in `Fhat` is closed iff it has bounded width, and
compactness gives nothing weaker.

## Consequence for the corpus

Any future argument that routes this repository's finite-quotient kill
theorem toward a non-weakly-sofic endpoint contains a false step, and (b)
localizes where: at the moment the argument fixes a relator list. Recorded so
that the route is not re-attempted.  The companion node
`weak-soficity-survives-every-corpus-obstruction` records the same conclusion
for the corpus's other obstruction mechanisms.
