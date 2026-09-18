---
rg: 2
id: one-relator-groups-sofic
kind: claim
title: "Pestov Question 4.10: every one-relator group is sofic"
root: true
distinct_from:
  nonsofic-one-relator-group: that is the negative answer to the same question and asks for a witness; this is the affirmative answer and asks for a proof covering all relators. They cannot both be established, and no route to either is a route to the other.
  residually-rationally-solvable-one-relator-sofic: that is this statement restricted to the residually rationally solvable subclass, and it is closed; this is the full question and is open.
  hyperlinear-implies-sofic: that is Pestov's Question 3.4 in the affirmative and concerns hyperlinear groups; this is his Question 4.10 and concerns one-relator presentations. Neither is known to bear on the other.
  pestov-question-5-3-negative: that is Pestov's Question 5.3, about essentially free near actions, and it is closed negatively by this development; this is his Question 4.10 and is untouched by it.
  q3-4-resolved: that is the program goal — Pestov's Question 3.4, resolved either way, about hyperlinear groups — and admits exactly two answer routes by construction; this is his Question 4.10, a single directional statement about one-relator groups, with ordinary routes and a separate negation claim. Neither question is known to bear on the other.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that proves every one-relator group sofic only after quotienting by the derived Linton radical and gives a new positive class when `R' = 1`; this asks for the remaining nonabelian core as well.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
---

OPEN.  Pestov, *Hyperlinear and sofic groups: a brief guide* (arXiv:0804.3968),
Open Question 4.10: is every one-relator group `G = <X | w>` sofic?

Live reductions and failed approaches are recorded below. As of the
2026-09-07 update, this repository has no resolution in either direction;
the negative answer is the separate
claim [[nonsofic-one-relator-group]].

## What is already settled

- [[peelable-extreme-one-relator-groups-are-sofic]] — if some zero-exponent
  Magnus rewriting has an extreme letter forming one syllable, or two
  syllables of equal absolute exponent, the group is sofic. The remainder is
  [[unpeelable-extreme-one-relator-groups-sofic]], routed through
  `tf-two-generator-sofic-via-extreme-peeling`.
- [[berlai-mixed-conjugator-example-is-sofic]] — a cyclic-amalgam
  construction now proves the asymmetric example `w=b^(-1)ab^2` sofic.
  [[single-block-conjugator-one-relator-groups-are-sofic]] covers every
  `w=b^p a^s b^q`, and
  [[one-sided-conjugator-one-relator-groups-are-sofic]] permits arbitrary
  words with strictly one-sided indexed support. These are written proofs
  with explicit subgroup and presentation checks, not Lean certificates.
- [[one-relator-soficity-is-torsion-free-two-generator-case]] — the full
  question is exactly equivalent to the torsion-free two-generator case.
  Torsion one-relator groups are residually finite, and every torsion-free
  one-relator group embeds in a torsion-free two-generator one-relator group.
- [[berlai-nonresidual-one-relator-families-sofic]] — two explicit infinite
  two-generator families are sofic, including examples that are neither
  residually finite nor residually solvable; this closes the Bannon--Noblett
  subproblem but not the full question.
- [[residually-rationally-solvable-one-relator-sofic]] — the whole residually
  rationally solvable subclass is sofic.
- [[one-relator-soficity-localizes-at-rational-derived-stage]] — for every
  one-relator group there is an `n <= |w|` with `G` sofic **iff** `E = G_Q^(n)`
  sofic, and `E` is free-by-(rationally perfect).  So the remaining content of
  this claim is exactly [[linton-shell-sofic]].
- [[one-relator-fox-magnus-descent-to-derived-linton-radical]] — the whole
  quotient `G/R'` embeds in a finite-lamp wreath product and is sofic, while
  `E/R'` is residually finite.  In particular
  [[one-relator-abelian-linton-radical-sofic]] closes the class `R' = 1`.
- [[nonsofic-one-relator-relator-has-primitivity-rank-two]] — any
  counterexample has `π(w) = 2`, so is torsion-free and locally indicable.

## Attempts

1. **Reduce to the Linton shell and prove the shell sofic.**  *Live, with its
   first-order layer closed*, recorded
   as `one-relator-sofic-via-linton-shell`.  The reduction is done; the shell is
   [[linton-shell-sofic]].  Its quotient by `R'` is residually finite; all
   remaining difficulty sits in an action-compatible, genuinely nonabelian
   approximation of the derived core.
2. **Magnus induction on relator length.**  *Stalls, and the stall is precise.*
   For `χ : G ↠ Z` with `t`-exponent-sum zero, `ker χ` is a bi-infinite amalgam
   of shorter one-relator pieces `B_i` over free Magnus subgroups `C_i`, and
   `G` is sofic iff `ker χ` is (the quotient is `Z`, amenable).  When
   `rank C_i <= 1` the edge groups are amenable and existing amalgamation
   permanence plus directed unions finish.  When `rank C_i >= 2` the edge group
   is a nonamenable free group and no permanence theorem applies; worse, a
   finite window of the chain is a **staggered multi-relator** group, not a
   smaller one-relator group, so the induction hypothesis is not available
   either. The new [[triangular-conjugate-bs-chains-are-sofic]] construction
   closes a subclass even with rank-two or larger standard overlaps by
   proving an alternative sequence of cyclic attachments. It does not
   supply such a construction for every chain. The remaining repair is
   isolated as [[magnus-staggered-chain-sofic]] and
   routed by `one-relator-sofic-via-magnus-staggered-amalgam`.
3. **Recent graph-of-groups soficity theorems.**  *Dies on hypothesis
   mismatch.*  Gao--Kunnawalkam Elayavalli--Mj (arXiv:2408.11724) cover doubles
   and graphs whose edge embeddings are identical or separability-controlled; a
   generic Magnus HNN has **two distinct** embeddings of its free associated
   subgroup, and nothing in the theorem identifies them.
4. **Sofic kernel with residually amenable quotient.**  *Dead*, recorded as
   `one-relator-sofic-via-residually-amenable-quotient` and killed by
   [[relative-soficity-extension-theorem-withdrawn]].  This is the most
   attractive wrong turn in the region — Linton hands over a residually
   rationally solvable quotient on a plate — so it is labelled rather than
   omitted.
5. **Semidirect closure applied to the shell.**  *Dead*, recorded as
   `linton-shell-sofic-via-generic-semidirect-closure` and killed by
   [[sofic-semidirect-product-closure-fails]].
6. **Strong Atiyah / Lück approximation / coherence.**  *Discarded, not
   attempted to conclusion.*  The peer-reviewed theorems
   [[one-relator-groups-are-coherent]],
   [[characteristic-zero-one-relator-group-algebras-are-coherent]], and
   [[torsion-one-relator-group-algebras-are-coherent-over-all-fields]] close
   group coherence, characteristic-zero group-algebra coherence, and the
   all-fields torsion branch, respectively.  None states or implies soficity:
   homological and ring finiteness are not finite symmetric-group
   approximation.  Treating them as a bridge would be exactly the error this
   graph exists to prevent.
7. **Locally finite alphabet along the Magnus shift.**  *Closes a class and
   gives a one-directional reduction; dies exactly at singular extremes.*
   [[nonsingular-magnus-extremes-separable-piece-sofic]]:
   - **Hypotheses.** Both extreme letters of the Magnus rewriting have
     nonzero exponent sum, and the piece `B_0` is residually finite with
     `F_-` and `F_+` separable.
   - **Conclusion.** `G` is sofic.
   - **Method.** A finite quotient of the piece is extended letter by letter
     along the shift, by solving nonsingular equations in finite overgroups
     (Gerstenhaber--Rothaus). The target is residually-locally-finite-by-`Z`,
     so it is neither residually finite nor amenable.
   - **Coset action.** It is sofic through an enlarged stabilizer that is
     detected at coordinate `0`.
   - **Free pieces.** Free Magnus pieces with nonsingular extremes are
     therefore sofic.

   The method fails at the first equation with zero exponent sum. For
   Baumslag--Gersten the forward step `X^(-1) u X = u^2` is unsolvable
   whenever `u` has even order. More strongly, every shift representation of
   BG over a periodic alphabet is trivial on `a`: a descending-prime argument
   rules it out. So a singular extreme needs letters of infinite order, and
   those give up the local finiteness that the coset-action step uses.
8. **Amenable alphabets at singular extremes.** *Reduction landed; the model
   case is open, and the `U(m)` way out of Attempt 7 is dead.*
   - **Reduction.** [[amenable-alphabet-magnus-shift-dictionary-sofic]]: local
     finiteness was never needed. Any amenable alphabet works, with no
     exponent hypothesis. `G` is sofic once the Magnus kernel has amenable
     quotients that separate finitely many piece elements from `F_-`, `F_+`
     and `1`. Attempt 7 is the special case of a locally finite alphabet
     obtained by solving nonsingular equations.
   - **Obstruction.** [[bg-shift-chains-die-in-residually-linear-alphabets]]:
     an infinite forward chain `x_(j+1)^(-1) x_j x_(j+1) = x_j^2` is trivial in
     every group that is residually periodic, linear over any field, or
     solvable, and in every compact group. So the BG dictionary kills `a` over
     `U(m)`, over every linear alphabet, and over every residually solvable
     alphabet.
   - **Rank one.** With `n = 1` the Magnus edges are cyclic, and `G` is sofic
     iff `B_0` is. BG itself is sofic classically. Singular extremes matter
     only for `n >= 2`, where BG is the model zero-exponent step.
   - **Next step.** [[bs12-extends-to-amenable-square-conjugation-chain]]:
     embed `BS(1,2)` in an amenable group carrying an infinite forward chain.
     Equivalently, iterate an amenable extension lemma that conjugates an
     infinite-order element to its square. A solvable length-3 stage is
     explicit. Any full solution is perfect on the chain and not residually
     linear. A negative answer kills the shift dictionary at every singular
     extreme of this type.
   - **Model case settled positively (w5-073).**
     [[bs12-extends-to-amenable-square-conjugation-chain]] is proved by an
     induced-module tower. The prepend step is
     `Phi(K,c) = Ind_(<c>)^K(Q_(1/2)) rtimes K`. It is functorial, and its
     direct limit from `Z` is locally solvable and carries the forward
     chain. Moreover, [[baumslag-gersten-elementary-amenable-quotient-keeps-a]]:
     `BG` maps to an elementary amenable group with `a` of infinite order. So
     (AA) holds for `BG`, and the singular forward step is passable. The
     mechanism never solves the singular equation. It solves the linear
     backward equation universally, and the limit converts prepending into
     forward growth.
   - **Open next.** For `n >= 2`, the same functor needs the backward
     equation in `a_0` to linearize over an abelian normal layer. It also
     needs a seed group embedding in its own `Phi`-image, and separation of
     `B_0` from the rank-`n` subgroups `F_-` and `F_+`.

First-order Fox, abelian, solvable, and rational-derived iterations are no
longer live completion strategies in the perfect-core regime.  Their maximal
descent is the exact kernel `R'` computed above; when `k = 1`, `R = R'` is
already perfect and every solvable lamp quotient is trivial.
