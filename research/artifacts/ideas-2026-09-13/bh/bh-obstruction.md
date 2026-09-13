# Idea lane bh-obstruction: the counterexample direction for Boone–Higman

Date: 2026-09-13. Target: `boone-higman-conjecture`.

These are ideas, not results. Nothing here is a theorem. "Survives" means only
that the first kill test did not kill the approach.

## The filter every separating invariant must pass

- **Only inherited properties can separate.** If `G <= S`, a property of `S`
  constrains `G` only through a form that passes to finitely generated
  subgroups. Two kinds pass down:
  - universal first-order sentences;
  - word-problem complexity upper bounds (length-linear substitution).
  Laws, torsion or Dehn functions of `G` need not hold in `S`.
- **Solvable word problem is not enough, and finite presentation must be used.**
  Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356, Theorem 3.8, as read from
  source in `boone-higman-thompson-simple-envelope`: "A finitely generated group
  has solvable word problem if and only if it embeds into a finitely generated,
  computably presented simple group." So a separating invariant must hold for
  finitely generated subgroups of every finitely presented simple group, and fail
  for some finitely generated subgroup of a computably presented simple group.
- **Relation to the root.** Attempt 7 on the root found no hereditary separating
  property beyond solvable word problem. Approach 1 below is a candidate
  property, conditional on a uniform bound.

## Approach 1: a uniform complexity bound on all fp simple groups (SURVIVES, sharpest)

- **Idea.** Suppose one recursive `T` serves every finitely presented simple
  group `S`: some algorithm decides its word problem in time
  `C_S*T(C_S*l) + C_S*l + C_S`. Then `complexity-bounded-host-classes-are-not-universal`
  (ESTABLISHED) gives a two-generated group with solvable word problem that
  embeds in no finitely presented simple group, so Boone–Higman fails.
- **What it would prove.** A counterexample, through the diagonal input of that
  claim, not an explicit group.
- **Contrapositive already in the graph.** Boone–Higman implies the OPEN root
  `fp-simple-groups-with-arbitrarily-complex-word-problem`. Both routes into that
  root (`arbitrarily-complex-fp-simple-via-hard-type-a-actors`,
  `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`) sit on OPEN
  premises. The first records that twisted Brin–Thompson hosts beat every
  recursive bound only if their type (A) actors do.
- **Kill test run: literature.** J.-C. Birget, "Circuits, coNP-completeness, and
  the groups of Richard Thompson", arXiv:math/0310335, §1 (quoted through the
  arXiv HTML; re-read the PDF before citing further):
  - "A consequence of this conjecture would be that the word problem of finitely
    presented simple groups can have arbitrarily large time complexity." The
    conjecture meant is Higman's strengthening of Boone–Higman.
  - "All known finitely presented simple groups have word problems with rather
    low complexity (in the cases where the complexity has been analyzed in
    detail it always turned out to be in the complexity class P)."
- **Verdict: survives.** This is the one counterexample route with an ESTABLISHED
  implication. A uniform bound is implausible in expectation. The next kill test
  is concrete: build one family of finitely presented simple groups beating every
  recursive bound. For example, show that the hard finitely presented residually
  finite groups of `kms-arbitrarily-hard-fp-rf-groups` admit type (A) actions or
  Röver–Nekrashevych envelopes. That would kill this approach and close the root
  positively.

## Approach 2: isoperimetric, Dehn-function and distortion inheritance (KILLED)

- **Idea.** A finitely presented group with solvable word problem has a recursive
  Dehn function. Try to push an isoperimetric constraint from `S` down to `G`.
- **Kill test run.** Dehn functions and distortion do not pass to finitely
  generated subgroups.
  - Birget–Olshanskii–Rips–Sapir, Annals 156(2) (2002), arXiv:math/9811106
    (abstract): the word problem of `G` is in NP iff `G` is a subgroup of a
    finitely presented group with polynomial isoperimetric function, with bounded
    distortion possible.
  - Finitely presented simple groups with at least exponential Dehn function
    exist (arXiv:2305.15176; title only, not read).
  So an isoperimetric property of the host reaches `G` only through word-problem
  complexity.
- **Verdict: killed** as an independent invariant. It reduces to Approach 1.

## Approach 3: torsion, laws and centralizers (KILLED as invariants)

- **Idea.** Find algebraic structure forced on subgroups of finitely presented
  simple groups.
- **Kill test run: direction of inheritance.** A law or torsion property of `G`
  never needs to hold in `S`. The properties of `S` that pass down are universal
  sentences (Approach 5). Concretely, Röver's finitely presented simple group
  `V𝒢` contains Grigorchuk's infinite torsion group (as recounted in
  arXiv:2405.09722).
- **Test input kept, with no obstruction attached.** Free Burnside groups
  `B(m,n)` are item (6) of Problem 5.3 in arXiv:2306.16356. The list is from a
  summarizing fetch; re-read before quoting.
- **Verdict: killed** as an invariant lens.

## Approach 4: isolatedness as the missing "finite presentation" invariant (UNCLEAR)

- **Idea.** Finite presentation buys what computable presentation does not:
  finitely presented simple groups are isolated points of the space of marked
  groups.
- **Source.** Cornulier–Guyot–Pitsch, J. Algebra 307 (2007), arXiv:math/0511714,
  read from the PDF text:
  - a finitely generated group is isolated iff finitely presented and finitely
    discriminable;
  - Theorem 3.4 (stated as Theorem 4 in the introduction): solvable word problem
    iff recursively presentable and recursively discriminable;
  - Corollary 5: isolated groups have solvable word problem;
  - Theorem 7: finitely discriminable (resp. isolated) groups are stable under
    extensions and finite-index overgroups;
  - Theorem 9: every finitely generated group is a quotient of an isolated group.
- **Weaker target.** Every finitely generated group with solvable word problem
  embeds in an isolated group. Boone–Higman implies this, so an input embedding
  in no isolated group refutes Boone–Higman.
- **Kill test run.** The extracted text states no subgroup heredity (Theorem 7
  lists only extensions and finite-index overgroups; Theorem 9 is about
  quotients). By hand, finite discriminability does not pass to subgroups:
  `Z <= V`. So no intrinsic invariant results, only the embedding question.
- **Verdict: unclear.** Sharp question for a follow-up lane: does every finitely
  generated group with solvable word problem embed in an isolated group? A
  positive answer would be "Boone–Higman without simplicity".

## Approach 5: a universal sentence true in every fp simple group (UNCLEAR)

- **Idea.** Universal sentences pass to subgroups, so the fully intrinsic
  hereditary invariants are finite systems `Σ` of equations and inequations
  unsatisfiable in every finitely presented simple group. A `Σ` satisfiable in a
  group with solvable word problem but in no finitely presented simple group
  refutes Boone–Higman. This is strictly stronger than a counterexample, since
  an embedding imposes infinitely many conditions.
- **Kill test run.**
  - Every finite group embeds in Thompson's `V`, which contains the symmetric
    group permuting `2^k` standard dyadic intervals. So any `Σ` with a finite
    model is realized in `V`.
  - Systems realized in the known Boone–Higman classes are realized too:
    hyperbolic groups, Baumslag–Solitar groups, `GL_n(Z)`, contracting or
    finitely presented self-similar groups (as summarized from arXiv:2306.16356).
  - So `Σ` needs no finite models and no models in those classes. Candidate:
    Higman's relations `x_i^{x_{i+1}} = x_i^2` (indices mod 4) with `x_1 != 1`.
    Every model contains a nontrivial quotient of Higman's group, which has no
    nontrivial finite quotients. Solvability of its word problem was not checked
    here. The survey summary does not mention it, and a web search found no
    embedding into a finitely presented simple group.
- **Verdict: unclear.** Next kill test: embed Higman's group, or a quotient where
  `x_1` survives, in a known finitely presented simple host (twisted
  Brin–Thompson, Röver–Nekrashevych). The repository's obstructions for
  Baumslag–Gersten and Deligne's lattice kill only Röver–Nekrashevych hosts, not
  Boone–Higman.

## Summary

- Approach 1 is the only counterexample route with an ESTABLISHED implication: a
  uniform bound on all finitely presented simple groups refutes Boone–Higman. It
  is the negation of the OPEN root
  `fp-simple-groups-with-arbitrarily-complex-word-problem`.
- Approaches 4 and 5 leave sharpened intermediate questions: embedding in
  isolated groups, and a separating universal sentence.
- Approach 2 reduces to Approach 1. Approach 3 dies on the direction of
  inheritance.
