# STW Problem LX (real rank zero weak cancellation / K1-surjectivity) -- swarm attack 2026-09-16

Agent: `swarm-stw99-problem-lx-rr0-weak-canc`.  Lock held on
`stw99-problem-lx-rr0-weak-cancellation` for the session.

## Setup

Problem LX (Schafhauser--Tikuisis--White, arXiv:2506.10902, TeX source read
2026-09-16, e-print dated 2026-05-11):
(1) do real rank zero C\*-algebras have weak cancellation?
(2) are real rank zero C\*-algebras K1-surjective?

STW's definition of weak cancellation: "A has weak cancellation if for all
projections p,q in A which generate the same closed ideal I, one has
[p]_0=[q]_0 in K_0(I) implies p~q".  STW footnote: A is separative iff
A (x) K has weak cancellation (citing Brown--Pedersen JFA 2014, 2.3, and AGOR
Section 3).  STW, same passage: AGOR Theorem 3.1 (separative real rank zero
algebras are K1-surjective); AGOR "Question 3.2" asks (1) in the separativity
form; AGOP Theorem 7.6: separative unital real rank zero algebras that are
finite are stably finite, "and in the simple case, this also implies stable
rank one".

## Status gate (2026-09-16)

* STW e-print (2026-05-11): LX listed as open.
* AGOR arXiv:math/9906141 (PJM 195 (2000)), TeX read: the Problem "Is every
  C\*-algebra with real rank zero separative?" (unnumbered in the arXiv source;
  STW cite it as Question 3.2).
* Ara--Goodearl--O'Meara--Pardo--Perera, *Regular ring properties degraded
  through inverse limits*, arXiv:2405.06837 (v1 2024-05-10, v2 2024-11-20),
  abstract re-read 2026-09-16: "the long standing Separativity Problem", with a
  suggested negative approach via inverse limits of regular rings.  A
  von Neumann regular C\*-algebra is finite-dimensional (a standard fact, not
  re-verified this session), so a regular ring counterexample would not by
  itself answer LX.
* Earlier in this session (before a context compaction) I also read the
  abstracts of Alahmadi--Jain--Leroy arXiv:2104.09296 (non-separative regular
  rings still unknown), Lolk arXiv:1705.04494 (tame separated graph algebras)
  and Brown--Pedersen arXiv:0708.3078 (extremally rich real rank zero).  A
  metadata re-fetch on 2026-09-16 failed (connection resets), so these are
  recorded but not quoted in any node.
* No source found claiming a solution of LX(1), LX(2) or AGOR's Problem.

Verdict: open.  No novelty claim is made beyond the specific reductions below.

## What was proven (graph nodes written)

1. `finite-simple-rr0-sr1-via-weak-cancellation` (route, full proof in body):
   for a unital simple real rank zero `C` with finite unit, weak cancellation of
   `V(C)` gives stable finiteness, cancellation, internal cancellation, and
   density of invertibles.  With the existing reverse route this makes
   `finite-simple-rr0-algebras-have-weak-cancellation` and
   `finite-simple-rr0-algebras-have-stable-rank-one` equivalent.  It formalizes
   STW's parenthetical without using AGOP 7.6.  Step 4 is the standard argument
   that internal cancellation plus real rank zero gives stable rank one, written
   out in full.
2. `agor-separative-rr0-algebras-are-k1-bijective` + citation route
   `agor-separative-rr0-k1-bijective-citation` (requires []): AGOR Theorem 3.1
   verbatim, and the AGOR Section 3 remark "Separativity in A is thus equivalent
   to the requirement that all matrix algebras M_n(A) satisfy the weak
   cancellation introduced by Brown and Pedersen" verbatim.
3. `rr0-c-star-algebras-are-separative` (claim, AGOR's Problem) and
   `rr0-algebras-are-k1-bijective` (claim, Zhang's conjecture as stated by
   AGOR), both with Attempts.
4. `stw99-lx-via-rr0-separativity` (route to the root) and
   `rr0-separativity-via-lx` (converse route): LX is equivalent to AGOR's
   Problem, given the AGOR import.  The non-unital case goes through the
   unitization: `p, q` in `A` generate the same ideal in `A~` as in `A`, and a
   partial isometry `v = vp` in `A~` lies in `A`.
5. `rr0-k1-bijectivity-via-separativity`: AGOR's Problem implies Zhang's
   conjecture.
6. `prime-rr0-algebras-are-separative` (claim, Attempts) and
   `rr0-separativity-from-prime-case-and-k1-bijectivity` (route, artifact
   `research/artifacts/rr0-separativity-prime-reduction-2026-09-16.md`): Zhang's
   conjecture plus the prime case gives AGOR's Problem.

Net: LX(1) <=> AGOR's Problem <=> (Zhang's conjecture AND prime case).

## Normal form (N1) and the critical quotient

Any separativity failure over any real rank zero `A` yields a unital real rank
zero corner `B` with `1 = P + Q`, `P (+) P ~ Q (+) P ~ Q (+) Q`, `P` not
equivalent to `Q`, `P` and `Q` full.  Zorn over ideals modulo which `P, Q`
stay inequivalent gives a critical quotient (equivalence modulo every nonzero
ideal).  The chain step uses `dist(b, closure of union J_a) = lim dist(b, J_a)`
and polar decomposition with constant `1/4`.  This part needs no K-theory.

## Approaches tried and where each dies

* **N3: LX(2) => LX(1) directly.**  From `W` with `W*W = P (+) P`,
  `WW* = Q (+) P` one gets a unitary of `M_2(B)` conjugating the two, and
  K1-surjectivity replaces its class by that of a unitary of `B`.  Dies: this
  only gives unitary equivalence after stabilizing; extracting `P ~ Q` needs
  cancellation.  So no route from Zhang's conjecture alone to separativity was
  found.  The prime reduction is what survives.
* **Gluing in prime algebras.**  The pullback argument needs two nonzero ideals
  with zero intersection.  In a prime critical quotient every gluing over
  `B/(K_1 ∩ K_2)` only reproduces equivalence modulo `K_1 ∩ K_2`, which
  criticality already gives.  Same wall as the LXI prime reduction of another
  swarm agent (`prime-quotient-minimal-k1-trivial-unitaries-are-null`).
* **Separative radical.**  Idea: take the largest ideal `J` such that `B/J` is
  separative, or a maximal ideal with non-separative quotient, and use AGOP
  Theorem 7.5 (extensions of separative real rank zero algebras are separative,
  as cited in AGOR Remark 3.2; AGOP not re-read).  Dies twice.  Separativity
  failures in `B/J_a` for a chain need not persist in the quotient by the
  closure of the union, since the witnesses move with `a`, so Zorn does not
  apply.  And AGOP 7.5 would need the ideal itself to be separative, about
  which criticality says nothing.  That is why criticality is tied to one pair.
* **Unitary lifting without cancellation.**  In the gluing step one must lift
  the discrepancy unitary `w~`, not only its K1 class.  Index-zero or
  K1-trivial unitaries of a quotient lift to the identity component
  (F4 in the artifact), but a K1-nontrivial discrepancy has to be realized by
  genuine unitaries of the corners `Q_i B_i Q_i`.  That is exactly
  K1-surjectivity of finite-type corners, which is why (K) cannot be weakened to
  injectivity alone.
* **N6: K1-surjectivity of finite corners.**  For a finite simple real rank
  zero corner without stable rank one no argument was found.  Rieffel covers
  stable rank one, Cuntz purely infinite simple algebras.  This is where (K) is
  open in the simple case.
* **Direct monoid attack.**  A refinement monoid can be wild and
  non-separative, and `opr-mixed-simple-refinement-monoid` rules out purely
  monoid-theoretic proofs even for simple algebras.  The prime reduction
  identifies the needed analytic input as unitary K-theory plus the prime case.

## N2 and N5 (recorded, no nodes)

* N2 (AGOR Section 3 remark): separativity is equivalent to the condition
  `p (+) r ~ q (+) r => p ~ q` whenever `r <~ n.p` and `r <~ n.q`, and to weak
  cancellation of all `M_n(A)`.
* N5: weak cancellation for all simple real rank zero algebras is equivalent to
  stable rank one for all finite simple real rank zero algebras.  Purely
  infinite simple algebras have weak cancellation (Cuntz, as recalled by STW).
  Infinite, not purely infinite ones fail it (`stw29-counterexample-level-two-fingerprint`).
  So the infinite, not purely infinite case is exactly Rordam's dichotomy, and
  since weak cancellation already gives the dichotomy
  (`stw29-via-finite-simple-rr0-weak-cancellation`), N5 follows from node 1
  plus the existing routes.  No separate node was written.

## Lin's lemma number

AGOR's proof of Theorem 3.1 cites "Lin, Lemma 2.2" for K1-injectivity; STW
cite "Lemma 2.1" of Lin's Pacific J. Math. paper.  The PJM scan fetched this
session (`pjm173-2`) is image-only, and no OCR was available, so neither number
was verified.  For this reason `rr0-algebras-are-k1-bijective` is stated as
bijectivity, with injectivity attributed but not imported.

## Literature consulted

* Schafhauser--Tikuisis--White, arXiv:2506.10902, TeX source (e-print
  2026-05-11), read 2026-09-16: Problem LX and the surrounding discussion.
* Ara--Goodearl--O'Meara--Raphael, arXiv:math/9906141 (Pacific J. Math. 195
  (2000)), TeX source read 2026-09-16: Section 3, Theorem 2.8, Theorem 3.1,
  Remark 3.2, the Problem.
* Ara--Goodearl--O'Meara--Pardo--Perera, arXiv:2405.06837 v2 (2024-11-20),
  abstract read 2026-09-16.
* Alahmadi--Jain--Leroy arXiv:2104.09296; Lolk arXiv:1705.04494;
  Brown--Pedersen arXiv:0708.3078: abstracts read earlier in this session,
  re-fetch failed 2026-09-16; not quoted in nodes.
* H. Lin, Pacific J. Math. 173 (1996): scan fetched, unreadable, UNVERIFIED.
* Brown--Pedersen, J. Funct. Anal. 99 (1991): permanence of real rank zero
  under matrices and corners used as known, theorem numbers UNVERIFIED.
* AGOP (Israel J. Math. 105 (1998)) Theorems 7.2, 7.5, 7.6: only as quoted by
  AGOR and STW; not read.

## Files

* `research/finite-simple-rr0-sr1-via-weak-cancellation.md`
* `research/agor-separative-rr0-algebras-are-k1-bijective.md`
* `research/agor-separative-rr0-k1-bijective-citation.md`
* `research/rr0-c-star-algebras-are-separative.md`
* `research/rr0-algebras-are-k1-bijective.md`
* `research/prime-rr0-algebras-are-separative.md`
* `research/stw99-lx-via-rr0-separativity.md`
* `research/rr0-separativity-via-lx.md`
* `research/rr0-k1-bijectivity-via-separativity.md`
* `research/rr0-separativity-from-prime-case-and-k1-bijectivity.md`
* `research/artifacts/rr0-separativity-prime-reduction-2026-09-16.md`
