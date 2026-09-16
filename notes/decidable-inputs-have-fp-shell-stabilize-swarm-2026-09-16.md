# Swarm note: decidable-inputs-have-fp-shell-stabilizers, 2026-09-16

Agent: swarm-decidable-inputs-have-fp-shell. Hole locked and worked:
`decidable-inputs-have-fp-shell-stabilizers` (the target itself).

## Setup

P is countably infinite, nu:P->N a bijection, E=E_nu=<V,hat(P)> the
shell group of `shell-cantor-embeddings-are-finite-germ-extensions`,
p=0^infinity, q=1*0^infinity, singularities relative to V, and

    A_1  = {e: sing(e) subset {p}, e(p)=p},
    A_12 = {e in A_1: e(q)=q},
    A_2  = {e: sing(e) subset {p,q}, e(p)=p, e(q)=q}.

The target asks, for decidable infinite f.p. P, for one nu making all
three finitely presented.

## What was proved

Outcome: a genuine reduction. For EVERY countably infinite P and EVERY
enumeration nu,

    A_1 finitely presented  ==>  A_12 and A_2 finitely presented.

Hence the three clauses of the target collapse to the single clause
"A_1 is finitely presented". Recorded as the claim
`shell-one-singularity-fp-forces-two-point-stabilizers-fp` with route
`shell-one-singularity-fp-forces-two-point-stabilizers-fp-proof`, full
proof in
`research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md`.
The target now has the route
`decidable-shell-stabilizers-via-one-singularity-clause`, requiring the
lemma and the new open hole
`decidable-inputs-have-fp-one-singularity-shell-stabilizer`.

The known necessary chain becomes

    three clauses FP <==> A_1 FP ==> Q FP <==> F_nu FP ==> R_nu FP.

(F_nu=R_nu x_Z R_nu; the last arrow is stated in
`shell-germ-group-has-index-two-fiber-product` for finitely generated P.)

## Proof sketch of the reduction

1. Compactness: a homeomorphism locally in V everywhere is in V. Hence
   A_1 is exactly the set of homeomorphisms that fix p, are locally V
   off p, and have germ at p in Q=(E)_p. The shell claim gives Q=germ_p(A_1).
2. The localization f |-> (0z |-> 0f(z), 1z |-> 1z) is an isomorphism
   from A_1 onto G_p (support in 0C), and from G_p onto G_00 (support in
   00C). Its sigma-conjugates give G_q and G_10 at q=1*0^infinity.
3. W=Fix_V({p,q}) is finitely presented and Fix_V(p) finitely generated
   (`contracting-srn-rational-stabilizers-are-fp` with trivial G).
4. Matching germs: A_2=G_p G_q K_2 and A_12=G_p <s_q> K_2, where K_2 is
   the set of V-elements equal to the identity near p and q.
5. Overlap lemma (from simplicity of V and cone swaps):
   K_2=<K(0C),K(1C),V(01C union 11C)>.
6. Presentation Gamma: presentations of G_p, G_q and W; identify the
   localized copies of Fix_V(p), Fix_V(q); impose [G_p,G_q]=1,
   [G_00,V(Y)]=1 and [G_10,V(Y)]=1 on generators.
7. Normality of the copy of K_2. The one nonformal case uses g=hu, with
   h in K(0C) agreeing with g on 01C (clopen interpolation) and u in G_00.
8. The quotient by the copy of K_2 is Q x Q (Q x Z for A_12) and maps
   isomorphically to the germ quotient. Pi is injective on the copy of
   K_2, so Gamma is isomorphic to A_2.

## Approaches tried and where each dies

* Direct lift "Q finitely presented ==> A_1 finitely presented". The
  analogous calculus for A_1=<G_p, Fix_V(p)>, with G_p isomorphic to A_1,
  is self-referential. Normality of K=union V(C minus 0^n C) needs
  commutator relations for all depths n. Those relations are s^n
  conjugates of one set, but rewriting a lifted germ generator as
  h s^n u s^-n with u in G_p already uses relations of A_1. An abstract
  version fails: the fiber product F_2 x_Z F_2 has an f.p. quotient F_2
  over ker x 1 and an f.p. diagonal subgroup mapping onto it, yet is not
  f.p. (Baumslag--Roseblade, classical, not re-fetched). The attempt
  stops here.
* Brown-criterion or complex-based presentation of A_1 for general P.
  It stops for the same reason: the neighborhood kernel is an increasing
  union of copies of V, and conjugation by lifted germ generators is not
  controlled at unbounded depth.
* Polyhedral or b-adic automaton enumerations of Z^2 as candidates. They
  were not pursued beyond sketches. A shift-normalizing enumeration is
  excluded by `one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`.
  The square spiral fails by
  `square-spiral-z2-near-shift-group-is-not-finitely-presented`. A proof
  that no enumeration of Z^2 works would need case analysis that was not
  carried out.
* Converse "A_2 FP ==> A_1 FP". It is not needed, because the target
  contains clause 1, so it was not studied.

## Literature consulted (checked 2026-09-16)

* J. Belk, J. Hyde, F. Matucci, "Finite Germ Extensions",
  arXiv:2407.03149 (v1, 3 July 2024). HTML v1 was fetched. Theorem 2.1
  gives type F_n for finite germ extensions when B acts on sing(G)^n with
  finitely many orbits and every SingFix_G(M,M') with M subset M',
  |M'|<=n, has type F_n. Appendix A gives F_infinity for stabilizers of
  finite sets of rational points in Higman--Thompson groups; this
  independently corroborates the W input. Neither the abstract nor the
  inspected statements reduce SingFix groups with two singular points to
  one.
* J. Belk, C. Bleak, F. Matucci, M. C. B. Zaremsky, "Progress around the
  Boone-Higman Conjecture", arXiv:2306.16356 (v3, 22 May 2025, survey).
  Only the abstract page was re-fetched today.
* The arXiv author listing for J. Belk was fetched. The only 2024+ items
  shown were 2407.03149 and 2409.12621 (maximality of T in V); nothing on
  presentations of singular stabilizers.
* The arXiv API keyword query timed out, then returned HTTP 429, so no
  broader 2025-2026 keyword sweep completed today. The novelty of the
  reduction lemma is therefore not certified beyond these sources and
  the graph search.

## Files

* research/shell-one-singularity-fp-forces-two-point-stabilizers-fp.md (claim)
* research/shell-one-singularity-fp-forces-two-point-stabilizers-fp-proof.md (route)
* research/decidable-inputs-have-fp-one-singularity-shell-stabilizer.md (open hole)
* research/decidable-shell-stabilizers-via-one-singularity-clause.md (reduction route into target)
* research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md (full proof)

check.sh exit 0 on all five research paths.

## Referee (2026-09-16)

Checked, line by line, the artifact
`research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md`
against the definitions in `shell-cantor-embeddings-are-finite-germ-extensions`
(and its route `shell-cantor-embedding-and-germ-proof`), the target's
three clauses, and the ESTABLISHED inputs
`contracting-srn-rational-stabilizers-are-fp` (applied with the trivial,
contracting self-similar group, so B=V) and
`thompson-v-finitely-presented-infinite-simple`.

* (F1)-(F4): compactness refinement to a level-L cone partition, the
  cone-swap normal-subgroup argument in V(X) (conjugates of a swap are
  products of disjoint swaps of cones inside X), and the overlap identity
  (au bu)=(au e)(e bu)(au e) all verified.
* Lemma 3.2: recomputed that f^(0) agrees near p with s f s^-1 (and the
  inverse with s^-1 g s), s being a bijection with s^n(1C)=C minus 0^(n+1)C;
  onto-ness of G_p -> G_00 verified.
* Lemma 4.2(a): the germ at q of e in A_2 is realized in G_q because
  sigma^-1 e sigma lies in E, fixes p, and (E)_p=germ_p(A_1) by the shell
  claim's generator description (hat(P) and s both lie in A_1). Correct.
* Lemma 4.3 (K_2 generated by K(0C), K(1C), V(Y)) and Lemma 4.4
  (g=hu, h in K(0C) agreeing with g on 01C, u in G_00): the choice m>=2,
  X=0C minus 0^(m+1)C and the nonemptiness of X minus 01C and X minus Z
  via 0^m 1C verified; u is the identity on 01C union 1C.
* Section 5: every relator holds in A_2 (disjoint supports 00C, 10C vs Y);
  (R2) makes the G_p- and W-images of V_p(0C) agree, so K(0C), K(1C) and h
  have unambiguous images; normality cases (i)-(iii) and the sigma-symmetric
  cases hold; the quotient Gamma/K_2* -> Q x Q argument (composite equals
  the joint germ map on g_a g_b) and the final injectivity argument are
  correct. Section 6 (A_12, quotient Q x Z via the infinite-order germ of
  s_q at q) verified likewise.
* No hidden hypothesis on P or nu is used; the rational stabilizer input
  needs only p, q eventually periodic.
* Duplicates: `bin/cairn search --similar` on both new claims shows no
  duplicate; distinct_from entries are accurate. The new hole has an
  '## Attempts' section. Ids are within caps (claims 56 and 57 chars).
* Literature spot-check: arXiv:2407.03149 abstract and HTML v1 re-fetched
  (Theorem 2.1 statement as quoted; the paper verifies F_infinity for
  Stab_B(M), M a finite set of rational points, B Higman--Thompson) and
  arXiv:2306.16356 version history (v3 22 May 2025) re-fetched; both match.
  Baumslag--Roseblade remains marked unverified (web search budget
  exhausted); the counterexample reasoning is only used in the Attempts
  of an open hole and in notes.

Changes made: added to the artifact's Section 7 and to this note that
F_nu=R_nu x_Z R_nu and that the arrow F_nu FP ==> R_nu FP is stated in the
graph only for finitely generated P. No mathematical change.

Verdict: sound. The lemma is a correct written proof (not Lean). The
reduction route into the target is valid; the existence problem for A_1
remains open.
