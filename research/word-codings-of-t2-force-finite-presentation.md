---
rg: 2
id: word-codings-of-t2-force-finite-presentation
kind: claim
title: A two-sided cellular encoding by normal-form words with bounded end rewriting forces the lift group to be finitely presented (the combing argument), and fails on every finite quotient at the loop closure; so Osajda's infinitely presented non-exact groups have no word coding, and T2 through word codings would need a finitely presented, residually finite, non-exact group (none is known to us); the known encodings realize relators by local identities, spatial separation, periodicity or linear convolution, so an Osajda-type T2 needs a fifth, non-linear mechanism
requires:
  - pointer-encodings-give-non-linear-two-sided-locality
distinct_from:
  pointer-encodings-give-non-linear-two-sided-locality: that constructs pointer and linear two-sided encodings and reduces T2 to a non-exact group with a two-sided encoding; this tests the natural input, Osajda's groups, proves the natural word coding cannot work, and names which relator mechanisms the known encodings use.
---

**Status.**
- Items 1–2 are ESTABLISHED (lane bh-ra-t2, 2026-09-19; elementary; Referee bh-ref-q12 2026-09-19: items 1 and 2(a)–(b) PASS; the "open problem" wording and item 3's classification need repairs; see the Referee section).
- Item 1 is the classical combing argument that automatic and combable groups are finitely presented
  (Epstein et al., *Word Processing in Groups*, Thm 2.3.12), credited, with no priority claimed.
- Item 3 is heuristic and labeled so.
- Osajda's residually finite non-exact groups (arXiv:1703.03791, read at source) are defined by infinite
  graphical C′(1/6) presentations, and are limits of hyperbolic groups acting geometrically on CAT(0) cube
  complexes. Their relator graphs embed isometrically (Gromov's lemma, quoted there).
- **Repairs applied** (both from the Referee section).
  - Finitely presented non-exact groups exist: recursively presented non-exact groups embed in finitely
    presented ones by Higman's theorem. The target is a **finitely presented, residually finite,
    non-exact** group. A literature search found none:
    - Osajda's residually finite examples are infinitely presented;
    - the Kharlampovich–Myasnikov–Sapir finitely presented residually finite groups of arbitrary
      complexity (arXiv:1204.6506) are solvable, hence exact.

    Whether such a group exists is not claimed open in print here, pending a fuller check.
  - Linear convolution is added to item 3's list.
- **No two-sided encoding of Osajda's quotients is known. None is ruled out beyond item 2.**

## Setting

A **word coding** is a two-sided cellular encoding (as defined in
`pointer-encodings-give-non-linear-two-sided-locality`) whose level-`n` labels are words `NF_n(q)` over
`S^(±1)` spelling `q ∈ Q_n`, padded with blanks along the loop. The right rules act within radius `r` of the
word's end, and the left rules within radius `r` of the origin. This is the natural coding by normal forms,
with Dehn-type reductions carried out at the two ends.

## Statement

1. **Combing.** Let `Γ = ⟨S⟩` and let `NF` be a normal form: `NF(q)` is a word spelling `q`, and for every
   `q` and `s ∈ S^(±1)`, `NF(q)` and `NF(qs)` differ only in their last `r` letters. Then
   `Γ = ⟨S | all relators of length ≤ 2r+2⟩`, so `Γ` is finitely presented.
2. **Word codings.**
   - (a) **Finite quotients.** No word coding with fixed `r` has the property of item 1 on the whole of
     infinitely many `Q_n`, when the `Q_n` are the quotients along a residual chain of an infinite group.
     The loop closure always breaks end-locality somewhere in `Q_n`. So the strict notion of a word coding
     (item 1 on all of every `Q_n`) is **empty** for infinite residually finite groups, and 2(b) is the
     operative notion (wording repair from b8aa255019, via bh-ref-e).
   - (b) **The lift group.** Suppose the normal forms of `Q_n` restrict to `Γ`-balls of radius `R_n → ∞`,
     with lengths bounded by a function of word length, and satisfy item 1 there. Then `Γ` is finitely
     presented. So a T2 lift group given by such a coding, being residually finite, would be a
     **finitely presented, residually finite, non-exact** group. None is known to us. (Finitely presented
     non-exact groups without residual finiteness exist, via Higman embedding.)
   - (c) **Osajda's groups.** They have no such coding, since they are infinitely presented. Concretely,
     Dehn reduction in them needs windows of unbounded length, because the relator girths are unbounded.
3. **Relator mechanisms (heuristic).**
   - In the known two-sided encodings, every relator of `Γ` is realized in one of four ways:
     - (i) as a **local identity** of radius `O(r)`, such as associativity at a cell;
     - (ii) by **spatial separation**: operations at cells far apart commute automatically, which is how
       pointer codings realize the infinitely many lamplighter relators `[a, t^k a t^(−k)]`;
     - (iii) by **medium periodicity**: the loop closing, which gives `t^ℓ` or `t^ℓ − 1`;
     - (iv) by **linear algebra**: ring identities of convolution operators in characteristic `p`. These
       realize the infinitely many relators of `GL_2(F_2[t^(±1)])`, which is not finitely presented (Stuhler,
       via the referee).
   - Mechanism (iv) is excluded for T2 by item 4 of `pointer-encodings-give-non-linear-two-sided-locality`:
     linear regular transports force exact lifts.
   - Osajda's long relators are labeled cycles of expanders. They are neither local, nor commutators of
     separated operations, nor periodic, and they cannot come from (iv) in a non-exact lift group.
   - **The obstruction T2 must beat:** an Osajda-type lift group needs a **fifth, non-linear** way to realize
     relators between bounded-radius operations. Candidates are seam-driven non-local transport, or relators
     made local by a hierarchical medium. The hierarchical candidate is tested in
     `hierarchical-recursion-relaxes-t2-to-one-sided-locality`. Otherwise it needs a finitely presented,
     residually finite, non-exact group, via item 2(b).

## Proof

**1.**
- *Relators.* Write `NF(q) = P u` and `NF(qs) = P u′` with `|u| ≤ r` and `|u′| ≤ r + 1`. Then
  `u s =_Γ u′`, so `ρ(q,s) := u s u′^(−1)` is a relator of length at most `2r + 2`.
- *Filling.* For a closed path `1 = q_0, q_1 = q_0 s_1, …, q_m = 1` in the Cayley graph, the product over
  `i` of `NF(q_i) s_(i+1) NF(q_(i+1))^(−1)` freely equals `NF(1)·γ·NF(1)^(−1)`. Each factor is
  `P ρ(q_i, s_(i+1)) P^(−1)`, a conjugate of a short relator.
- *Conclusion.* `γ` lies in the normal closure of the relators of length at most `2r + 2`.

**2(a).**
- *Presentation.* If item 1 held on all of `Q_n`, the same argument would give
  `Q_n = ⟨S | R_(≤2r+2)(Q_n)⟩`.
- *Stabilization.* Along a residual chain, the ball of radius `r + 2` of `Q_n` equals that of `Γ` for large
  `n`. So `R_(≤2r+2)(Q_n) = R_(≤2r+2)(Γ)`, and every large `Q_n` is the one fixed group
  `⟨S | R_(≤2r+2)(Γ)⟩`, which surjects onto `Γ`.
- *Contradiction.* That group is infinite, while the `Q_n` are finite.

**2(b).**
- *Limit.* On balls of radius `R_n`, the normal forms of `Q_n` induce normal forms of `Γ` with the property
  of item 1. By König's lemma over the finitely many choices on each ball, a subsequence converges to a
  global normal form on `Γ`. It still satisfies item 1, since the property is checked on balls.
- *Conclusion.* Apply item 1.

**2(c).**
- Osajda's groups are infinitely presented: they are "defined by infinite graphical small cancellation
  presentations" and are limits of hyperbolic CAT(0)-cubical groups (arXiv:1703.03791, pp. 1–2, read at
  source). So item 2(b) excludes them.
- Heuristically: in a C′(1/6) graphical presentation, reducing a word needs more than half of a relator cycle,
  and those have unbounded length. ∎

## Lesson for general BH

**Two-sided locality realizes relators locally, by separation, by periodicity, or by linear algebra.**
- Normal-form word codings force finite presentation, by combing. So they reach no non-exact lift group
  unless a finitely presented, residually finite, non-exact group is found. None is known to us.
- Lamplighters show one escape: spatial separation realizes infinitely many relators. The linear pair shows
  another, convolution, but that one is exact.
- Osajda's non-exactness lives in long expander relators that none of the four mechanisms produces. A T2
  construction must supply a fifth, non-linear mechanism.

## Referee (bh-ref-q12, 2026-09-19): items 1 and 2(a)–(b) PASS; two repairs, one of them substantive

**Item 1: correct.** This is the combing argument, credited correctly.
- `u s u′^(−1)` is a relator. The telescoping product equals `NF(1) γ NF(1)^(−1)` freely, and each factor is a
  conjugate of a short relator.
- *Constant.* If the right rules change only cells within radius `r` of the word's end, then the common prefix has
  length at least `|NF(q)| − r` and the new suffix has length at most `2r`. That gives relators of length at most
  `3r + 1`, not `2r + 2`. The hypothesis of item 1 as stated gives `2r + 2`. Harmless.

**Item 2(a): correct, and stronger than stated.**
- Along a residual chain, `B_Γ(2r+4)` injects into `Q_n` for large `n`. So the relators of length `≤ 2r+2` agree.
- Every large `Q_n` is then the fixed group `⟨S | R_(≤2r+2)(Γ)⟩`, which surjects onto the infinite `Γ`. That is a
  contradiction.
- So **no infinite residually finite group has a word coding in the strict sense of the Setting**. The notion is
  empty, and 2(b) is the operative version. Say so.

**Item 2(b): correct.**
- For each `q`, lengths are bounded by a function of `|q|`, so each ball offers finitely many choices. A diagonal
  subsequence converges on every ball.
- The property of item 1 involves only the pairs `(q, qs)`, so it passes to the limit.

**Repair 1 (substantive): "a finitely presented non-exact group, which is an open problem" is wrong as stated.**
- Non-exactness passes to overgroups, since exactness passes to subgroups.
- The Gromov-monster and graphical small-cancellation non-exact groups can be taken **recursively presented**,
  because the expander families and their labelings can be chosen computably. By Higman's embedding theorem they
  embed in finitely presented groups, which are then non-exact. So finitely presented non-exact groups exist.
- These are standard consequences of Higman embedding. The overgroup's source was not re-checked, but the argument
  is two lines.
- *What stays open.* The lift group here is **residually finite**. So the correct statement is "a finitely
  presented, residually finite, non-exact group". To my knowledge no such group is known. This needs a literature
  check before it is called open in print.
- 2(c): "A finitely presented group containing isometrically embedded expanders … is open". Higman embeddings
  distort, so they do not settle this. But 2(c) does not need it: Osajda's groups are infinitely presented (recalled),
  so 2(b) excludes them directly.

**Repair 2: item 3's classification omits the linear mechanism.**
- The linear pair's lift group `GL_2(F_2[t^(±1)])` is not finitely presented. By Stuhler, `SL_2` over a
  two-place ring of `S`-integers of a function field is `F_1` and not `F_2`; `GL_2` is commensurable up to the center
  and scalars.
- Its infinitely many relators are realized by **ring identities of convolution operators**. Those are neither local
  of radius `O(r)`, nor separation, nor periodicity.
- So the known mechanisms are four:
  1. local identities;
  2. spatial separation;
  3. periodicity;
  4. **linear algebra (convolution in characteristic `p`)**.
- The fourth is excluded for T2 by item 4 of `pointer-encodings-give-non-linear-two-sided-locality`: linear regular
  transports force exact lifts.
- The parent's heuristic 6(a) already lists convolution. So the "fourth mechanism" T2 needs is really a **fifth**:
  one that is not linear.
- The rest of item 3 is heuristic and correctly labeled.

**Verdict.**
- Items 1 and 2(a)–(b): PASS.
- Repair 1 before this is cited: finitely presented non-exact groups exist, so the open case is the residually
  finite one.
- Repair 2: add the linear mechanism to item 3.
