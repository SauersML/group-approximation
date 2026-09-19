---
rg: 2
id: word-codings-of-t2-force-finite-presentation
kind: claim
title: A two-sided cellular encoding by normal-form words with bounded end rewriting forces the lift group to be finitely presented (the combing argument), and fails on every finite quotient at the loop closure; so Osajda's infinitely presented non-exact groups have no word coding, and T2 through word codings would produce a finitely presented non-exact group; lamplighters escape because pointer codings realize their infinitely many relators by spatial separation, which is the mechanism an Osajda-type T2 would have to replace
requires:
  - pointer-encodings-give-non-linear-two-sided-locality
distinct_from:
  pointer-encodings-give-non-linear-two-sided-locality: that constructs pointer and linear two-sided encodings and reduces T2 to a non-exact group with a two-sided encoding; this tests the natural input, Osajda's groups, proves the natural word coding cannot work, and names which relator mechanisms the known encodings use.
---

**Status.**
- Items 1–2 are ESTABLISHED (lane bh-ra-t2, 2026-09-19; elementary; not reviewed).
- Item 1 is the classical combing argument that automatic and combable groups are finitely presented
  (Epstein et al., *Word Processing in Groups*, Thm 2.3.12), credited, with no priority claimed.
- Item 3 is heuristic and labelled so.
- Recalled, not re-proved: Osajda's residually finite non-exact groups (Acta Math. 2020) are graphical
  C′(1/6) quotients whose relator graphs have girth tending to infinity and embed isometrically. They are
  not finitely presented; whether a finitely presented non-exact group exists is open.
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
     The loop closure always breaks end-locality somewhere in `Q_n`.
   - (b) **The lift group.** Suppose the normal forms of `Q_n` restrict to `Γ`-balls of radius `R_n → ∞`,
     with lengths bounded by a function of word length, and satisfy item 1 there. Then `Γ` is finitely
     presented. So a T2 lift group given by such a coding would be a finitely presented non-exact group,
     which is an open problem.
   - (c) **Osajda's groups.** They have no such coding, since they are infinitely presented. Concretely,
     Dehn reduction in them needs windows of unbounded length, because the relator girths are unbounded.
3. **Relator mechanisms (heuristic).**
   - In the known two-sided encodings, every relator of `Γ` is realized in one of three ways:
     - (i) as a **local identity** of radius `O(r)`, such as associativity at a cell;
     - (ii) by **spatial separation**: operations at cells far apart commute automatically, which is how
       pointer codings realize the infinitely many lamplighter relators `[a, t^k a t^(−k)]`;
     - (iii) by **medium periodicity**: the loop closing, which gives `t^ℓ` or `t^ℓ − 1`.
   - Osajda's long relators are labelled cycles of expanders. They are neither local, nor commutators of
     separated operations, nor periodic.
   - **The obstruction T2 must beat:** an Osajda-type lift group needs a fourth way to realize relators
     between bounded-radius operations. Candidates are seam-driven non-local transport, or relators made
     local by a hierarchical medium. Otherwise it needs a finitely presented non-exact group, via item 2(b).

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
- A finite presentation of Osajda's group would be a finitely presented group containing isometrically
  embedded expanders. The existence of such a group is open.
- Directly: in a C′(1/6) graphical presentation, reducing a word needs more than half of a relator cycle,
  and those have unbounded length. ∎

## Lesson for general BH

**Two-sided locality realizes relators only locally, by separation, or by periodicity.**
- Normal-form word codings force finite presentation, by combing. So they reach no non-exact group short of
  answering Gromov-type existence for finitely presented non-exact groups.
- Lamplighters show the escape: spatial separation realizes infinitely many relators.
- Osajda's non-exactness lives in long expander relators that none of the three mechanisms produces. A T2
  construction must supply a fourth mechanism.
