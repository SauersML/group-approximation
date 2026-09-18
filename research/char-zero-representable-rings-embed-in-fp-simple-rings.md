---
rg: 2
id: char-zero-representable-rings-embed-in-fp-simple-rings
kind: claim
title: Every ring embeddable in M_D(C ⊗ Q<x_1..x_m>), C a finitely generated commutative Q-algebra or field of characteristic zero, embeds in a simple ring finitely presented as a ring (over Z)
distinct_from:
  polynomially-representable-algebras-have-fp-simple-envelopes: that is the field-K version for subalgebras of M_n(K<x> ⊗ K[t]), with finite presentation over K; this is finite presentation over Z, and C may be any finitely generated commutative Q-algebra (localizations, finite extensions, nilpotents), because the host contains Q(t_1..t_k).
  rational-function-fields-embed-in-fp-simple-rings: that is the construction of the host R_k; this is its consequence for representable rings.
  countable-char-zero-fields-embed-in-fp-simple-rings: that is the open question for countable fields that are not finitely generated, such as the algebraic closure of Q; this covers the finitely generated ones.
  char-zero-ring-boone-higman: that is the open statement for every finitely generated Q-algebra with solvable word problem; this is a large explicit class of inputs.
---

**ESTABLISHED** through `char-zero-representable-rings-embed-in-fp-simple-rings-proof`
(lane proof; refereed PASS by `gq-referee-a` (proof gaps, `gq-referee-a-char-zero-representable-rings-embed-in-fp-simple-rings.md`, 69a3cc64f) and `gq-referee-b` (`gq-referee-b-rational-function-fields-embed-in-fp-simple-rings.md`, d7414d7a4)). No priority is claimed
beyond a bounded search.

**Known and credit.** Finitely presented simple *algebras over a field* of characteristic
zero are classical: the Weyl algebra `A_1(Q)`, the Leavitt algebras `L_Q(1,n)`, and
Nekrashevych algebras are finitely presented over `Q` and simple. The point here is finite
presentation *as a ring*, that is, as a `Z`-algebra, which forces all of `Q` to be generated
by finitely many elements. This is the characteristic-zero case of the algebra form of
Boone--Higman (`algebra-boone-higman-conjecture`, with finite presentation over `Z`) for
these inputs. No printed source asks this question, so it is not an answer to an open
problem. A bounded search (web and arXiv; no MathSciNet, zbMATH or Dniester Notebook;
`gq-gq-lit-arxiv-priority.md` §§6, 9) found no prior construction.

**Statement.** Let `C` be a commutative `Q`-algebra that embeds unitally in
`M_e(Q(t_1..t_k))` for some `e` and `k`. By the proof, §2, every finitely generated
commutative `Q`-algebra and every finitely generated field of characteristic zero
qualifies. Let `D, m >= 1`.
Every subring of `M_D(C ⊗_Q Q<x_1, ..., x_m>)` embeds in the finitely presented simple
ring `M_e(R_k)` for suitable `e` and `k`, where `R_k` is the ring of
`rational-function-fields-embed-in-fp-simple-rings`.

**Special cases.** Each of the following embeds in a finitely presented simple ring:
1. every finitely generated commutative `Q`-algebra, and every commutative ring whose
   additive group is torsion-free and which is finitely generated as a ring;
2. every finitely generated field of characteristic zero, including number fields and
   function fields of varieties over them, together with all its matrix rings;
3. every finitely generated subring of `M_n(F)`, for `F` any field of characteristic zero,
   and every subring of `M_n(E)` for `E` a finitely generated field of characteristic zero;
4. every finitely generated free algebra over such a field, and tensor products of these
   with the rings in (1).

**Group consequences.** For every finitely generated field `E` of characteristic zero,
`GL_n(E)` embeds in the unit group of a finitely presented simple ring. That includes
`GL_n(Q(t))` and `GL_n` of every number field. By
`leavitt-scalar-commutators-block-fp-central-quotients`, this does not by itself give a
finitely presented simple group.

**Relation to the open questions.**
- The class shares one uniform recursive word-problem bound, like
  `polynomially-representable-algebras-have-fp-simple-envelopes`. It therefore does not
  settle `char-zero-ring-boone-higman`.
- It does settle every finitely generated input that is linear over a commutative
  `Q`-algebra.
- It is the characteristic-zero ring counterpart, over `Z` rather than over a field, of
  that repository node, and it extends the node from polynomial coefficients to arbitrary
  finitely generated commutative coefficients.
