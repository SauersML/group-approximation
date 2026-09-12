# Assessment: Arulseelan–Hanson "Every AW*-algebra is normal" and the quasitrace problem

Import and assessment by lane `quasitrace`, 2026-09-12, for STW Problem I
(`stw99-problem-i-quasitraces-are-traces`, Kaplansky's quasitrace problem).

**Source.** Aareyan Arulseelan and James Hanson, *Every AW\*-Algebra is Normal*,
arXiv:2609.10218v1, submitted 9 September 2026. Text extracted from the PDF of v1
(pages 1–4) on MSI (poppler `pdftotext`) and read 2026-09-12. Statements below are
quoted or paraphrased from that text; the proofs were not re-derived.

## Definitions and results, as stated

- **Definition 1.2 (monotone complete).** A C\*-algebra `A` is monotone complete
  if every norm-bounded upward-directed family in `A_sa` has a least upper bound
  in `A_sa`.
- **Conjecture 1.3 (monotone completeness conjecture).** Every AW\*-algebra is
  monotone complete. "The conjecture has a clear affirmative answer for
  W\*-algebras and for commutative AW\*-algebras."
- **Definition 1.4 (normal, Wright).** An AW\*-algebra `A` is normal if for every
  upward-directed family `(p_i)` in `Proj(A)`, the projection-lattice join
  `⋁ p_i` is the least upper bound of the family in the self-adjoint order `A_sa`;
  equivalently, `a ∈ A_sa`, `a ≥ p_i` for all `i`, implies `a ≥ ⋁ p_i`.
- **Theorem A.** Every AW\*-algebra is normal. (Resolves Wright's 1980 question.)
- **Berberian [Ber83, Theorem 3].** An AW\*-algebra is a W\*-algebra iff it is
  normal and has a large W\*-corner ("large" = a faithful projection `p`, one with
  central support `1`, such that `pAp` is a W\*-algebra).
- **Corollary 1.5.** An AW\*-algebra `A` is a W\*-algebra iff it has a large
  W\*-corner. (Theorem A removes the normality hypothesis from Berberian.)
- **Theorem B (equiconsistency).** There is a model of ZFC with a non–monotone-complete
  AW\*-algebra iff there is a model of ZFC with a non–monotone-complete AW\*-*factor*.
  Contrapositive: a ZFC proof that every AW\*-factor is monotone complete already
  proves Conjecture 1.3 in general.

Prior status the paper records: Wright [W80] proved every AW\*-algebra of *finite
type* is normal; **Saitô–Wright 1991 [SW91, Cor 4.7] proved every AW\*-*factor* is
normal** (the paper's Theorem 2.13); Ara–Mathieu [AM08] proved every σ-finite
AW\*-algebra normal. Both A-H theorems use Ozawa's Boolean-valued factor
representations.

## Bearing on Kaplansky's quasitrace problem

The relevant Cairn bridge is Gow's four-way equivalence
(`stw01-kaplansky-2q-pedersen-retract-equivalence`,
`stw01-gow-four-way-equivalence-citation`, arXiv:2601.04431v2, Thm 4.11):

> **2Q** (every bounded 2-quasitrace on a unital C\*-algebra is a trace)
> **⟺ every type II₁ AW\*-factor is a type II₁ W\*-factor.**

So the entire quasitrace problem sits on the *factor* case. Combining Gow with
Berberian and A-H Corollary 1.5:

> **2Q ⟺ every type II₁ AW\*-factor has a large W\*-corner**
> (a faithful projection `p` with `pFp` a W\*-algebra).

**A-H Theorem A does not advance Kaplansky's problem.** The reformulation above is
available without it: at the factor bottleneck, normality was already the 1991
Saitô–Wright theorem, so Berberian's criterion already reads "II₁ AW\*-factor is
W\* ⟺ large W\*-corner" since 1991. Theorem A's novelty is the *non-factor* case
and the removal of normality for general AW\*-algebras, neither of which touches
the II₁-factor crux to which `stw01-separable-simple-reduction` and Gow reduce
Problem I.

**The crux is W\*-ness, which is strictly stronger than monotone completeness.**
A W\*-factor is monotone complete, but monotone completeness does not conversely
force W\*: wild monotone-complete factors that are not W\*-algebras exist
(Takenouchi- and Dyer-type type III examples; Saitô–Wright's generic-dynamics
constructions). Hence:

- Kaplansky's 2Q is *strictly stronger* than "every II₁ AW\*-factor is monotone
  complete" (Conjecture 1.3 for factors). A resolution of Conjecture 1.3 would not
  by itself resolve 2Q; one additionally needs the monotone-complete II₁
  AW\*-factor to carry a separating family of normal states (equivalently, a large
  W\*-corner).
- A-H Theorem B is therefore a statement about the weaker (monotone-completeness)
  layer, and does not reduce 2Q to a factor-only assertion beyond what Gow already
  gives.

**Net.** Import A-H as a tool on the AW\*-side and record the corner reformulation,
but do not expect it to close, or measurably narrow, Kaplansky's quasitrace
problem. The open ingredient stays: a II₁ AW\*-factor must be genuinely W\*, not
merely monotone complete or normal.
