---
rg: 2
id: gordon-free-products-of-three-groups-have-normal-rank-above-one
kind: claim
title: A free product of three or more nontrivial groups is never the normal closure of one element
distinct_from:
  wiegold-problem-has-finitely-presented-counterexamples: that is settled with two left-orderable factors; this asks for normal rank above one with three or more arbitrary factors, torsion included, where no orderability is available.
  torsion-free-free-products-have-normal-rank-above-one: that is the two-factor torsion-free question; this has at least three factors of any kind, while two factors with coprime torsion can have normal rank one.
---

**OPEN.** This is C. McA. Gordon's conjecture, as stated secondhand by Chen–Lodha,
arXiv:2510.26073 v2, `wiegold.tex`.
- **l.218:** "Most known approaches towards the Wiegold problem involve showing
  that a free product G=⋆_{i∈I} A_i of nontrivial groups A_i has normal rank
  greater than 1, under suitable assumptions."
- **l.220:** "For |I|≥3, an unsolved conjecture of Cameron Gordon [Gordon83,
  Conjecture 9.5] predicts that such a free product always has normal rank
  greater than 1. When the factors are finite cyclic groups, this is the
  Scott--Wiegold conjecture, confirmed by James Howie [How02]. It seems tempting to
  make this work for a free product of three (even finite) perfect groups, but no
  one has succeeded."

**Primary sources, not read.**
- C. McA. Gordon, *Dehn surgery and satellite knots*, Trans. Amer. Math. Soc. 275
  (1983), 687–708.
- J. Howie, *A proof of the Scott–Wiegold conjecture on free products of cyclic
  groups*, J. Pure Appl. Algebra 173 (2002), 167–176.

**Settled cases.**
- **Finite cyclic factors:** Howie, as quoted above.
- **Two factors with nontrivial left-orderable quotients:**
  `left-orderable-free-products-have-normal-rank-above-one` via
  `normal-rank-one-free-products-need-cyclic-abelianization`.
- **Two factors whose abelianizations have non-cyclic direct sum:** the same
  constraints claim.
- **Contrast with two factors:** two nontrivial finite perfect factors can have
  normal rank one (`finite-perfect-free-pairs-have-normal-rank-one`), so the
  three-factor hypothesis matters.

## Attempts

1. **Quotient constraints** (solve-wiegold, 2026-09-13; established in
   `normal-rank-one-free-products-need-cyclic-abelianization`). A counterexample
   must meet two conditions.
   - **Abelianizations.** Either they are finite cyclic of pairwise coprime orders,
     or exactly one factor has abelianization `Z` over perfect others whose free
     product is neither torsion-free nor hyperlinear.
   - **Orderable quotients.** At most one factor has a nontrivial left-orderable
     quotient.

   The smallest untouched case is three finite perfect groups, e.g. `A_5 * A_5 * A_5`.
2. **Conjugation-parameter degree** (solve-wiegold, observation only, details not
   written out). Let the factors map to `SO(3)`, and conjugate the factor images
   independently. On each one-parameter slice, `u ↦ u a u^{-1}` has degree
   `1 + (−1) = 0`, and it is trivial on `π_1`. So the evaluation of `w` shows no
   degree or mod-2 surjectivity obstruction. A Gerstenhaber–Rothaus-style solution
   of `w = 1` would need another mechanism, since there is no free letter.
