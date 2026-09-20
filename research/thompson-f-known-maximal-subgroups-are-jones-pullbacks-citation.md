---
rg: 2
id: thompson-f-known-maximal-subgroups-are-jones-pullbacks-citation
kind: route
title: Import of Golan–Sapir (arXiv:1508.00493) on the maximal subgroup Psi^{-1}(Jones) and Golan (arXiv:2209.03244) on maximal Jones subgroups F_p
target: thompson-f-known-maximal-subgroups-are-jones-pullbacks
requires: []
---

**Sources.**
- [GS1] G. Golan and M. Sapir, *On subgroups of R. Thompson's group F*, arXiv:1508.00493,
  Trans. Amer. Math. Soc. 369 (2017).
- [G] G. Golan, *On maximal subgroups of Thompson's group F*, arXiv:2209.03244 (revised version,
  source file `MaximalSubgroupsRevisedArxiv.tex`).
- [GS] G. Golan and M. Sapir, *On Jones' subgroup of R. Thompson group F*, arXiv:1501.00724,
  J. Algebra 470 (2017).

**How it was read.** The arXiv TeX sources of [GS1] and [G] were downloaded on 2026-09-20
(`arxiv.org/e-print/1508.00493`, `arxiv.org/e-print/2209.03244`) and read locally. [GS] was not
reopened here. Item 1 for `n = 2` is also recorded, from [GS] directly, in
`jones-subgroup-is-stabilizer-of-odd-digit-sum-dyadics-citation`. For general `n`, item 1 is taken
from its restatement in [G].

**Verbatim.**
- Item 1, [G] Lemma `lem:stabilizers`, attributed to [GS, Theorem 5.11]: "Let n ≥ 2. For each
  i=0,…,n−1, let S_i be the set of all dyadic fractions such that the sum of digits in their finite
  binary representation is i modulo n. Then \vec F_n = ∩_{i=0}^{n−1} Stab(S_i)."
- Item 2, [GS1] Theorem labelled `t:11` (recorded elsewhere in the graph as Theorem 3.15): "Let
  Ψ: F → G be the isomorphism taking x_i to y_i, i=0,1 (see Lemma iso). Then H=Ψ^{-1}(\vec F) is a
  maximal subgroup of infinite index in F and H does not stabilize any x∈(0,1)." In its proof,
  "y_0=x_0x_2 and y_1=x_1x_2". [GS1] Corollary `cor`: "\vec F is a maximal subgroup of infinite
  index inside G". The remark after it identifies `G` with "the subgroup G' of F consisting of
  functions whose slope at 1 is of the form 2^{2n}". The introduction says "there are exactly three
  subgroups of F containing \vec F".
- Item 3, [G] Theorem `thm: main2`: "The only subgroups of Thompson's group F which strictly
  contain \vec F_p are F_{1,p} and F." [G] Corollary `cor:max Jones`: "For every prime number p,
  Thompson's group F has a maximal subgroup isomorphic to Jones' subgroup \vec F_p." Its proof uses
  "Since F_{1,p} is isomorphic to F". [G] §8 names the maximal subgroup as "Let ν: F_{1,p}→F be an
  isomorphism. Then ν(\vec F_p) is a maximal subgroup of F". Pairwise non-isomorphism: the
  introduction of [G] says "there is an infinite family of pairwise non-isomorphic maximal
  subgroups of infinite index in F".

**Equality `∩_i Stab(S_i) = Stab(c_n)`.** This is immediate: `c_n ∘ g^{-1} = c_n` says exactly
that `g` maps each colour class `S_i` onto itself.

**Also recorded in [G], not used here.** Every maximal subgroup of infinite index is closed
([G] Theorem `thm:int1`). Every finitely generated proper subgroup lies in a finitely generated
maximal subgroup ([G] Theorem `thm:int4`). The revision remark says that "Problem p1 was recently
solved in the affirmative by the author [G23]": for every `n` there is a maximal subgroup with
exactly `n` orbits on the dyadics.
