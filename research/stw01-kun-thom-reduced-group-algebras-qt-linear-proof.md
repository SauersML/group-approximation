---
rg: 2
id: stw01-kun-thom-reduced-group-algebras-qt-linear-proof
kind: route
title: Property A permanence plus Haagerup's theorem for the Kun--Thom groups
target: stw01-kun-thom-reduced-group-algebras-are-qt-linear
requires: []
---

Statements were read from Willett, *Some notes on Property A*,
arXiv:math/0612492v2, which proves or cites each one. The primary sources were not
re-read.

1. **The kernel.** `R = F_q[x_1^(+-1),...,x_d^(+-1)]` lies in the field
   `F = F_q(x_1,...,x_d)`. So `EL_r(R)` is a countable subgroup of `GL_r(F)` and
   has property A (Guentner–Higson–Weinberger 2005; Willett §2.3 list).
2. **The quotient.** `SL_d(Z) <= GL_d(Q)` has property A, for the same reason.
3. **`G` and `Gamma`.** `1 -> EL_r(R) -> G -> SL_d(Z) -> 1` is an extension of
   property A groups, so `G` has property A (Willett Theorem 2.3.6,
   Dadarlat–Guentner). Subgroups inherit property A (Willett Lemma 2.3.4), so
   `Gamma` has it.
4. **The wreath `W`.** `1 -> direct_sum_(G/Gamma) Z/2Z -> W -> G -> 1`, and the
   kernel is abelian, hence amenable, hence property A. So `W` has property A
   (Theorem 2.3.6).
5. **The double `D`.** `G *_Gamma G` is an amalgam of property A groups over a
   common subgroup, so it has property A (Willett Theorem 2.3.11).
6. **Exactness.** A countable discrete group has property A iff its reduced
   C*-algebra is exact (Guentner–Kaminker, Ozawa 2000; Willett Theorem 4.3.9).
   C*-subalgebras of exact C*-algebras are exact.
7. **Linearity.** Every bounded 2-quasitrace on an exact C*-algebra is a trace
   (Haagerup, C. R. Math. Acad. Sci. Soc. R. Can. 36 (2014)). A quasitrace on a
   quotient pulls back to a quasitrace on the algebra, so quotients inherit
   linearity.
8. **Finite abelianization.** `G` has property (T) (Kun--Thom Theorem E), so
   `G^ab` is finite.
   - `W^ab` is `(direct_sum_(G/Gamma) Z/2Z)_G` plus `G^ab`. The coinvariants of a
     transitive permutation module are `Z/2Z`, so `W^ab` is finite.
   - `D^ab` is a quotient of `G^ab + G^ab`, so it is finite.

   A group with finite abelianization has no quotient `Z`, hence no quotient
   `F_2`.
9. **Full algebras.** For a subgroup `H <= K` of a discrete group, `C*(H)` embeds
   in `C*(K)`. So `C*(F_2)` sits in `C*(G)`, `C*(W)` and `C*(D)`, and each of these
   is non-exact.

Trust surfaces:
- the published permanence theorems, read through Willett's notes;
- Kun--Thom Theorem E (arXiv:2608.06222v3), read in
  `research/artifacts/review-surjunctive-nonsofic-2026-09-12.md`;
- Haagerup's theorem.
