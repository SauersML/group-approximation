---
rg: 2
id: thompson-t-ppsl2z-imbert-citation
kind: route
title: Import T = PPSL_2(Z) from Haagerup--Olesen, arXiv:1609.05086, Definition 2.1, Theorem 2.2 and Proposition 2.4, cross-checked against Fossas, arXiv:1006.0508, Definition 4 and Theorem 2
target: thompson-t-is-isomorphic-to-ppsl2z
requires: []
---

**Primary source.** U. Haagerup, K. K. Olesen, *Non-inner amenability of the Thompson groups T
and V*, arXiv:1609.05086v1 [math.OA] (J. Funct. Anal. 2017). Read from the PDF text (pypdf
extraction), 2026-09-18. Section 2, "The isomorphism between T and PPSL(2, Z)":

> **Definition 2.1.** We denote by PPSL(2, Z) the group of homeomorphisms of R∪{∞} which are
> piecewise in PSL(2, Z), that is, piecewise of the form (1), and which have only finitely many
> breakpoints, all them being in Q ∪ {∞}.
> In the above definition, a breakpoint of an element g ∈ PPSL(2, Z) should be understood as a
> point x ∈ R ∪ {∞} for which there is no open neighbourhood U so that g acts on U as an element
> of PSL(2, Z).
>
> **Theorem 2.2 (Thurston).** There exists a homeomorphism φ of R ∪ {∞} onto R/Z = S1 such that
> the map Φ : PPSL(2, Z) → T given by g ↦ φ ◦ g ◦ φ−1 is an isomorphism.

Form (1) is the Möbius action "g(x) = (ax + b)/(cx + d)" of `PSL(2, Z) = SL(2, Z)/{±1}`, and the
text states "This action is faithful". The paper says it uses "a slightly modified version of
Thurston's result, given by Imbert in [12, Theorem 1.1], where T is realized as Möbius
transformations of R ∪ {∞}". Further, verbatim: "Note that PSL(2, Z) is a subgroup of
PPSL(2, Z)", and

> **Proposition 2.4.** Let Φ : PPSL(2, Z) → T be the isomorphism from Theorem 2.2, and let Λ
> denote the subgroup Φ(PSL(2, Z)) of T. Then D2 = CA = Φ(a) and C = Φ(b) are free generators of
> Λ ≅ Z2 ∗ Z3, of order 2 and 3, respectively.

**Cross-check.** A. Fossas, *PSL(2,Z) as a non distorted subgroup of Thompson's group T*,
arXiv:1006.0508v1 [math.GR]. Definition 4, verbatim: "The piecewise projective Thompson's group
T (PPSL 2(Z)) is the group of orientation preserving homeomorphisms of the real projective line
RP 1 which are piecewise PSL 2(Z) and have a finite number of non differentiable points, all of
them being rational numbers." Theorem 2, verbatim: "([11], theorem 1.1) The group PPSL 2(Z) is
isomorphic to Thompson's group T. Proof. We claim that the homomorphism Inn? : PPSL 2(Z)→ T,
given by Inn?(g) =?◦g◦ ?−1 is an isomorphism." Reference [11] is M. Imbert, *Sur l'isomorphisme
du groupe de Richard Thompson avec le groupe de Ptolémée*, Geometric Galois actions 2, LMS
Lecture Notes 243, 1997, 313-324.

The target states Definition 2.1 (with its breakpoint convention), Theorem 2.2 and
Proposition 2.4. Downstream nodes use only these and the breakpoint convention of
Definition 2.1; the Fossas statement is recorded as the `φ = ?` form only.
