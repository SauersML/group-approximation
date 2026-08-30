---
title: Nuclear C*-algebras, 99 problems --- ingestion dossier (2026-08-27)
---

Source: Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).  Authors Christopher Schafhauser, Aaron Tikuisis, Stuart White.
Problem numbering is the paper's (Roman numerals I--XCIX).

## Problems ingested and the nodes carrying them

| Problem | Statement (paper's wording, abridged) | Node |
|---|---|---|
| I | If τ is a bounded quasitrace on a C*-algebra, must τ be a trace? | stw99-problem-i-quasitraces-are-traces |
| VII (Blackadar--Kirchberg) | Is every separable nuclear stably finite C*-algebra quasidiagonal? | stw99-problem-vii-blackadar-kirchberg |
| IX(1) | Separable nuclear C*-algebra with a faithful trace: is it quasidiagonal? | stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal |
| X(1) | Are amenable traces on C*-algebras necessarily quasidiagonal? | stw99-problem-x1-amenable-traces-quasidiagonal |
| X(2) | Is the hyperfinite II₁ factor quasidiagonal? | stw99-problem-x2-hyperfinite-factor-quasidiagonal |
| XC | C*-simple G: does C*_r(G) have strict comparison w.r.t. its unique trace? | stw99-problem-xc-cstar-simple-strict-comparison |
| XCI (Robert) | Is C*_r(F₂) selfless? Is C*_r(G) selfless for every C*-simple G? | stw99-problem-xci-cstar-simple-selfless |
| XCIII | Does C*_r(F₂) ⊗ 𝒵 have property (SI)? | stw99-problem-xciii-free-group-jiang-su-si |
| XCIV | Is the hyperfinite II₁ factor separably 𝒵-stable? | stw99-problem-xciv-hyperfinite-factor-separably-z-stable |
| VIII | Is every separable exact quasidiagonal C*-algebra AF-embeddable? | stw99-problem-viii-exact-quasidiagonal-af-embeddable |
| IX(2) | Exact with faithful quasidiagonal trace: AF-embeddable? | stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable |
| LXXXII | Nuclear dimension across arbitrary C*-extensions | stw99-problem-lxxxii-nuclear-dimension-extensions |
| XCV (first part) | Cu(A)=Cu(B)=Cu(Z) should force Cu(A tensor B)=Cu(Z) | stw99-problem-xcv-cu-z-tensor |
| XCV (general part) | Minimal tensor products of pure C*-algebras should be pure | stw99-problem-xcv-pure-tensor-permanence |
| XCVI (simple) | Every unital simple separable C*-algebra is singly generated | stw99-problem-xcvi-simple-single-generation |
| XCVI (nowhere scattered) | Every unital separable nowhere scattered C*-algebra is singly generated | stw99-problem-xcvi-nowhere-scattered-single-generation |
| XCVII | Every unital simple separable nuclear C*-algebra is singly generated | stw99-problem-xcvii-nuclear-single-generation |
| LXXXIV | Nuclear dimension of amenable group C*-algebras | stw99-problem-lxxxiv-nuclear-dimension-amenable-groups |
| LXXXVI | Eckhardt--Wu: finite decomposition rank iff polynomial growth | stw99-eckhardt-wu-decomposition-rank-conjecture |
| LXXXVII | dim_nuc of the uniform Roe algebra vs asymptotic dimension | stw99-problem-lxxxvii-roe-algebra-nuclear-dimension |
| LXVI | Unital CAR embedding in a simple infinite algebra with a finite image projection | stw99-problem-lxvi-car-embedding-with-finite-projection |
| LXXIII | Global Glimm halving by one square-zero ideal generator | problem-lxxiii-global-square-zero-cover |
| LXXIV | Infinite nonzero projections in a simple unital algebra force pure infiniteness | stw99-problem-lxxiv-infinite-projections-purely-infinite |
| LXXVI | Every pure C*-algebra is Cuntz-semigroup regular | stw99-problem-lxxvi-pure-implies-cu-regular |

## Reductions recorded as routes, with the sentence in the paper that asserts them

* X(1) ⟹ IX(1): "If Problem X(1) below ... has a positive answer, it would imply a positive answer to Problem IX(1)."
* VII ⟹ IX(1): faithful traces are stably finite (elementary).
* X(1) ⟹ X(2): τ_R is amenable (Connes' Følner condition, Brown Thm 3.1.7(3)); "Using that R has a unique trace and the trace is faithful, this is equivalent to Problem X(2)."
* XCI ⟹ XC: Robert, Selfless C*-algebras, Theorem 3.1.
* XC ⟹ unique quasitrace for C*_r(G): footnote 152 (Thiel).
* XCIII ⟺ unique quasitrace on the central sequence algebra: discussion after Problem XCIII.
* (SI) for R ⟹ XCIV: remark after Problem XCIV.
* AGKP Theorem B (Addendum 25.1): acylindrically hyperbolic + rapid decay + no nontrivial finite normal subgroup ⟹ selfless.

## The repository's contribution to Problem X(1)

The literal finitely presented group E of non_mf_groups_exist.tex is sofic
(Lean: LiteralSoficAssembly.markedGroup_isSofic) and has a central involution
`mark ≠ 1` killed by every operator-norm corona representation (Lean:
LiteralNonMFEndpoint.literal_mark_eq_one_in_unitaryCorona).  So the canonical
trace τ_E of C*(E) is a hyperlinear trace (SoficHyperlinearBridge) that is not
an MF trace, hence not a quasidiagonal trace (LiteralTraceConsequence,
QuasidiagonalTraceModel.toMFTraceModel).  Brown's Theorem 4.1.9 identifies
amenability of τ_E with Kirchberg's factorization property of E.  Hence:

    E has the factorization property  ⟹  Problem X(1) is false.

The factorization property of E is open (literal-group-factorization-property).
It is not implied by hyperlinearity: Kirchberg (Math. Ann. 299 (1994)) shows
Kazhdan groups with the factorization property are residually finite, so
"hyperlinear ⟹ factorization property" would make every infinite simple
Kazhdan group non-hyperlinear.

## Literature cited (true facts, credited; nothing reproved here)

* N. P. Brown, Invariant means and finite representation theory of C*-algebras, Mem. AMS 184 (2006), no. 865: Thm 3.1.6, Thm 3.1.7, Def 3.3.1, Prop 4.1.3, Prop 4.1.4, Thm 4.1.9, Prop 4.1.12.
* E. Kirchberg, Discrete groups with Kazhdan's property T and factorization property are residually finite, Math. Ann. 299 (1994).
* B. Blackadar, E. Kirchberg, Generalized inductive limits of finite-dimensional C*-algebras, Math. Ann. 307 (1997).
* A. Tikuisis, S. White, W. Winter, Quasidiagonality of nuclear C*-algebras, Ann. of Math. 185 (2017).
* U. Haagerup, Quasitraces on exact C*-algebras are traces, C. R. Math. Acad. Sci. Soc. R. Can. 36 (2014).
* E. Breuillard, M. Kalantar, M. Kennedy, N. Ozawa, C*-simplicity and the unique trace property for discrete groups, Publ. IHÉS 126 (2017).
* L. Robert, Selfless C*-algebras, arXiv 2023.
* T. Amrutam, D. Gao, S. Kunnawalkam Elayavalli, G. Patchell, Strict comparison in reduced group C*-algebras, arXiv:2412.06031.
* L. Louder, M. Magee, Strongly convergent unitary representations of limit groups, arXiv:2210.08953.
* M. Bekka, M. Cowling, P. de la Harpe, Some groups whose reduced C*-algebra is simple, Publ. IHÉS 80 (1994).
* Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE.
