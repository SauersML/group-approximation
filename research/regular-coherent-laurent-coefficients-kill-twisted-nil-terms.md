---
rg: 2
id: regular-coherent-laurent-coefficients-kill-twisted-nil-terms
kind: claim
title: If every Laurent ring R[Z^m] is regular coherent, the K-theory of a skew Laurent ring R_φ[t, t^-1] is the mapping torus of φ on K(R)
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports vanishing of K(L_2 ⊗ R) for regular supercoherent R, through the Ara–Brustenga–Cortiñas sequence for Leavitt path algebras; this is the twisted Bass–Heller–Swan theorem with vanishing Nil terms, for any skew Laurent ring over a ring whose Laurent extensions are regular coherent.
  regular-coherent-coefficients-kill-leavitt-tensor-k-theory: that is the Leavitt-tensor statement for regular coherent coefficient rings in degrees n >= 1; this concerns skew Laurent rings and holds in every degree, under regular coherence of all Laurent extensions.
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `R` be a ring such that
`R[Z^m] = R[t_1^±, ..., t_m^±]` is regular coherent for every `m >= 0`. Here
"regular coherent" means that every finitely presented module has a finite
resolution by finitely generated projective modules. Let `φ` be a ring
automorphism of `R`.

Then the natural map from the mapping torus of `K(φ^−1)` on the non-connective
`K`-theory spectrum `K(R)`,

```text
T_(K(φ^−1)) -> K(R_φ[t, t^−1]),
```

is a weak equivalence, and the twisted Nil spectra `NK(R_φ[t^±1])` are
contractible. In particular, if `K_n(R) = 0` for every `n ∈ Z`, then
`K_n(R_φ[t, t^−1]) = 0` for every `n ∈ Z`.

**Sources.** Both were read from the arXiv e-print TeX sources on MSI,
2026-09-12.

1. A. Bartels and W. Lück, *Vanishing of Nil-terms and negative K-theory for
   additive categories*, arXiv:2002.03412. The arXiv abstract page gives the
   journal reference Proc. Roy. Soc. Edinburgh Sect. A 154 (2024) 1945–2023.
   - **Theorem `the:The_non_connective_K-theory_of_additive_categories`.** "Let A
     be an additive category. Suppose that A[Z^m] is regular coherent for every
     m ≥ 0. Consider any automorphism Φ: A → A of additive categories. Then we get
     a weak homotopy equivalence of non-connective spectra
     a^∞ : T_{K^∞(Φ^{−1})} → K^∞(A_Φ[t,t^{−1}])." Its proof records
     π_n(NK^∞(A_Φ[t^{±}])) = 0 for all n ∈ Z.
   - **The Laurent categories.** "A[Z^m] := A[Z^{m−1}]_id[t,t^{−1}]", the
     iterated untwisted finite Laurent category.
   - **Rings versus categories.** Definition: R is regular coherent "if every
     finitely presented R-module M is of type FP". Corollary
     `cor:regualiyt_for_R-versus_underline(r)_oplus)`: R is regular coherent if
     and only if the additive category `R_⊕` is.
2. W. Lück and W. Steimle, *A twisted Bass–Heller–Swan decomposition for the
   algebraic K-theory of additive categories*, arXiv:1309.1353.
   - **Example "Finitely generated free R-modules".** For a ring automorphism
     `φ` with induced `Φ`, `R_Φ[t,t^{−1}]` "is equivalent to the category of
     finitely generated free modules over the twisted group ring
     R_φ[t,t^{−1}]". With `φ = id` and induction, `R_⊕[Z^m] ≃ R[Z^m]_⊕`.
   - **Theorem `the:Passage_to_the_idempotent_completion`, part 2.** "The map of
     non-connective spectra K^∞(η(A)) : K^∞(A) → K^∞(Idem(A)) is a weak homotopy
     equivalence." So `K^∞(R_⊕)` is the non-connective `K`-theory of `R`, and
     likewise for `R_φ[t, t^−1]`.

**The ring form.**
- Apply source 1 to `A = R_⊕` and `Φ = φ_*`. The hypothesis holds by the
  corollary on rings versus categories and the identification `R_⊕[Z^m] ≃ R[Z^m]_⊕`.
- The target is `K(R_φ[t, t^−1])`, by the Example and part 2 of the
  idempotent-completion theorem.
- If `K(R) ≃ 0`, the mapping torus of a self-map of a contractible spectrum is
  contractible.
