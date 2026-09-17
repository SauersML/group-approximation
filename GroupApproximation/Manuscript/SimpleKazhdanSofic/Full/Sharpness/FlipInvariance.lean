import GroupApproximation.Manuscript.SimpleKazhdanSofic.CrossedProductConjugacy
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Meta.AxiomGuard

/-!
# Sharpness over `ℤ`: simplicity and property `(T)` are conjugacy and flip invariants

`simple_kazhdan_sofic_group.tex`, subsection "Sharpness over $\Z$" (Section `sec:main`),
tex l.393–396:

> For a homeomorphism $T$ of a Cantor set $X$, the group $\EL_3(\LC(X,\F_2)\rtimes_T\Z)$ is simple
> and Kazhdan if and only if $(X,T)$ is conjugate to a minimal subshift.

The printed statement only makes sense up to conjugacy: "conjugate to a minimal subshift" is a
conjugacy invariant, so the left-hand side must be one as well. The tex also uses the flip
(`T ↦ T⁻¹`, section "Questions", tex l.747–749: "If $(X,T)$ is topologically conjugate to $(Y,S)$
or to $(Y,S^{-1})$, then $G_X\cong G_Y$").

## Proof route

* The root theorem `nonempty_elementaryGroup_equiv_of_conj_or_flip` turns a conjugacy
  `φ ∘ T = S ∘ φ`, or a flip conjugacy `φ ∘ T = S⁻¹ ∘ φ`, into an isomorphism
  `EL_n(LC(X,k) ⋊_T ℤ) ≃* EL_n(LC(Y,k) ⋊_S ℤ)`, for every rank `n` and ring `k`.
* Simplicity moves along isomorphisms (`MulEquiv.isSimpleGroup_congr`), and so does property `(T)`
  (`HasKazhdanPropertyT.of_mulEquiv`).
-/

namespace GroupApproximation.Full.SK07

open GroupApproximation.SimpleKazhdanSofic (nonempty_elementaryGroup_equiv_of_conj_or_flip)

/-- **Simple and Kazhdan is a conjugacy and flip invariant** (tex l.393–396, together with
"Questions", tex l.747–749). If `(X,T)` is conjugate to `(Y,S)` or to `(Y,S⁻¹)`, then
`EL_n(LC(X,k) ⋊_T ℤ)` is simple with property `(T)` exactly when `EL_n(LC(Y,k) ⋊_S ℤ)` is. -/
theorem simpleKazhdan_iff_of_conj_or_flip {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {T : X ≃ₜ X} {S : Y ≃ₜ Y} (k : Type) [Ring k] (n : ℕ) (φ : X ≃ₜ Y)
    (hφ : (∀ x, φ (T x) = S (φ x)) ∨ ∀ x, φ (T x) = S.symm (φ x)) :
    (IsSimpleGroup (elementaryGroup (Fin n) (ClopenCrossedProduct T k)) ∧
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) (ClopenCrossedProduct T k))) ↔
      (IsSimpleGroup (elementaryGroup (Fin n) (ClopenCrossedProduct S k)) ∧
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) (ClopenCrossedProduct S k))) := by
  obtain ⟨e⟩ := nonempty_elementaryGroup_equiv_of_conj_or_flip k n φ hφ
  constructor
  · rintro ⟨hs, hT⟩
    exact ⟨(MulEquiv.isSimpleGroup_congr e).mp hs, HasKazhdanPropertyT.of_mulEquiv e.symm hT⟩
  · rintro ⟨hs, hT⟩
    exact ⟨(MulEquiv.isSimpleGroup_congr e).mpr hs, HasKazhdanPropertyT.of_mulEquiv e hT⟩

#audit_axioms simpleKazhdan_iff_of_conj_or_flip

/-- **The flip `T ↦ T⁻¹` does not change whether `EL_n(LC(X,k) ⋊_T ℤ)` is simple and Kazhdan**
(tex l.393–396 and l.747–749, with `φ` the identity). -/
theorem simpleKazhdan_iff_symm {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k]
    (n : ℕ) :
    (IsSimpleGroup (elementaryGroup (Fin n) (ClopenCrossedProduct T k)) ∧
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) (ClopenCrossedProduct T k))) ↔
      (IsSimpleGroup (elementaryGroup (Fin n) (ClopenCrossedProduct T.symm k)) ∧
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) (ClopenCrossedProduct T.symm k))) :=
  simpleKazhdan_iff_of_conj_or_flip (T := T) (S := T.symm) k n (Homeomorph.refl X)
    (Or.inr fun _ => rfl)

#audit_axioms simpleKazhdan_iff_symm

end GroupApproximation.Full.SK07
