import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ThomGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Root audit for `simple_kazhdan_sofic_group.tex`: the introduction (row A2)

The introductory paragraph before `thm:main` (tex l.48–68) records three results from the
literature, all formalized by the `Full.A2Endpoint` lane:

* Ozawa (tex l.54–56): the full C*-algebra of an infinite simple Kazhdan hyperlinear group does not
  have the local lifting property;
* Thom, via Kirchberg (tex l.57–59): a Kazhdan group that is not residually finite has no
  factorization property, and a finitely generated Kazhdan LEF group of this kind exists;
* tex l.59–60: Thom's example `G₀(F_p[t,t⁻¹])/C` is not simple.

`intro_ozawa_thom` is the conjunction of the types of those endpoints, proved by the tuple.
`Full.Root.Manuscript` collects it with the other labels.
-/

namespace GroupApproximation.Full.SKRoot

/-- **The introduction, row A2** (tex l.54–60): Ozawa's no-LLP theorem for the full C*-algebra of
an infinite simple Kazhdan hyperlinear group; Kirchberg's theorem in Thom's form (Kazhdan and not
residually finite gives no factorization property), together with a finitely generated Kazhdan LEF
group that is not residually finite and has no factorization property; and non-simplicity of Thom's
group `G₀(F_p[t,t⁻¹])/C`.  Conjuncts: `A2Endpoint.ozawa_not_hasLocalLiftingProperty`,
`A2Endpoint.not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite`,
`A2Endpoint.exists_fg_kazhdan_lef_not_rf_not_fp_not_simple`, and
`A2Endpoint.not_isSimpleGroup_thomGroup_zmod`. -/
theorem intro_ozawa_thom :
    type_of% @Full.A2Endpoint.ozawa_not_hasLocalLiftingProperty ∧
    type_of% @Full.A2Endpoint.not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite ∧
    type_of% @Full.A2Endpoint.exists_fg_kazhdan_lef_not_rf_not_fp_not_simple ∧
    type_of% @Full.A2Endpoint.not_isSimpleGroup_thomGroup_zmod :=
  ⟨@Full.A2Endpoint.ozawa_not_hasLocalLiftingProperty,
    @Full.A2Endpoint.not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite,
    @Full.A2Endpoint.exists_fg_kazhdan_lef_not_rf_not_fp_not_simple,
    @Full.A2Endpoint.not_isSimpleGroup_thomGroup_zmod⟩

end GroupApproximation.Full.SKRoot

#audit_closed_axioms GroupApproximation.Full.SKRoot.intro_ozawa_thom
