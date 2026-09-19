import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WideSigma
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNK
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: the `|K|`-induction, and `FieldCosetAt F` from the wide residual

k2-poly piece A5.2 (lane k2-field-a). The field port of lane 93l's `ElemFPK2PolyNagaoWideMain`.

* `fnWide_stab_of_gens`: a `σ` with `σ(e_L) ∈ Z ⊔ Q`, good on the small generating set, gives
  `fnWide_Stab F K L`.
* `fnWide_stab_all`: the residual `fnWide_Statement F` gives `Stab(K, L)` for every nonempty `K`,
  by strong induction on `|K|`. The case `K = {m}` is `fnWeyl_genGood_rankOne`, proved outright.
  The case `|K| ≥ 2` uses the residual at `Stab(J, m)`, `J = K \ {m}`.
* **`fnWide_coset_of_statement : fnWide_Statement F → FieldCosetAt F`.**
* **`fieldNK_of_wide`**: `(∀ F, fnWide_Statement F) → FieldNKStatement`, via the lead's
  `fieldNK_of_fieldCoset`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic (K2)
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnC FieldNKStatement fieldNK_of_fieldCoset)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_one unitVec
  rootSpan_mono)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- **Coset trick.** A `σ` with `σ(e_L) ∈ Z ⊔ Q`, good on the small generating set, gives
`Stab(K, L)`. -/
theorem fnWide_stab_of_gens {K : Finset I} {m L : I} (hLK : L ∉ K) (hmL : m ≠ L)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)}
    (hσ : σ (unitVec L) ∈ fnZQ F K L) (hG : fnGenGood F K L m hmL σ) : fnWide_Stab F K L := by
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  have hgen := fn_coset_of_gen hLK hmL hmn hLn hG
  intro g hg hfix
  have hc := fn_closure σ hgen hg (unitVec L) ⟨1, Subgroup.one_mem _, act_one _⟩
  rw [hfix] at hc
  have e : g = σ (unitVec L) * ((σ (unitVec L))⁻¹ * g * σ (unitVec L)) *
      (σ (unitVec L))⁻¹ := by
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hc) (Subgroup.inv_mem _ hσ)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_stab_of_gens

/-- `S_J ≤ S_K`. -/
theorem fnWide_S_erase_le (K : Finset I) (m : I) : fnS F (K.erase m) ≤ fnS F K := fun _ hs =>
  rootSpan_mono (p := fun i j => i ∈ K.erase m ∧ j ∈ K.erase m)
    (q := fun i j => i ∈ K ∧ j ∈ K)
    (fun _ _ _ h => ⟨Finset.mem_of_mem_erase h.1, Finset.mem_of_mem_erase h.2⟩) hs

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_S_erase_le

/-- **The `|K|`-induction.** The residual gives `Stab(K, L)` for every nonempty `K`. -/
theorem fnWide_stab_all (hR : fnWide_Statement F) (N : ℕ) :
    ∀ (K : Finset I) (L : I), K.card = N → L ∉ K → K.Nonempty →
      (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
      (∀ s ∈ fnS F K, s ∈ K2 I (Polynomial F) → s ∈ fnC F) → fnWide_Stab F K L := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K L hN hLK hK hthird hSK
  obtain ⟨m, hmK⟩ := hK
  have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  by_cases hKm : ∀ i ∈ K, i = m
  · exact fnWide_stab_of_gens hLK hmL hthird (fnSigma_sigma_unitVec_mem m L hmL)
      (fnWeyl_genGood_rankOne hmL hmn hLn hmK hKm)
  · push Not at hKm
    obtain ⟨i, hi, him⟩ := hKm
    have hlt : (K.erase m).card < N := by
      rw [← hN]
      exact Finset.card_erase_lt_of_mem hmK
    have hJ : fnWide_Stab F (K.erase m) m :=
      ih _ hlt (K.erase m) m rfl (Finset.notMem_erase m K)
        ⟨i, Finset.mem_erase.2 ⟨him, hi⟩⟩ hthird
        (fun s hs hs2 => hSK s (fnWide_S_erase_le K m hs) hs2)
    exact fnWide_stab_of_gens hLK hmL hthird (fnWide_sigma_unitVec hmL hmK hLK)
      (fnWide_gens_of_check hmL hmK hLK hthird hJ
        (hR K m L hmL hLK hmK ⟨i, hi, him⟩ hthird hSK hJ))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_stab_all

/-- **The wide residual gives the van der Waerden criterion over `F`.** -/
theorem fnWide_coset_of_statement (hR : fnWide_Statement F) : FieldCosetAt F := by
  intro I _ _ K L hLK hK hthird ih
  obtain ⟨m, hmK⟩ := hK
  have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  by_cases hKm : ∀ i ∈ K, i = m
  · exact ⟨fnSigma_sigma F m L hmL, fnSigma_sigma_unitVec_mem m L hmL,
      fn_coset_of_gen hLK hmL hmn hLn (fnWeyl_genGood_rankOne hmL hmn hLn hmK hKm)⟩
  · push Not at hKm
    obtain ⟨i, hi, him⟩ := hKm
    have hJ : fnWide_Stab F (K.erase m) m :=
      fnWide_stab_all hR _ (K.erase m) m rfl (Finset.notMem_erase m K)
        ⟨i, Finset.mem_erase.2 ⟨him, hi⟩⟩ hthird
        (fun s hs hs2 => ih s (fnWide_S_erase_le K m hs) hs2)
    exact ⟨fnWide_sigma F K m L hmL, fnWide_sigma_unitVec hmL hmK hLK,
      fn_coset_of_gen hLK hmL hmn hLn (fnWide_gens_of_check hmL hmK hLK hthird hJ
        (hR K m L hmL hLK hmK ⟨i, hi, him⟩ hthird ih hJ))⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_coset_of_statement

/-- **Endpoint.** The wide residual at every field gives `FieldNKStatement` (A5). -/
theorem fieldNK_of_wide (hR : ∀ (F : Type) [Field F], fnWide_Statement F) : FieldNKStatement :=
  fieldNK_of_fieldCoset fun F _ => fnWide_coset_of_statement (hR F)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fieldNK_of_wide

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
