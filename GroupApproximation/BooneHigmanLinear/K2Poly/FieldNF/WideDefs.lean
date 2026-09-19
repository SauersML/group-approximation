import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.Sigma
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: definitions of the wide step, and its residual `fnWide_Statement`

k2-poly piece A5.2 (lane k2-field-a). The field port of the definitions of lane 93l's
`ElemFPK2PolyNagaoWide{Span,Stab,Sigma,Main}`, gathered in one small module so that consumers
can build against the residual before the proofs land. Notation of `FieldNF.Check`; `m ∈ K`,
`L ∉ K`, `J = K \ {m}`.

* `fnWide_Qr K L = ⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K⟩` (equal to `Q`), `fnWide_Qm K m L`
  (`j ∈ J`), and `fnWide_Gml m L = ⟨x_mL(f), x_Lm(f)⟩`.
* `fnWide_Stab F K L`: every `g ∈ S_{K ∪ {L}}` fixing `e_L` lies in `Z ⊔ Q`, the field form
  of `Stab_G(e_L) = Q`.
* `fnWide_Supp m L r`: `r` is supported on `{m, L}`.
* The wide section `fnWide_sigma F K m L hmL v = q_v · σ₀(r_v)`: `r_v` a representative of `v`
  supported on `{m, L}` in the `Q`-orbit of `v`, `q_v ∈ Q` with `q_v r_v = v`, and `σ₀` the
  Euclidean section of `FieldNF.Sigma`.
* **`fnWide_Statement F`** (the residual): given `Stab(J, m)`, the wide section passes the check
  at the single generator `x_mL(1)`. `FieldNF.WideMain` proves
  `fnWide_coset_of_statement : fnWide_Statement F → FieldCosetAt F`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic (K2)
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV fnC)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- `r` is supported on `{m, L}`. -/
def fnWide_Supp {R : Type} [Zero R] (m L : I) (r : I → R) : Prop :=
  ∀ i, i ≠ m → i ≠ L → r i = 0

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Supp

section Defs

variable (F : Type) [Field F]

/-- `Q` as one root span: `⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K⟩`. -/
def fnWide_Qr (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  rootSpan (R := Polynomial F) fun i j => i ∈ insert L K ∧ j ∈ K

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Qr

/-- `Q^m = ⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K \ {m}⟩`. -/
def fnWide_Qm (K : Finset I) (m L : I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  rootSpan (R := Polynomial F) fun i j => i ∈ insert L K ∧ j ∈ K.erase m

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Qm

/-- `G_{mL} = ⟨x_mL(f), x_Lm(f)⟩`. -/
def fnWide_Gml (m L : I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  rootSpan (R := Polynomial F) fun i j => (i = m ∨ i = L) ∧ (j = m ∨ j = L)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Gml

/-- `Stab_G(e_L) ≤ Z ⊔ Q` at one `K`, `L`. -/
def fnWide_Stab (K : Finset I) (L : I) : Prop :=
  ∀ g ∈ fnS F (insert L K), act g (unitVec L) = unitVec L → g ∈ fnZQ F K L

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Stab

/-- The admissible representatives of `v`: supported on `{m, L}` and in the `Q`-orbit of `v`. -/
def fnWide_repSet (K : Finset I) (m L : I) (v : I → Polynomial F) (r : I → Polynomial F) :
    Prop :=
  fnWide_Supp m L r ∧ ∃ q ∈ fnQ F K L, act q r = v

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_repSet

/-- The chosen representative of `v`. -/
noncomputable def fnWide_rep (K : Finset I) (m L : I) (v : I → Polynomial F) :
    I → Polynomial F :=
  Classical.epsilon (fnWide_repSet F K m L v)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_rep

/-- The chosen `q ∈ Q` with `q r_v = v`. -/
noncomputable def fnWide_qsel (K : Finset I) (m L : I) (v : I → Polynomial F) :
    SteinbergGroup I (Polynomial F) :=
  Classical.epsilon fun q => q ∈ fnQ F K L ∧ act q (fnWide_rep F K m L v) = v

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_qsel

/-- **The wide section.** `σ(v) = q_v · σ₀(r_v)`. -/
noncomputable def fnWide_sigma (K : Finset I) (m L : I) (hmL : m ≠ L) (v : I → Polynomial F) :
    SteinbergGroup I (Polynomial F) :=
  fnWide_qsel F K m L v * fnSigma_sigma F m L hmL (fnWide_rep F K m L v)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_sigma

end Defs

/-- **The residual of the wide step over `F`.** Given `Stab(J, m)` (`J = K \ {m}` nonempty) and
the induction hypothesis `S_K ∩ K₂ ⊆ C`, the wide section passes the check at the single
generator `x_mL(1)`, with target `Z ⊔ Q`. -/
def fnWide_Statement (F : Type) [Field F] : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L : I) (hmL : m ≠ L),
    L ∉ K → m ∈ K → (∃ i ∈ K, i ≠ m) → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ s ∈ fnS F K, s ∈ K2 I (Polynomial F) → s ∈ fnC F) →
    fnWide_Stab F (K.erase m) m →
    fnCheck F K L (fnWide_sigma F K m L hmL) (x m L hmL (1 : Polynomial F))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Statement

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
