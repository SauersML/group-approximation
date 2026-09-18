import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsCoreConj
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.Nodup
import Batteries.Data.List.Perm
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite core relators: products over the alphabet and canonical splitting data

Helpers for step 4 of the finite core (splitting and root relators on generators).
* `rcore_prod_mul_prod`, `rcore_prod_perm`: merging and reindexing products over a list without
  repetition, when factors indexed by distinct letters commute.
* `rcoreShift u σ ∈ V_X`: `localize u (nfRootShift σ)`, multiplicative in `σ`, carrying
  `cone (u ++ [y])` onto `cone (u ++ [σ y])`.
* `rcoreE x₀ w ∈ V_X`: a chosen element carrying `cone [x₀]` onto `cone w`.
* `rcoreSt H hH h x ∈ H`: the state of `h` at `[x]`, with the cocycle rule `rcoreSt_mul`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

theorem rcore_prod_mul_prod {G ι : Type*} [Group G] (F K : ι → G) (l : List ι) (hl : l.Nodup)
    (hc : ∀ x y, x ≠ y → Commute (F x) (K y)) :
    (l.map F).prod * (l.map K).prod = (l.map fun x => F x * K x).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, mul_one]
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := List.nodup_cons.mp hl
    have hPK : Commute (t.map F).prod (K a) := by
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact hc b a fun hba => hat (hba ▸ hb)
    simp only [List.map_cons, List.prod_cons]
    rw [← ih ht, mul_assoc, ← mul_assoc (t.map F).prod, hPK.eq]
    simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_prod_mul_prod

theorem rcore_prod_perm {G ι : Type*} [Group G] (F : ι → G) {l l' : List ι} (hl : l.Nodup)
    (hl' : l'.Nodup) (hmem : ∀ x, x ∈ l ↔ x ∈ l')
    (hc : ∀ x y, x ≠ y → Commute (F x) (F y)) :
    (l.map F).prod = (l'.map F).prod :=
  (((List.perm_ext_iff_of_nodup hl hl').mpr hmem).map F).prod_eq'
    (List.pairwise_map.mpr (hl.pairwise_of_forall_ne fun a _ b _ hab => hc a b hab))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_prod_perm

theorem rcore_cantor_ext {f g : Equiv.Perm (Cantor X)}
    (h : ∀ (a : X) (y : Cantor X), f (prepend [a] y) = g (prepend [a] y)) : f = g := by
  refine Equiv.ext fun z => ?_
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (length_firstWord 1 z)
  rw [← prepend_firstWord 1 z, ha]
  exact h a _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_cantor_ext

theorem rcore_nfRootShift_mul (σ τ : Equiv.Perm X) :
    nfRootShift (σ * τ) = nfRootShift σ * nfRootShift τ :=
  rcore_cantor_ext fun a y => by
    simp only [Equiv.Perm.mul_apply, nfRootShift_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_nfRootShift_mul

theorem rcore_rootPerm_mul (g h : TreeAut X) :
    TreeAut.rootPerm (g * h) = TreeAut.rootPerm g * TreeAut.rootPerm h :=
  Equiv.ext (TreeAut.rootFun_mul g h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_rootPerm_mul

/-- The shift `localize u (nfRootShift σ)` as an element of `V_X`. -/
def rcoreShift [Finite X] (u : List X) (σ : Equiv.Perm X) : ↥(higmanThompsonV X) :=
  ⟨localize u (nfRootShift σ), localize_mem_higmanThompsonV (nfRootShift_mem σ) u⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreShift

theorem rcoreShift_mul [Finite X] (u : List X) (σ τ : Equiv.Perm X) :
    rcoreShift u (σ * τ) = rcoreShift u σ * rcoreShift u τ :=
  Subtype.ext (by
    show localize u (nfRootShift (σ * τ)) =
      localize u (nfRootShift σ) * localize u (nfRootShift τ)
    rw [rcore_nfRootShift_mul, map_mul])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreShift_mul

theorem rcore_mapsCone_shift [Finite X] (u : List X) (σ : Equiv.Perm X) (y : X) :
    MapsCone (rcoreShift u σ : Equiv.Perm (Cantor X)) (u ++ [y]) (u ++ [σ y]) := fun z => by
  show localize u (nfRootShift σ) (prepend (u ++ [y]) z) = prepend (u ++ [σ y]) z
  rw [prepend_append, prepend_append, localize_apply_prepend, nfRootShift_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_mapsCone_shift

open Classical in
/-- A chosen element of `V_X` carrying `cone [x₀]` onto `cone w` (or `1` if there is none). -/
def rcoreE [Finite X] (x₀ : X) (w : List X) : ↥(higmanThompsonV X) :=
  if h : ∃ e : ↥(higmanThompsonV X), MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w then h.choose
  else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreE

theorem rcoreE_spec [Finite X] [Nontrivial X] (x₀ : X) {w : List X} (hw : w ≠ []) :
    MapsCone (rcoreE x₀ w : Equiv.Perm (Cantor X)) [x₀] w := by
  have h : ∃ e : ↥(higmanThompsonV X), MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w := by
    obtain ⟨f, hf, hfw⟩ := exists_mapsCone_of_ne_nil (List.cons_ne_nil x₀ []) hw
    exact ⟨⟨f, hf⟩, hfw⟩
  rw [rcoreE, dif_pos h]
  exact h.choose_spec

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreE_spec

/-- The state of `h ∈ H` at the vertex `[x]`, as an element of the self-similar group `H`. -/
def rcoreSt (H : Subgroup (TreeAut X)) (hH : IsSelfSimilar H) (h : ↥H) (x : X) : ↥H :=
  ⟨TreeAut.state (h : TreeAut X) [x], hH _ h.2 x⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreSt

theorem rcoreSt_mul (H : Subgroup (TreeAut X)) (hH : IsSelfSimilar H) (h k : ↥H) (x : X) :
    rcoreSt H hH (h * k) x =
      rcoreSt H hH h (TreeAut.rootPerm (k : TreeAut X) x) * rcoreSt H hH k x :=
  Subtype.ext (by
    show TreeAut.state ((h : TreeAut X) * (k : TreeAut X)) [x] =
      TreeAut.state (h : TreeAut X) [TreeAut.rootPerm (k : TreeAut X) x] *
        TreeAut.state (k : TreeAut X) [x]
    rw [TreeAut.state_mul, TreeAut.smul_singleton, TreeAut.rootPerm_apply])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreSt_mul

theorem rcore_exists_list [Finite X] : ∃ l : List X, l.Nodup ∧ ∀ x, x ∈ l := by
  have := Fintype.ofFinite X
  exact ⟨Finset.univ.toList, Finset.nodup_toList _,
    fun x => Finset.mem_toList.mpr (Finset.mem_univ x)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_exists_list

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
