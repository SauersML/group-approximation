import GroupApproximation.BooneHigman.Metabelian.EnvelopeCantorAction
import GroupApproximation.BooneHigman.V.Group
import GroupApproximation.BooneHigman.V.Supports
import Mathlib.Data.List.OfFn
import GroupApproximation.Meta.AxiomGuard

/-!
# The wreath recursion on the Cantor set

For `h : TreeAut X` the Cantor permutation `cantorHom h` splits along the first level as
`cantorHom h = nfRootShift (rootPerm h) * Π_{x} localize [x] (cantorHom (state h [x]))`.
Here `nfRootShift σ` is the depth-one element `x y ↦ σ(x) y` of `V_X`.

Route.
* `nf_firstWord_succ_prepend`: the first `N + 1` letters of `x y` are `x :: firstWord N y`.
  Proof: `firstWord_length_prepend` for `x :: firstWord N y` together with `prepend_firstWord`.
* `nf_cantorHom_prepend_singleton`: `h · (x y) = rootPerm h x · (state h [x] · y)`, by
  comparing first words (`firstWord_streamFun`, `TreeAut.smul_cons`).
* `nfLevelProd l g = Π_{b ∈ l} localize [b] (g b)` fixes `x y` for `x ∉ l` and acts as
  `x y ↦ x (g x y)` for `x ∈ l` when `l` has no duplicates.  Both are by induction on `l`.
* `nf_wreath`: the two sides agree on every `x y`, and every stream is of this form.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

theorem nf_firstWord_succ_prepend (x : X) (y : Cantor X) (N : ℕ) :
    firstWord (N + 1) (prepend [x] y) = x :: firstWord N y := by
  have e : prepend (x :: firstWord N y) (dropN N y) = prepend [x] y := by
    rw [show x :: firstWord N y = [x] ++ firstWord N y from rfl, prepend_append,
      prepend_firstWord]
  have h := firstWord_length_prepend (x :: firstWord N y) (dropN N y)
  rw [e, List.length_cons, length_firstWord] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_firstWord_succ_prepend

theorem nf_eq_of_firstWord_succ {a b : Cantor X}
    (h : ∀ N : ℕ, firstWord (N + 1) a = firstWord (N + 1) b) : a = b := by
  funext n
  exact congrFun (List.ofFn_inj.mp (h n)) ⟨n, Nat.lt_succ_self n⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_eq_of_firstWord_succ

/-- The wreath recursion for the Cantor action on a one-letter cone. -/
theorem nf_cantorHom_prepend_singleton (g : TreeAut X) (x : X) (y : Cantor X) :
    cantorHom g (prepend [x] y) =
      prepend [TreeAut.rootPerm g x] (cantorHom (TreeAut.state g [x]) y) := by
  refine nf_eq_of_firstWord_succ fun N => ?_
  rw [nf_firstWord_succ_prepend, cantorHom_apply, cantorHom_apply, firstWord_streamFun,
    firstWord_streamFun, nf_firstWord_succ_prepend, TreeAut.smul_cons]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_cantorHom_prepend_singleton

/-- The depth-one element of `V_X` permuting the first letter by `σ`. -/
def nfRootShift (σ : Equiv.Perm X) : Equiv.Perm (Cantor X) :=
  cantorHom (TreeAut.ofWreath σ fun _ => 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRootShift

theorem nfRootShift_apply (σ : Equiv.Perm X) (x : X) (y : Cantor X) :
    nfRootShift σ (prepend [x] y) = prepend [σ x] y := by
  simp only [nfRootShift, nf_cantorHom_prepend_singleton, TreeAut.rootPerm_ofWreath,
    TreeAut.state_ofWreath, map_one, Equiv.Perm.one_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRootShift_apply

theorem nfRootShift_mem [Finite X] (σ : Equiv.Perm X) : nfRootShift σ ∈ higmanThompsonV X := by
  refine mem_higmanThompsonV.mpr ⟨1, fun w hw => ?_⟩
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hw
  exact ⟨[σ a], fun y => nfRootShift_apply σ a y⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRootShift_mem

theorem nf_not_isStreamPrefix_singleton {x b : X} (hxb : x ≠ b) (y : Cantor X) :
    ¬ IsStreamPrefix [b] (prepend [x] y) := by
  intro hp
  have h0 := hp 0 (by simp)
  rw [prepend_getElem [x] y (n := 0) (by simp)] at h0
  exact hxb (by simpa using h0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_not_isStreamPrefix_singleton

/-- The product over the letters of `l` of the elements `g b` localised at `[b]`. -/
def nfLevelProd (l : List X) (g : X → Equiv.Perm (Cantor X)) : Equiv.Perm (Cantor X) :=
  (l.map fun b => localize [b] (g b)).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfLevelProd

theorem nfLevelProd_cons (b : X) (l : List X) (g : X → Equiv.Perm (Cantor X)) :
    nfLevelProd (b :: l) g = localize [b] (g b) * nfLevelProd l g := by
  simp only [nfLevelProd, List.map_cons, List.prod_cons]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfLevelProd_cons

theorem nfLevelProd_apply_of_not_mem (g : X → Equiv.Perm (Cantor X)) (x : X) (y : Cantor X)
    (l : List X) (hx : x ∉ l) : nfLevelProd l g (prepend [x] y) = prepend [x] y := by
  induction l with
  | nil => simp [nfLevelProd]
  | cons b l ih =>
    have hxb : x ≠ b := fun e => hx (List.mem_cons.mpr (Or.inl e))
    rw [nfLevelProd_cons, Equiv.Perm.mul_apply,
      ih fun e => hx (List.mem_cons.mpr (Or.inr e)),
      localize_apply_of_not (nf_not_isStreamPrefix_singleton hxb y)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfLevelProd_apply_of_not_mem

theorem nfLevelProd_apply_of_mem (g : X → Equiv.Perm (Cantor X)) (x : X) (y : Cantor X)
    (l : List X) (hl : l.Nodup) (hx : x ∈ l) :
    nfLevelProd l g (prepend [x] y) = prepend [x] (g x y) := by
  induction l with
  | nil => simp at hx
  | cons b l ih =>
    rw [List.nodup_cons] at hl
    rw [nfLevelProd_cons, Equiv.Perm.mul_apply]
    rcases List.mem_cons.mp hx with e | e
    · subst e
      rw [nfLevelProd_apply_of_not_mem g x y l hl.1, localize_apply_prepend]
    · have hxb : x ≠ b := fun e' => hl.1 (by rw [← e']; exact e)
      rw [ih hl.2 e, localize_apply_of_not (nf_not_isStreamPrefix_singleton hxb _)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfLevelProd_apply_of_mem

/-- **The wreath recursion.**  `h = σ_h · Π_x localize [x] (h|_x)` on the Cantor set. -/
theorem nf_wreath (h : TreeAut X) (l : List X) (hl : l.Nodup) (hall : ∀ x, x ∈ l) :
    cantorHom h = nfRootShift (TreeAut.rootPerm h) *
      nfLevelProd l fun x => cantorHom (TreeAut.state h [x]) := by
  refine Equiv.ext fun z => ?_
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (length_firstWord 1 z)
  rw [← prepend_firstWord 1 z, ha, Equiv.Perm.mul_apply,
    nfLevelProd_apply_of_mem _ a _ l hl (hall a), nf_cantorHom_prepend_singleton,
    nfRootShift_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_wreath

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
