import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceElementaryWeylNormalGenerationClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Exact closure of the current normal-generation sentences

The current proof of normal generation uses two intermediate assertions that
are stronger than the conclusion-only declarations used elsewhere in the
tree.  First, a finite product of the printed generalized permutation
matrices conjugates any unit root to any other unit root or its inverse.
Second, after the sandwich commutators and this Weyl propagation, the normal
subgroup contains every coefficient root before generation gives that it is
the whole elementary group.

Both assertions are exposed below in their printed order.  No ring-specific
or literature-supplied hypothesis is used.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

universe u v

/-! ## Finite products of the printed Weyl matrices -/

/-- The set of literal generalized permutation matrices printed in the
manuscript: `w_uv = e_uv(1) e_vu(-1) e_uv(1)`. -/
def printedWeylSet (ι : Type u) (S : Type v)
    [Fintype ι] [DecidableEq ι] [Ring S] :
    Set (elementaryGroup ι S) :=
  {w | ∃ (a b : ι) (hab : a ≠ b),
    w = ElementaryWeyl.weyl (S := S) a b hab}

/-- A group element is a finite product of the literal printed Weyl matrices
when it is the product of a finite list all of whose entries lie in
`printedWeylSet`. -/
def IsPrintedWeylProduct
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (W : elementaryGroup ι S) : Prop :=
  ∃ ws : List (elementaryGroup ι S),
    (∀ w ∈ ws, w ∈ printedWeylSet ι S) ∧ ws.prod = W

private theorem isPrintedWeylProduct_one
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S] :
    IsPrintedWeylProduct (1 : elementaryGroup ι S) := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · rfl

private theorem isPrintedWeylProduct_weyl
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (a b : ι) (hab : a ≠ b) :
    IsPrintedWeylProduct (ElementaryWeyl.weyl (S := S) a b hab) := by
  refine ⟨[ElementaryWeyl.weyl (S := S) a b hab], ?_, by simp⟩
  intro w hw
  simp only [List.mem_singleton] at hw
  subst w
  exact ⟨a, b, hab, rfl⟩

private theorem IsPrintedWeylProduct.mul
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    {W₂ W₁ : elementaryGroup ι S}
    (hW₂ : IsPrintedWeylProduct W₂) (hW₁ : IsPrintedWeylProduct W₁) :
    IsPrintedWeylProduct (W₂ * W₁) := by
  obtain ⟨ws₂, hws₂, hprod₂⟩ := hW₂
  obtain ⟨ws₁, hws₁, hprod₁⟩ := hW₁
  refine ⟨ws₂ ++ ws₁, ?_, ?_⟩
  · intro w hw
    rw [List.mem_append] at hw
    exact hw.elim (hws₂ w) (hws₁ w)
  · rw [List.prod_append, hprod₂, hprod₁]

private theorem conjugatesUpToInverse_comp
    {G : Type*} [Group G] {W₁ W₂ x y z : G}
    (h₁ : W₁ * x * W₁⁻¹ = y ∨ W₁ * x * W₁⁻¹ = y⁻¹)
    (h₂ : W₂ * y * W₂⁻¹ = z ∨ W₂ * y * W₂⁻¹ = z⁻¹) :
    (W₂ * W₁) * x * (W₂ * W₁)⁻¹ = z ∨
      (W₂ * W₁) * x * (W₂ * W₁)⁻¹ = z⁻¹ := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · left
    calc
      (W₂ * W₁) * x * (W₂ * W₁)⁻¹ =
          W₂ * (W₁ * x * W₁⁻¹) * W₂⁻¹ := by group
      _ = W₂ * y * W₂⁻¹ := by rw [h₁]
      _ = z := h₂
  · right
    calc
      (W₂ * W₁) * x * (W₂ * W₁)⁻¹ =
          W₂ * (W₁ * x * W₁⁻¹) * W₂⁻¹ := by group
      _ = W₂ * y * W₂⁻¹ := by rw [h₁]
      _ = z⁻¹ := h₂
  · right
    calc
      (W₂ * W₁) * x * (W₂ * W₁)⁻¹ =
          W₂ * (W₁ * x * W₁⁻¹) * W₂⁻¹ := by group
      _ = W₂ * y⁻¹ * W₂⁻¹ := by rw [h₁]
      _ = (W₂ * y * W₂⁻¹)⁻¹ := by group
      _ = z⁻¹ := by rw [h₂]
  · left
    calc
      (W₂ * W₁) * x * (W₂ * W₁)⁻¹ =
          W₂ * (W₁ * x * W₁⁻¹) * W₂⁻¹ := by group
      _ = W₂ * y⁻¹ * W₂⁻¹ := by rw [h₁]
      _ = (W₂ * y * W₂⁻¹)⁻¹ := by group
      _ = (z⁻¹)⁻¹ := by rw [h₂]
      _ = z := inv_inv z

private theorem oneWeyl_conjugatesUpToInverse
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (a b : ι) (hab : a ≠ b) (p q : ι) (hpq : p ≠ q)
    (p' q' : ι) (hp : Equiv.swap a b p = p')
    (hq : Equiv.swap a b q = q') (hp'q' : p' ≠ q') :
    let W := ElementaryWeyl.weyl (S := S) a b hab
    W * elGen p q hpq (1 : S) * W⁻¹ = elGen p' q' hp'q' 1 ∨
      W * elGen p q hpq (1 : S) * W⁻¹ = (elGen p' q' hp'q' 1)⁻¹ := by
  dsimp only
  rcases ElementaryWeyl.weyl_conj_elGen
      a b hab hpq hp hq hp'q' (1 : S) with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (ElementaryWeyl.elGen_neg_eq_inv p' q' hp'q' 1))

private theorem existsPrintedWeylProduct_conjugates_source
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (p q : ι) (hpq : p ≠ q) (v' : ι) (hpv' : p ≠ v') :
    ∃ W : elementaryGroup ι S,
      IsPrintedWeylProduct W ∧
        (W * elGen p q hpq (1 : S) * W⁻¹ = elGen p v' hpv' 1 ∨
          W * elGen p q hpq (1 : S) * W⁻¹ = (elGen p v' hpv' 1)⁻¹) := by
  by_cases hqv' : q = v'
  · subst v'
    exact ⟨1, isPrintedWeylProduct_one, by simp⟩
  · let W := ElementaryWeyl.weyl (S := S) q v' hqv'
    have hconj :
        W * elGen p q hpq (1 : S) * W⁻¹ = elGen p v' hpv' 1 ∨
          W * elGen p q hpq (1 : S) * W⁻¹ = (elGen p v' hpv' 1)⁻¹ :=
      oneWeyl_conjugatesUpToInverse q v' hqv' p q hpq p v'
        (Equiv.swap_apply_of_ne_of_ne hpq hpv')
        (Equiv.swap_apply_left q v') hpv'
    exact ⟨W, isPrintedWeylProduct_weyl q v' hqv', hconj⟩

/-- **Current Weyl-product sentence.**  A finite product of the printed
generalized permutation matrices conjugates any unit root to any prescribed
unit root or its inverse.  The finite list itself, the fact that every entry
is a literal Weyl word, and its product are all visible in the conclusion. -/
def CurrentWeylProductConjugatesUnitRoot : Prop :=
    ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S]
      (j k : ι) (hjk : j ≠ k) (p q : ι) (hpq : p ≠ q),
      ∃ ws : List (elementaryGroup ι S),
        (∀ w ∈ ws, w ∈ printedWeylSet ι S) ∧
          (ws.prod * elGen j k hjk (1 : S) * ws.prod⁻¹ = elGen p q hpq 1 ∨
            ws.prod * elGen j k hjk (1 : S) * ws.prod⁻¹ =
              (elGen p q hpq 1)⁻¹)

theorem manuscriptCurrentWeylProductConjugatesUnitRoot :
    CurrentWeylProductConjugatesUnitRoot := by
  intro ι S _ _ _ j k hjk p q hpq
  have hex : ∃ W : elementaryGroup ι S,
      IsPrintedWeylProduct W ∧
        (W * elGen j k hjk (1 : S) * W⁻¹ = elGen p q hpq 1 ∨
          W * elGen j k hjk (1 : S) * W⁻¹ = (elGen p q hpq 1)⁻¹) := by
    by_cases hjp : j = p
    · subst p
      exact existsPrintedWeylProduct_conjugates_source j k hjk q hpq
    · by_cases hkp : k = p
      · subst p
        let W₁ := ElementaryWeyl.weyl (S := S) j k hjk
        have h₁ :
            W₁ * elGen j k hjk (1 : S) * W₁⁻¹ = elGen k j hjk.symm 1 ∨
              W₁ * elGen j k hjk (1 : S) * W₁⁻¹ =
                (elGen k j hjk.symm 1)⁻¹ :=
          oneWeyl_conjugatesUpToInverse j k hjk j k hjk k j
            (Equiv.swap_apply_left j k) (Equiv.swap_apply_right j k) hjk.symm
        obtain ⟨W₂, hW₂, h₂⟩ :=
          existsPrintedWeylProduct_conjugates_source (S := S)
            k j hjk.symm q hpq
        exact ⟨W₂ * W₁, hW₂.mul (isPrintedWeylProduct_weyl j k hjk),
          conjugatesUpToInverse_comp h₁ h₂⟩
      · let W₁ := ElementaryWeyl.weyl (S := S) j p hjp
        have hpk : p ≠ k := fun hpk ↦ hkp hpk.symm
        have h₁ :
            W₁ * elGen j k hjk (1 : S) * W₁⁻¹ = elGen p k hpk 1 ∨
              W₁ * elGen j k hjk (1 : S) * W₁⁻¹ =
                (elGen p k hpk 1)⁻¹ :=
          oneWeyl_conjugatesUpToInverse j p hjp j k hjk p k
            (Equiv.swap_apply_left j p)
            (Equiv.swap_apply_of_ne_of_ne hjk.symm hkp) hpk
        obtain ⟨W₂, hW₂, h₂⟩ :=
          existsPrintedWeylProduct_conjugates_source (S := S)
            p k hpk q hpq
        exact ⟨W₂ * W₁, hW₂.mul (isPrintedWeylProduct_weyl j p hjp),
          conjugatesUpToInverse_comp h₁ h₂⟩
  obtain ⟨W, ⟨ws, hws, hprod⟩, hconj⟩ := hex
  subst W
  exact ⟨ws, hws, hconj⟩

/-! ## Every coefficient root occurs before generation -/

/-- **Current normal-generation intermediates.**  Under the full printed
hypotheses, the two sandwich commutators produce a unit root, Weyl products
move it to every ordered pair, and one final Steinberg commutator supplies
every coefficient.  The conclusion exposes that universal root membership
before recording that the elementary generators force `N = top`. -/
def CurrentSandwichedRootGivesAllRootsAndTop : Prop :=
    ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S],
      3 ≤ Fintype.card ι →
        ∀ (N : Subgroup (elementaryGroup ι S)) [N.Normal]
          (i j : ι) (hij : i ≠ j) (a x b : S),
          elGen i j hij x ∈ N → a * x * b = 1 →
            (∀ (p q : ι) (hpq : p ≠ q) (r : S), elGen p q hpq r ∈ N) ∧
              N = ⊤

theorem manuscriptCurrentSandwichedRootGivesAllRootsAndTop :
    CurrentSandwichedRootGivesAllRootsAndTop := by
  intro ι S _ _ _ hcard N _ i j hij a x b hx hsandwich
  obtain ⟨k, hki, hkj⟩ := exists_third_index hcard i j
  have hik : i ≠ k := hki.symm
  have hjk : j ≠ k := hkj.symm
  have hxb : elGen i k hik (x * b) ∈ N := by
    have hcomm := commutator_mem_left N hx (elGen j k hjk b)
    rwa [commutatorElement_def,
      elGen_commutator i j k hij hjk hik x b] at hcomm
  have hone : elGen j k hjk (1 : S) ∈ N := by
    have hcomm := RowAnnihilator.commutator_mem_right N
      (elGen j i hij.symm a) hxb
    rw [commutatorElement_def,
      elGen_commutator j i k hij.symm hik hjk a (x * b)] at hcomm
    simpa only [← mul_assoc, hsandwich] using hcomm
  have hunit : ∀ (p q : ι) (hpq : p ≠ q),
      elGen p q hpq (1 : S) ∈ N := by
    intro p q hpq
    exact ElementaryWeyl.elGen_one_mem_of_ne N hjk hone hpq
  have hroot : ∀ (p q : ι) (hpq : p ≠ q) (r : S),
      elGen p q hpq r ∈ N := by
    intro p q hpq r
    obtain ⟨h, hhp, hhq⟩ := exists_third_index hcard p q
    have hph : p ≠ h := hhp.symm
    have hhq' : h ≠ q := hhq
    have hcomm := RowAnnihilator.commutator_mem_right N
      (elGen p h hph r) (hunit h q hhq')
    rwa [commutatorElement_def,
      elGen_commutator p h q hph hhq' hpq r 1, mul_one] at hcomm
  have hquot : ∀ g : elementaryGroup ι S, QuotientGroup.mk' N g = 1 :=
    elementaryGroup_hom_eq_one_of_gens (QuotientGroup.mk' N)
      (fun p q hpq r ↦ (QuotientGroup.eq_one_iff _).mpr
        (hroot p q hpq r))
  have htop : N = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    exact (QuotientGroup.eq_one_iff g).mp (hquot g)
  exact ⟨hroot, htop⟩

#audit_closed_axioms manuscriptCurrentWeylProductConjugatesUnitRoot
#audit_closed_axioms manuscriptCurrentSandwichedRootGivesAllRootsAndTop

end OneSidedMFRadical
end Manuscript
end GroupApproximation
