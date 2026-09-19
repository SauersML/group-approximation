import GroupApproximation.ClassTransposition.Presentation.Basic
import GroupApproximation.ClassTransposition.Presentation.Statement

/-!
# The transposition presentation of `CT_P(ℤ)` and its evaluation map

Research nodes: `class-transposition-presentation-has-central-kernel`,
`class-transposition-relations-present-ct-p-z` (Kourovka 17.61 lane).

A box is *admissible* for `P : Set ℕ` if its modulus is smooth over `P` (`IsSmoothModulus`, verbatim
from the challenge file). `TranspGroup P` has one generator `t(A,B)` for each ordered pair of
disjoint admissible boxes, and these relations:
* `t(A,B) = t(B,A)`;
* `t(A,B)² = 1`;
* `t(C,D) t(A,B) t(C,D) = t(A',B')` whenever the swap of `C, D` maps `A` onto `A'` and `B` onto
  `B'` canonically;
* `t(A,B) = ∏_{j<k} t(A_j, B_j)` for the `k`-children `A_j = place A (child k j)`, whenever these
  are admissible.

Main results:
* `eval P : TranspGroup P →* Perm ℤ` sends `t(A,B)` to the class transposition;
* `eval_range`: its range is exactly `classTranspositionGroupOver P`;
* `ctEquiv`: if `eval P` is injective (the research claim), then `TranspGroup P ≃* CT_P(ℤ)`;
* `kourovka1761Statement_of`: Kourovka 17.61 follows from injectivity together with finite
  presentability of `TranspGroup P`.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- `B` is admissible for `P`: its modulus has no prime factor outside `P ∪ {2}`. -/
def Adm (P : Set ℕ) (B : Box) : Prop := IsSmoothModulus P B.m

/-- Children of an admissible box under a smooth split are admissible. -/
theorem adm_kid {P : Set ℕ} {A : Box} {k : ℕ} (hk : IsSmoothModulus P (k : ℤ)) (hA : Adm P A)
    (j : Fin k) : Adm P (place A (child k j)) := by
  intro p hp hdvd
  rw [place_m, child_m] at hdvd
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h | h
  · exact hk p hp h
  · exact hA p hp h

/-- A generator `t(A,B)`: an ordered pair of disjoint admissible boxes. -/
structure Gen (P : Set ℕ) where
  A : Box
  B : Box
  disj : A.Disj B
  admA : Adm P A
  admB : Adm P B

/-- The generator with its two boxes exchanged. -/
def Gen.flip {P : Set ℕ} (g : Gen P) : Gen P := ⟨g.B, g.A, g.disj.symm, g.admB, g.admA⟩

/-- The `j`-th pair of `k`-children of a generator, given that it is admissible. -/
def Gen.kid {P : Set ℕ} (g : Gen P) (k : ℕ) (j : Fin k)
    (hA : Adm P (place g.A (child k j))) (hB : Adm P (place g.B (child k j))) : Gen P :=
  ⟨place g.A (child k j), place g.B (child k j), disj_place_of g.disj, hA, hB⟩

/-- The relations of the transposition presentation. -/
inductive Rel (P : Set ℕ) : FreeGroup (Gen P) → Prop
  | symm (g : Gen P) : Rel P (FreeGroup.of g * (FreeGroup.of g.flip)⁻¹)
  | sq (g : Gen P) : Rel P (FreeGroup.of g * FreeGroup.of g)
  | conj (c g g' : Gen P) (hA : CanonOn (swap c.A c.B c.disj) g.A g'.A)
      (hB : CanonOn (swap c.A c.B c.disj) g.B g'.B) :
      Rel P (FreeGroup.of c * FreeGroup.of g * FreeGroup.of c * (FreeGroup.of g')⁻¹)
  | split (g : Gen P) (k : ℕ) (hk : 0 < k)
      (hc : ∀ j : Fin k, Adm P (place g.A (child k j)) ∧ Adm P (place g.B (child k j))) :
      Rel P (FreeGroup.of g *
        ((List.finRange k).map fun j => FreeGroup.of (g.kid k j (hc j).1 (hc j).2)).prod⁻¹)

/-- The group presented by the transposition relations (`Γ_P` in the research nodes). -/
abbrev TranspGroup (P : Set ℕ) : Type := PresentedGroup {r | Rel P r}

/-- A generator evaluates to its class transposition. -/
noncomputable def evalGen (P : Set ℕ) (g : Gen P) : Perm ℤ := swap g.A g.B g.disj

theorem rel_eval (P : Set ℕ) :
    ∀ r ∈ {r | Rel P r}, FreeGroup.lift (evalGen P) r = 1 := by
  intro r hr
  change Rel P r at hr
  cases hr with
  | symm g =>
    rw [map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, mul_inv_eq_one]
    exact swap_comm g.disj
  | sq g =>
    rw [map_mul, FreeGroup.lift_apply_of]
    exact swap_mul_self g.disj
  | conj c g g' hA hB =>
    rw [map_mul, map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, mul_inv_eq_one]
    show swap c.A c.B c.disj * swap g.A g.B g.disj * swap c.A c.B c.disj = swap g'.A g'.B g'.disj
    have key := conj_swap (c := swap c.A c.B c.disj) g.disj g'.disj hA hB
    rwa [swap_inv c.disj] at key
  | split g k hk hc =>
    rw [map_mul, map_inv, map_list_prod, List.map_map, mul_inv_eq_one, FreeGroup.lift_apply_of]
    show swap g.A g.B g.disj = _
    rw [← swap_split g.disj k hk]
    congr 1

/-- The evaluation map `t(A,B) ↦` the class transposition of `A` and `B`. -/
noncomputable def eval (P : Set ℕ) : TranspGroup P →* Perm ℤ :=
  PresentedGroup.toGroup (rel_eval P)

@[simp] theorem eval_of (P : Set ℕ) (g : Gen P) :
    eval P (PresentedGroup.of g) = swap g.A g.B g.disj :=
  PresentedGroup.toGroup.of (rel_eval P)

/-! ### The image of `eval` is `CT_P(ℤ)` -/

theorem isClassTranspositionOver_swap {P : Set ℕ} {A B : Box} (h : A.Disj B) (hA : Adm P A)
    (hB : Adm P B) : IsClassTranspositionOver P (swap A B h) := by
  refine ⟨A.r, A.m, B.r, B.m, hA, hB, A.hr, A.hrm, B.hr, B.hrm, ?_, ?_, ?_⟩
  · intro t₁ t₂ he
    exact h _ (A.elt_mem t₁) (by rw [he]; exact B.elt_mem t₂)
  · intro t; exact ⟨swap_canon h t, swap_canon' h t⟩
  · intro n h1 h2
    apply swap_fix h
    · intro hA'; obtain ⟨t, ht⟩ := (A.mem_iff n).1 hA'; exact h1 t ht
    · intro hB'; obtain ⟨t, ht⟩ := (B.mem_iff n).1 hB'; exact h2 t ht

/-- Every class transposition over `P` is the swap of two disjoint admissible boxes. -/
theorem IsClassTranspositionOver.eq_swap {P : Set ℕ} {g : Perm ℤ}
    (hg : IsClassTranspositionOver P g) :
    ∃ (A B : Box) (h : A.Disj B), Adm P A ∧ Adm P B ∧ g = swap A B h := by
  obtain ⟨r₁, m₁, r₂, m₂, s1, s2, h1, h2, h3, h4, hd, hmap, hfix⟩ := hg
  have hAB : Box.Disj ⟨r₁, m₁, h1, h2⟩ ⟨r₂, m₂, h3, h4⟩ := by
    intro n ha hb
    obtain ⟨t₁, rfl⟩ := (Box.mem_iff _ n).1 ha
    obtain ⟨t₂, ht₂⟩ := (Box.mem_iff _ _).1 hb
    exact hd t₁ t₂ ht₂
  refine ⟨_, _, hAB, s1, s2, swap_eq_of g hAB (fun t => (hmap t).1) (fun t => (hmap t).2) ?_⟩
  intro n ha hb
  apply hfix
  · intro t ht; exact ha (by rw [ht]; exact Box.elt_mem _ t)
  · intro t ht; exact hb (by rw [ht]; exact Box.elt_mem _ t)

theorem eval_mem (P : Set ℕ) (x : TranspGroup P) : eval P x ∈ classTranspositionGroupOver P := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
  induction w using FreeGroup.induction_on with
  | C1 => simp only [map_one]; exact Subgroup.one_mem _
  | of g =>
    show eval P (PresentedGroup.of g) ∈ _
    rw [eval_of]
    exact Subgroup.subset_closure (isClassTranspositionOver_swap g.disj g.admA g.admB)
  | inv_of g ih =>
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ ih
  | mul a b iha ihb =>
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ iha ihb

/-- The range of the evaluation map is exactly Kohl's `CT_P(ℤ)`. -/
theorem eval_range (P : Set ℕ) : (eval P).range = classTranspositionGroupOver P := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    exact eval_mem P x
  · rw [classTranspositionGroupOver, Subgroup.closure_le]
    intro g hg
    obtain ⟨A, B, h, hA, hB, rfl⟩ := IsClassTranspositionOver.eq_swap hg
    exact MonoidHom.mem_range.2 ⟨PresentedGroup.of ⟨A, B, h, hA, hB⟩, eval_of P _⟩

/-- If the transposition relations present `CT_P(ℤ)` (research claim
`class-transposition-relations-present-ct-p-z`), the presented group is `CT_P(ℤ)`. -/
noncomputable def ctEquiv (P : Set ℕ) (hinj : Function.Injective (eval P)) :
    TranspGroup P ≃* classTranspositionGroupOver P :=
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (eval_range P))

/-- Kourovka 17.61 reduces to two claims about the transposition presentation, for every finite
set `P` of odd primes:
* the relations present `CT_P(ℤ)` (`class-transposition-relations-present-ct-p-z`);
* the presented group is finitely presented (`ct-p-z-has-a-finite-class-transposition-presentation`). -/
theorem kourovka1761Statement_of
    (h : ∀ P : Set ℕ, P.Finite → (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      Function.Injective (eval P) ∧ Group.IsFinitelyPresented (TranspGroup P)) :
    kourovka1761Statement := by
  intro P hP hodd
  obtain ⟨hinj, hfp⟩ := h P hP hodd
  exact Group.IsFinitelyPresented.equiv (ctEquiv P hinj)

end GroupApproximation.ClassTransposition.Presentation
