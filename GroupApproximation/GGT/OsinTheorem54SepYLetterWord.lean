import GroupApproximation.GGT.OsinTheorem54SepZTrick
import GroupApproximation.GGT.OsinTheorem54SepSplice

/-!
# A letter of `Y` spells a word of `Z`

This is the construction Osin's Lemma 5.8 opens with.  A letter `y` of the
enlarged alphabet satisfies `S(1,y;D) = ∅`, so a geodesic from `1` to `y` in
`Γ(G, X ⊔ ℋ)` penetrates nothing essentially: every one of its components has
`d̂_λ`-span at most `Dc`, and is therefore an element of `Z`.  Replacing each
letter of that geodesic by the `Z`-letter of the same value turns the geodesic
into a word over the BASE of `Z` alone --- no components at all --- of the same
length and with the same endpoints.

Two things make the replacement legitimate and both are cheap here.

* A component of a geodesic word is a single letter, so a component's span IS
  the letter's value (`vertex_succ`), and "the span is not deep" reads directly
  as "the value lies in `relBall`".
* The base letters of the geodesic are already letters of `Z`, since `Z`
  contains `X`.  So the case split is only on whether a letter is peripheral.

The output carries the strong form of what it is --- every letter is a `base`
letter of `Z` --- rather than merely `IsLetter`, because the next step needs the
resulting path to have NO components: the components of the spliced path must
be exactly the `ℋ`-letters that were already there, or the isolated-component
argument at the end of Lemma 5.8 has nothing to isolate.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## One letter -/

/-- **A letter with all its peripheral values shallow is a letter of `Z`.** -/
theorem val_mem_base_relGenSetZ (D : RelGenSet G Λ) (Dc : ℕ)
    {a : RelLetter G Λ} (hlet : D.IsLetter a)
    (hball : ∀ mu : Λ, a.IsCompOf mu → a.val ∈ D.relBall mu Dc) :
    a.val ∈ (relGenSetZ D Dc).base := by
  cases a with
  | base x => exact Or.inl hlet
  | comp mu x => exact Or.inr ⟨mu, hball mu rfl⟩

/-- **On a geodesic to a letter of `Y`, every component is shallow.**

If it were not, the component would essentially penetrate its coset and
`S(1,y;D)` would not be empty. -/
theorem mem_relBall_of_isCompOf_of_sepSet_empty (D : RelGenSet G Λ) (Dc : ℕ)
    {y : G} (hy : ∀ lam : Λ, sepSet D lam Dc 1 y = ∅)
    {p : List (RelLetter G Λ)} (hp : IsGeodesicWord D 1 y p) {i : ℕ}
    (hi : i < p.length) {mu : Λ} (hc : (p[i]'hi).IsCompOf mu) :
    (p[i]'hi).val ∈ D.relBall mu Dc := by
  by_contra hnot
  have hcomp : IsComp mu p i (i + 1) := isComp_of_isCompOf_geodesic D mu hp hi hc
  have hspan : (vertex 1 p i)⁻¹ * vertex 1 p (i + 1) = (p[i]'hi).val := by
    rw [vertex_succ p 1 i hi, inv_mul_cancel_left]
  have hess : EssentiallyPenetrates D mu Dc 1 p i (i + 1) := by
    refine ⟨hcomp, ?_⟩
    rw [hspan]
    exact hnot
  have hmem : (QuotientGroup.mk (vertex 1 p i) : G ⧸ D.fam mu)
      ∈ sepSet D mu Dc 1 y := ⟨p, i, i + 1, hp, hess, rfl⟩
  rw [hy mu] at hmem
  exact hmem

/-! ## The word -/

/-- **Reading a word with its peripheral letters demoted to base letters.** -/
def demote (w : List (RelLetter G Λ)) : List (RelLetter G Λ) :=
  w.map (fun a => RelLetter.base a.val)

theorem listVal_demote (w : List (RelLetter G Λ)) :
    RelLetter.listVal (demote w) = RelLetter.listVal w := by
  induction w with
  | nil => rfl
  | cons a t ih =>
      have h1 : RelLetter.listVal (demote (a :: t))
          = a.val * RelLetter.listVal (demote t) := listVal_cons _ _
      have h2 : RelLetter.listVal (a :: t) = a.val * RelLetter.listVal t :=
        listVal_cons a t
      rw [h1, h2, ih]

omit [Group G] in
theorem length_demote (w : List (RelLetter G Λ)) :
    (demote w).length = w.length := by
  simp [demote]

/-- **A geodesic to a letter of `Y` demotes to a word over the base of `Z`.**

Same length, same endpoints, and no peripheral letters left. -/
theorem forall_base_demote_of_sepSet_empty (D : RelGenSet G Λ) (Dc : ℕ)
    {y : G} (hy : ∀ lam : Λ, sepSet D lam Dc 1 y = ∅)
    {p : List (RelLetter G Λ)} (hp : IsGeodesicWord D 1 y p) :
    ∀ b ∈ demote p, ∃ x : G, b = RelLetter.base x ∧
      x ∈ (relGenSetZ D Dc).base := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  refine ⟨a.val, rfl, ?_⟩
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
  subst hia
  exact val_mem_base_relGenSetZ D Dc (hp.1 _ (List.getElem_mem hi))
    (fun mu hmu => mem_relBall_of_isCompOf_of_sepSet_empty D Dc hy hp hi hmu)

end OsinComponents
end GGT
end GroupApproximation
