import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.Meta.AxiomGuard

/-!
# Cutting a word of `X ⊔ ℋ` at the vertices of `H λ`

A word `rest` over the relative alphabet whose value lies in `H λ` is cut, at the vertices it
reads inside `H λ`, into pieces of two kinds.

* `Sum.inl i`: the single `λ`-letter at position `i`, read at a vertex of `H λ`.
* `Sum.inr g`: a maximal stretch reading no `λ`-letter at a vertex of `H λ`, of value `g`.

A stretch starts and ends at vertices of `H λ` (after a cut letter or at `1`, and before a cut
letter or at the end, whose vertex is the value of `rest`), and it traverses no edge of
`Γ_{H λ}`.  Translated by its start vertex, which lies in `H λ`, it is a path from `1` to `g`
avoiding `Γ_{H λ}` (`OsinComponents.avoidsFrom_smul_left`), so `g ∈ D.relBall λ rest.length`.

`exists_cosetPieces` records the cut: the pieces multiply to the value of `rest`, every stretch
value is `d̂_λ`-bounded by the length of `rest`, the `inl` pieces are exactly the `λ`-letters
read at vertices of `H λ`, in increasing order, and there are at most `rest.length + 1` pieces
(an empty stretch contributes no piece).

`mul_mem_relBall` and `mem_relBall_one_of_mem_base` restate `OsinComponents.relBall_mul` and
`OsinComponents.mem_relBall_of_mem_base` in the form the consumers of the cut combine them with.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

universe u w

/-- **The value of a piece.**  `Sum.inl i` is the letter at position `i` of `rest`, and
`Sum.inr g` is the value `g` of a stretch. -/
def pieceVal {G Λ} [Group G] (rest : List (RelLetter G Λ)) : Sum ℕ G → G
  | .inl i => (rest.getD i (RelLetter.base 1)).val
  | .inr g => g

/-- The entry after a prefix is the letter the prefix is followed by. -/
theorem cosetPieces_get_append {α : Type _} (a : α) :
    ∀ (pre t : List α) (hk : pre.length < (pre ++ a :: t).length),
      (pre ++ a :: t).get ⟨pre.length, hk⟩ = a
  | [], _, _ => rfl
  | _ :: pre, t, _ =>
      cosetPieces_get_append a pre t (by rw [List.length_append, List.length_cons]; omega)

/-- `cosetPieces_get_append` at an index given by an equation. -/
theorem cosetPieces_get_split {α : Type _} {rest pre t : List α} {a : α}
    (hsplit : rest = pre ++ a :: t) {k : ℕ} (hkeq : k = pre.length) (hk : k < rest.length) :
    rest.get ⟨k, hk⟩ = a := by
  subst hsplit
  subst hkeq
  exact cosetPieces_get_append a pre t hk

/-- The default-valued entry after a prefix is the letter the prefix is followed by. -/
theorem cosetPieces_getD_append {α : Type _} (a d : α) :
    ∀ (pre t : List α), (pre ++ a :: t).getD pre.length d = a
  | [], _ => by rw [List.nil_append, List.length_nil, List.getD_cons_zero]
  | _ :: pre, t => by
      rw [List.cons_append, List.length_cons, List.getD_cons_succ]
      exact cosetPieces_getD_append a d pre t

section Pieces

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`d̂_λ` is subadditive** (`OsinComponents.relBall_mul`, restated). -/
theorem mul_mem_relBall {D : RelGenSet G Λ} {lam : Λ} {m n : ℕ} {h₁ h₂ : G}
    (h1 : h₁ ∈ D.relBall lam m) (h2 : h₂ ∈ D.relBall lam n) :
    h₁ * h₂ ∈ D.relBall lam (m + n) :=
  OsinComponents.relBall_mul D lam h1 h2

/-- **An element of `H λ` that is a letter of `X` lies in the `d̂_λ`-ball of radius one**
(`OsinComponents.mem_relBall_of_mem_base`, restated). -/
theorem mem_relBall_one_of_mem_base {D : RelGenSet G Λ} {lam : Λ} {x : G}
    (hx : x ∈ D.base) (hfam : x ∈ D.fam lam) : x ∈ D.relBall lam 1 :=
  OsinComponents.mem_relBall_of_mem_base D lam hfam hx

/-- The pieces a stretch contributes: none when it is empty, its value otherwise. -/
def stretchPieces : List (RelLetter G Λ) → List (Sum ℕ G)
  | [] => []
  | a :: t => [Sum.inr (RelLetter.listVal (a :: t))]

theorem prod_map_stretchPieces (rest acc : List (RelLetter G Λ)) :
    ((stretchPieces acc).map (pieceVal rest)).prod = RelLetter.listVal acc := by
  cases acc with
  | nil => rfl
  | cons a t =>
      show [RelLetter.listVal (a :: t)].prod = RelLetter.listVal (a :: t)
      exact mul_one _

theorem mem_stretchPieces {acc : List (RelLetter G Λ)} {x : Sum ℕ G}
    (hx : x ∈ stretchPieces acc) : x = Sum.inr (RelLetter.listVal acc) := by
  cases acc with
  | nil => simp [stretchPieces] at hx
  | cons a t => simpa [stretchPieces] using hx

theorem length_stretchPieces_le (acc : List (RelLetter G Λ)) :
    (stretchPieces acc).length ≤ acc.length := by
  cases acc with
  | nil => exact Nat.le_refl 0
  | cons a t => exact Nat.succ_le_succ (Nat.zero_le t.length)

theorem filterMap_stretchPieces (acc : List (RelLetter G Λ)) :
    (stretchPieces acc).filterMap Sum.getLeft? = [] := by
  cases acc with
  | nil => rfl
  | cons a t => rfl

/-- The vertex reached after a prefix is the value of the prefix. -/
theorem cosetPieces_vertex_append (v : G) (w₁ w₂ : List (RelLetter G Λ)) :
    OsinComponents.vertex v (w₁ ++ w₂) w₁.length = v * RelLetter.listVal w₁ := by
  induction w₁ generalizing v with
  | nil =>
      rw [List.nil_append, List.length_nil, OsinComponents.vertex_zero, RelLetter.listVal_nil,
        mul_one]
  | cons a t ih =>
      rw [List.cons_append, List.length_cons, OsinComponents.vertex_cons_succ, ih,
        OsinComponents.listVal_cons, mul_assoc]

/-- **A stretch between two vertices of `H λ` that avoids `Γ_{H λ}` has `d̂_λ`-bounded value.**
Translating by the start vertex `listVal pre ∈ H λ` moves the start to `1`. -/
theorem cosetPieces_stretch_mem_relBall {D : RelGenSet G Λ} {lam : Λ}
    {rest pre acc w : List (RelLetter G Λ)}
    (hrest : ∀ a ∈ rest, D.IsLetter a) (hsplit : rest = pre ++ acc ++ w)
    (hpre : RelLetter.listVal pre ∈ D.fam lam)
    (hend : RelLetter.listVal pre * RelLetter.listVal acc ∈ D.fam lam)
    (hav : AvoidsFrom D.fam lam acc (RelLetter.listVal pre)) :
    RelLetter.listVal acc ∈ D.relBall lam rest.length := by
  have hacc : RelLetter.listVal acc ∈ D.fam lam := by
    have h := mul_mem (inv_mem hpre) hend
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h
  refine ⟨hacc, acc, ?_, rfl, ?_, ?_⟩
  · intro a ha
    apply hrest a
    rw [hsplit]
    exact List.mem_append_left w (List.mem_append_right pre ha)
  · have h := (OsinComponents.avoidsFrom_smul_left (inv_mem hpre) acc
      (RelLetter.listVal pre)).mpr hav
    rwa [inv_mul_cancel] at h
  · rw [hsplit, List.length_append, List.length_append]
    omega

/-- **The cut, from a position onwards.**  `rest = pre ++ acc ++ w`, the prefix `pre` ends at a
vertex of `H λ`, and the stretch `acc` accumulated since then avoids `Γ_{H λ}`.  The pieces of
`acc ++ w` multiply to its value, their stretch values are `d̂_λ`-bounded, and their `inl` pieces
are exactly the `λ`-letters of `w` read at vertices of `H λ`, in increasing order. -/
theorem exists_cosetPieces_aux (D : RelGenSet G Λ) (lam : Λ) (rest : List (RelLetter G Λ))
    (hrest : ∀ a ∈ rest, D.IsLetter a) (hval : RelLetter.listVal rest ∈ D.fam lam) :
    ∀ (w pre acc : List (RelLetter G Λ)), rest = pre ++ acc ++ w →
      RelLetter.listVal pre ∈ D.fam lam → AvoidsFrom D.fam lam acc (RelLetter.listVal pre) →
      ∃ pieces : List (Sum ℕ G),
        (pieces.map (pieceVal rest)).prod = RelLetter.listVal acc * RelLetter.listVal w ∧
        (∀ g, Sum.inr g ∈ pieces → g ∈ D.relBall lam rest.length) ∧
        (∀ i, Sum.inl i ∈ pieces → pre.length + acc.length ≤ i ∧ ∃ hi : i < rest.length,
          RelLetter.IsCompOf lam (rest.get ⟨i, hi⟩) ∧
            OsinComponents.vertex 1 rest i ∈ D.fam lam) ∧
        (∀ i (hi : i < rest.length), pre.length + acc.length ≤ i →
          RelLetter.IsCompOf lam (rest.get ⟨i, hi⟩) →
            OsinComponents.vertex 1 rest i ∈ D.fam lam → Sum.inl i ∈ pieces) ∧
        (pieces.filterMap Sum.getLeft?).Pairwise (· < ·) ∧
        pieces.length ≤ acc.length + w.length := by
  intro w
  induction w with
  | nil =>
      intro pre acc hsplit hpre hav
      have hend : RelLetter.listVal pre * RelLetter.listVal acc ∈ D.fam lam := by
        have h : RelLetter.listVal rest = RelLetter.listVal pre * RelLetter.listVal acc := by
          rw [hsplit, List.append_nil, OsinComponents.listVal_append]
        rw [← h]
        exact hval
      have hlen : rest.length = pre.length + acc.length := by
        rw [hsplit, List.append_nil, List.length_append]
      refine ⟨stretchPieces acc, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [prod_map_stretchPieces, RelLetter.listVal_nil, mul_one]
      · intro g hg
        obtain rfl := Sum.inr.inj (mem_stretchPieces hg)
        exact cosetPieces_stretch_mem_relBall hrest hsplit hpre hend hav
      · intro i hi
        exact absurd (mem_stretchPieces hi) Sum.inl_ne_inr
      · intro i hi hle _ _
        exfalso
        omega
      · rw [filterMap_stretchPieces]
        exact List.Pairwise.nil
      · rw [List.length_nil, Nat.add_zero]
        exact length_stretchPieces_le acc
  | cons a t ih =>
      intro pre acc hsplit hpre hav
      have hsplit' : rest = (pre ++ acc) ++ a :: t := hsplit
      have hlen : rest.length = pre.length + acc.length + (t.length + 1) := by
        rw [hsplit, List.length_append, List.length_append, List.length_cons]
      have hk : pre.length + acc.length < rest.length := by omega
      have hget : rest.get ⟨pre.length + acc.length, hk⟩ = a :=
        cosetPieces_get_split hsplit' (by rw [List.length_append]) hk
      have hpieceVal : pieceVal rest (Sum.inl (pre.length + acc.length)) = a.val := by
        show (rest.getD (pre.length + acc.length) (RelLetter.base 1)).val = a.val
        rw [hsplit', ← List.length_append, cosetPieces_getD_append]
      have hvert : OsinComponents.vertex 1 rest (pre.length + acc.length)
          = RelLetter.listVal pre * RelLetter.listVal acc := by
        rw [hsplit', ← List.length_append, cosetPieces_vertex_append, one_mul,
          OsinComponents.listVal_append]
      have ha : D.IsLetter a := by
        apply hrest a
        rw [hsplit']
        exact List.mem_append_right _ List.mem_cons_self
      by_cases hbreak : RelLetter.IsCompOf lam a ∧
          RelLetter.listVal pre * RelLetter.listVal acc ∈ D.fam lam
      · -- `a` is a `λ`-letter read at a vertex of `H λ`: close the stretch and cut
        obtain ⟨hc, hmem⟩ := hbreak
        have haval : a.val ∈ D.fam lam := by
          cases a with
          | base x => exact False.elim hc
          | comp mu h =>
              have e : mu = lam := hc
              rw [← e]
              exact ha
        have hpre' : RelLetter.listVal (pre ++ acc ++ [a]) ∈ D.fam lam := by
          rw [OsinComponents.listVal_append, OsinComponents.listVal_append,
            OsinComponents.listVal_cons, RelLetter.listVal_nil, mul_one]
          exact mul_mem hmem haval
        obtain ⟨pieces', hprod', hinr', hinl', hall', hpair', hlen'⟩ :=
          ih (pre ++ acc ++ [a]) [] (by rw [hsplit]; simp) hpre' trivial
        refine ⟨stretchPieces acc ++ Sum.inl (pre.length + acc.length) :: pieces',
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.map_append, List.prod_append, prod_map_stretchPieces, List.map_cons,
            List.prod_cons, hpieceVal, hprod', RelLetter.listVal_nil, one_mul,
            OsinComponents.listVal_cons]
        · intro g hg
          rcases List.mem_append.mp hg with hg | hg
          · obtain rfl := Sum.inr.inj (mem_stretchPieces hg)
            exact cosetPieces_stretch_mem_relBall hrest hsplit hpre hmem hav
          · rcases List.mem_cons.mp hg with hg | hg
            · exact absurd hg.symm Sum.inl_ne_inr
            · exact hinr' g hg
        · intro i hi
          rcases List.mem_append.mp hi with hi | hi
          · exact absurd (mem_stretchPieces hi) Sum.inl_ne_inr
          · rcases List.mem_cons.mp hi with hi | hi
            · obtain rfl := Sum.inl.inj hi
              refine ⟨Nat.le_refl _, hk, ?_, ?_⟩
              · rw [hget]
                exact hc
              · rw [hvert]
                exact hmem
            · obtain ⟨hle, hrest'⟩ := hinl' i hi
              refine ⟨?_, hrest'⟩
              simp only [List.length_append, List.length_cons, List.length_nil] at hle
              omega
        · intro i hi hle hc' hv'
          by_cases hlt : pre.length + acc.length < i
          · apply List.mem_append_right
            apply List.mem_cons_of_mem
            refine hall' i hi ?_ hc' hv'
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · have hi' : i = pre.length + acc.length := by omega
            subst hi'
            exact List.mem_append_right _ List.mem_cons_self
        · have hfm : (stretchPieces acc ++ Sum.inl (pre.length + acc.length) :: pieces').filterMap
              Sum.getLeft? = (pre.length + acc.length) :: pieces'.filterMap Sum.getLeft? := by
            rw [List.filterMap_append, filterMap_stretchPieces, List.nil_append]
            rfl
          rw [hfm]
          refine List.pairwise_cons.mpr ⟨?_, hpair'⟩
          intro j hj
          obtain ⟨x, hx, hxj⟩ := List.mem_filterMap.mp hj
          cases x with
          | inl j' =>
              have e : j' = j := Option.some.inj hxj
              subst e
              have h1 := (hinl' j' hx).1
              simp only [List.length_append, List.length_cons, List.length_nil] at h1
              omega
          | inr g => simp at hxj
        · have hs := length_stretchPieces_le acc
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen' ⊢
          omega
      · -- `a` extends the stretch
        have hav' : AvoidsFrom D.fam lam (acc ++ [a]) (RelLetter.listVal pre) :=
          (OsinComponents.avoidsFrom_append D.fam lam acc [a] (RelLetter.listVal pre)).mpr
            ⟨hav, hbreak, trivial⟩
        obtain ⟨pieces', hprod', hinr', hinl', hall', hpair', hlen'⟩ :=
          ih pre (acc ++ [a]) (by rw [hsplit]; simp) hpre hav'
        refine ⟨pieces', ?_, hinr', ?_, ?_, hpair', ?_⟩
        · rw [hprod', OsinComponents.listVal_append, OsinComponents.listVal_cons,
            OsinComponents.listVal_cons, RelLetter.listVal_nil, mul_one, mul_assoc]
        · intro i hi
          obtain ⟨hle, hrest'⟩ := hinl' i hi
          refine ⟨?_, hrest'⟩
          simp only [List.length_append, List.length_cons, List.length_nil] at hle
          omega
        · intro i hi hle hc' hv'
          by_cases hlt : pre.length + acc.length < i
          · refine hall' i hi ?_ hc' hv'
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · exfalso
            have hi' : i = pre.length + acc.length := by omega
            subst hi'
            rw [hget] at hc'
            rw [hvert] at hv'
            exact hbreak ⟨hc', hv'⟩
        · simp only [List.length_append, List.length_cons, List.length_nil] at hlen' ⊢
          omega

/-- **Cutting a word at the vertices of `H λ`.**  A word of admissible letters whose value lies
in `H λ` is the ordered product of its pieces: the `λ`-letters read at vertices of `H λ`
(`Sum.inl i`, all of them, in increasing order) and the maximal stretches between them
(`Sum.inr g`, each of value in the `d̂_λ`-ball of radius `rest.length`), at most
`rest.length + 1` pieces in all. -/
theorem exists_cosetPieces {G : Type u} [Group G] {Λ : Type w} (D : RelGenSet G Λ) (lam : Λ) (rest : List (RelLetter G Λ)) (hrest : ∀ a ∈ rest, D.IsLetter a) (hval : RelLetter.listVal rest ∈ D.fam lam) :
  ∃ pieces : List (Sum ℕ G),
    (pieces.map (pieceVal rest)).prod = RelLetter.listVal rest ∧
    (∀ g, Sum.inr g ∈ pieces → g ∈ D.relBall lam rest.length) ∧
    (∀ i, Sum.inl i ∈ pieces → ∃ hi : i < rest.length, RelLetter.IsCompOf lam (rest.get ⟨i, hi⟩) ∧ OsinComponents.vertex 1 rest i ∈ D.fam lam) ∧
    (∀ i (hi : i < rest.length), RelLetter.IsCompOf lam (rest.get ⟨i, hi⟩) → OsinComponents.vertex 1 rest i ∈ D.fam lam → Sum.inl i ∈ pieces) ∧
    (pieces.filterMap Sum.getLeft?).Pairwise (· < ·) ∧ pieces.length ≤ rest.length + 1 := by
  obtain ⟨pieces, hprod, hinr, hinl, hall, hpair, hlen⟩ :=
    exists_cosetPieces_aux D lam rest hrest hval rest [] [] rfl (one_mem (D.fam lam)) trivial
  refine ⟨pieces, ?_, hinr, fun i hi => (hinl i hi).2,
    fun i hi hc hv => hall i hi (Nat.zero_le i) hc hv, hpair, ?_⟩
  · rw [hprod, RelLetter.listVal_nil, one_mul]
  · rw [List.length_nil, Nat.zero_add] at hlen
    omega

end Pieces

end RelHyp
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.RelHyp.mul_mem_relBall
#audit_axioms GroupApproximation.GGT.RelHyp.mem_relBall_one_of_mem_base
#audit_axioms GroupApproximation.GGT.RelHyp.exists_cosetPieces_aux
#audit_axioms GroupApproximation.GGT.RelHyp.exists_cosetPieces
