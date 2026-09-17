import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Walks along dart lists (piece 08, list layer)

Generic list facts for the proper-source-arc step of the Greendlinger least-area leaf
(`OsinSectionPocketFaceSetProperSectionStatement`).

* `Walk f g p L q`: the list `L` is a walk from `p` to `q`, where a dart `d` starts at `g d` and
  ends at `f d`.  For a disc diagram, `g = vertexOf` and `f = vertexOf ∘ alpha`.
* `closed_iff_exists_walk`: the `IsChain`-plus-closing condition of `PocketFaceSet.ClosedWalk` is
  the existence of a closed walk, so a closed walk can be cut along `++` and a stretch with equal
  ends can be removed.
* Four membership facts for a four-part concatenation `l₁ ++ m ++ l₂ ++ l₃` with the middle part
  removed.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08

section Walks

variable {α β : Type*} {f g : α → β}

/-- `Walk f g p L q`: the darts of `L` are consecutive, from `p` to `q`; a dart `d` starts at
`g d` and ends at `f d`. -/
def Walk (f g : α → β) : β → List α → β → Prop
  | p, [], q => p = q
  | p, d :: L, q => g d = p ∧ Walk f g (f d) L q

theorem walk_nil {p q : β} : Walk f g p [] q ↔ p = q := Iff.rfl

theorem walk_cons {p q : β} {d : α} {L : List α} :
    Walk f g p (d :: L) q ↔ g d = p ∧ Walk f g (f d) L q := Iff.rfl

theorem walk_append (L₂ : List α) (q : β) :
    ∀ (L₁ : List α) (p : β),
      Walk f g p (L₁ ++ L₂) q ↔ ∃ r, Walk f g p L₁ r ∧ Walk f g r L₂ q
  | [], p => by
    rw [List.nil_append]
    constructor
    · intro h
      exact ⟨p, walk_nil.mpr rfl, h⟩
    · rintro ⟨r, hr, h⟩
      rw [walk_nil.mp hr]
      exact h
  | d :: L, p => by
    rw [List.cons_append, walk_cons, walk_append L₂ q L (f d)]
    constructor
    · rintro ⟨hd, r, h1, h2⟩
      exact ⟨r, walk_cons.mpr ⟨hd, h1⟩, h2⟩
    · rintro ⟨r, h1, h2⟩
      exact ⟨(walk_cons.mp h1).1, r, (walk_cons.mp h1).2, h2⟩

theorem walk_append_iff {L₁ L₂ : List α} {p q : β} :
    Walk f g p (L₁ ++ L₂) q ↔ ∃ r, Walk f g p L₁ r ∧ Walk f g r L₂ q :=
  walk_append L₂ q L₁ p

theorem walk_cons_iff :
    ∀ (d : α) (L : List α) (p q : β),
      Walk f g p (d :: L) q ↔
        g d = p ∧ (d :: L).IsChain (fun a b => f a = g b) ∧
          f ((d :: L).getLast (List.cons_ne_nil d L)) = q
  | d, [], p, q => by
    rw [walk_cons, walk_nil]
    exact ⟨fun h => ⟨h.1, List.IsChain.singleton d, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  | d, e :: L, p, q => by
    rw [walk_cons, walk_cons_iff e L (f d) q, List.isChain_cons_cons]
    exact ⟨fun h => ⟨h.1, ⟨h.2.1.symm, h.2.2.1⟩, h.2.2.2⟩,
      fun h => ⟨h.1, h.2.1.1.symm, h.2.1.2, h.2.2⟩⟩

/-- A nonempty list is a closed chain exactly when it is a closed walk. -/
theorem closed_iff_exists_walk (L : List α) (hL : L ≠ []) :
    (L.IsChain (fun a b => f a = g b) ∧ f (L.getLast hL) = g (L.head hL)) ↔
      ∃ p, Walk f g p L p := by
  cases L with
  | nil => exact absurd rfl hL
  | cons d L =>
    constructor
    · rintro ⟨hch, hcl⟩
      exact ⟨g d, (walk_cons_iff d L (g d) (g d)).mpr ⟨rfl, hch, hcl⟩⟩
    · rintro ⟨p, hp⟩
      obtain ⟨hd, hch, hcl⟩ := (walk_cons_iff d L p p).mp hp
      exact ⟨hch, hcl.trans hd.symm⟩

end Walks

section FourParts

variable {α : Type*} {l₁ m l₂ l₃ : List α} {x : α}

/-- In a duplicate-free `l₁ ++ m ++ l₂ ++ l₃`, no element of `m` lies in the other parts. -/
theorem not_mem_mid_of_nodup (h : (l₁ ++ m ++ l₂ ++ l₃).Nodup) (hx : x ∈ l₁ ++ l₂ ++ l₃)
    (hm : x ∈ m) : False := by
  rw [List.nodup_append, List.nodup_append, List.nodup_append] at h
  obtain ⟨⟨⟨_, _, D1⟩, _, D2⟩, _, D3⟩ := h
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact D1 x hx x hm rfl
    · exact D2 x (List.mem_append.mpr (Or.inr hm)) x hx rfl
  · exact D3 x (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm)))) x hx rfl

theorem mem_of_mem_mid_append (hx : x ∈ l₁ ++ m ++ l₂ ++ l₃) (hm : x ∉ m) :
    x ∈ l₁ ++ l₂ ++ l₃ := by
  simp only [List.mem_append] at hx ⊢
  rcases hx with ((hx | hx) | hx) | hx
  · exact Or.inl (Or.inl hx)
  · exact absurd hx hm
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

theorem mem_mid (hx : x ∈ m) : x ∈ l₁ ++ m ++ l₂ ++ l₃ := by
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr hx))

theorem mem_of_mem_skip (hx : x ∈ l₁ ++ l₂ ++ l₃) : x ∈ l₁ ++ m ++ l₂ ++ l₃ := by
  simp only [List.mem_append] at hx ⊢
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Or.inl (Or.inl hx))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

theorem nodup_skip (h : (l₁ ++ m ++ l₂ ++ l₃).Nodup) : (l₁ ++ l₂ ++ l₃).Nodup :=
  h.sublist (((List.sublist_append_left l₁ m).append (List.Sublist.refl l₂)).append
    (List.Sublist.refl l₃))

end FourParts

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08
