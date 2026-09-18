import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-17: cyclic blocks do not interleave

This is the list layer of lane `gl-p07-17` (`lanes/carto-gl-p07.md`).  It is the converse of
`FourPiece.exists_rotate_block`.  The lane's mathematics is in `NoninterleaveStatement.lean`.

## Statements

* `cyclicNoInterleave_of_rotate_eq_append`: if `l.rotate m = V ++ W`, with `V` inside `A` and `W`
  outside `A`, then `CyclicNoInterleave A l`.
* `cyclicNoInterleave_of_four_blocks`: suppose `l.rotate n = U₁ ++ U₂ ++ U₃ ++ U₄`, with `U₁`
  inside `A`, `U₃` outside `A`, and each of `U₂`, `U₄` uniform (all inside or all outside).
  Then `CyclicNoInterleave A l`.

## Proof

* **Triple lemma.**  Let `P, R` lie in `B` and `Q` lie outside `B`.  Then `P ++ Q ++ R` has no
  sublist `[x, y, z]` with pattern `¬B, B, ¬B`.  Induct on `P`, then on `Q`.
  * A head in `P` cannot be `x`.
  * A head in `Q` taken as `x` leaves `[y, z]` in `Q' ++ R`.  There `y ∈ B` forces `y ∈ R`, and
    then `z ∈ R`.
* **Rotations.**  `V ++ W ~r l.rotate n`, so `l.rotate n = (V ++ W).rotate k`.  Write this as
  `drop k' ++ take k'` with `k' = k % |V ++ W|`.
  * If `k' ≤ |V|`, the rotation reads `V.drop k' ++ W ++ V.take k'`, blocks `A, ¬A, A`.
  * Otherwise it reads `W.drop _ ++ V ++ W.take _`, blocks `¬A, A, ¬A`.
* **Alternations.**  An alternation `x, y, z, t` contains both `¬A, A, ¬A` and `A, ¬A, A` as
  sublists of three entries.  So the triple lemma, applied to `B = A` or to `B = ¬A`, refutes
  both alternations.
* **Four blocks.**  Rotate by `|U₁ ++ U₂ ++ U₃|` when `U₄` lies in `A`.  The `A`-part is then
  `U₁`, `U₁ ++ U₂`, `U₄ ++ U₁` or `U₄ ++ U₁ ++ U₂`, and it is followed by its complement.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece

section Lists

variable {α : Type*}

/-- A pair `B, ¬B` in this order does not sit in `Q ++ R` with `Q` outside `B` and `R` in `B`. -/
theorem not_sublist_pair_of_blocks {B : α → Prop} {Q R : List α} (hQ : ∀ x ∈ Q, ¬ B x)
    (hR : ∀ x ∈ R, B x) {y z : α} (hs : [y, z] <+ Q ++ R) (hy : B y) (hz : ¬ B z) : False := by
  induction Q with
  | nil =>
    rw [List.nil_append] at hs
    exact hz (hR z (hs.subset (by simp)))
  | cons a Q ih =>
    rw [List.cons_append, List.sublist_cons_iff] at hs
    rcases hs with hs | ⟨r, hr, -⟩
    · exact ih (fun x hx => hQ x (List.mem_cons_of_mem a hx)) hs
    · have hya : y = a := (List.cons.inj hr).1
      exact hQ a (by simp) (by rw [← hya]; exact hy)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.not_sublist_pair_of_blocks

/-- A triple `¬B, B, ¬B` does not sit in `P ++ Q ++ R` with `P, R` in `B` and `Q` outside `B`. -/
theorem not_sublist_triple_of_blocks {B : α → Prop} {P Q R : List α} (hP : ∀ x ∈ P, B x)
    (hQ : ∀ x ∈ Q, ¬ B x) (hR : ∀ x ∈ R, B x) {x y z : α} (hs : [x, y, z] <+ P ++ Q ++ R)
    (hx : ¬ B x) (hy : B y) (hz : ¬ B z) : False := by
  induction P with
  | nil =>
    rw [List.nil_append] at hs
    induction Q with
    | nil =>
      rw [List.nil_append] at hs
      exact hx (hR x (hs.subset (by simp)))
    | cons a Q ih =>
      rw [List.cons_append, List.sublist_cons_iff] at hs
      rcases hs with hs | ⟨r, hr, hrs⟩
      · exact ih (fun u hu => hQ u (List.mem_cons_of_mem a hu)) hs
      · obtain ⟨-, rfl⟩ := List.cons.inj hr
        exact not_sublist_pair_of_blocks (fun u hu => hQ u (List.mem_cons_of_mem a hu)) hR hrs
          hy hz
  | cons a P ih =>
    rw [List.cons_append, List.cons_append, List.sublist_cons_iff] at hs
    rcases hs with hs | ⟨r, hr, -⟩
    · exact ih (fun u hu => hP u (List.mem_cons_of_mem a hu)) hs
    · have hxa : x = a := (List.cons.inj hr).1
      exact hx (by rw [hxa]; exact hP a (by simp))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.not_sublist_triple_of_blocks

/-- **A cyclic block does not interleave.**  If a rotation of `l` is `V ++ W`, with `V` inside
`A` and `W` outside `A`, then no rotation of `l` alternates in `A`. -/
theorem cyclicNoInterleave_of_rotate_eq_append {A : α → Prop} {l V W : List α} {m : ℕ}
    (hrot : l.rotate m = V ++ W) (hV : ∀ x ∈ V, A x) (hW : ∀ x ∈ W, ¬ A x) :
    CyclicNoInterleave A l := by
  intro n x y z t hs
  have h₁ : V ++ W ~r l := by
    rw [← hrot]
    exact List.IsRotated.forall l m
  obtain ⟨k, hk⟩ := h₁.trans (List.IsRotated.forall l n).symm
  have sub₁ : [y, z, t] <+ [x, y, z, t] := List.Sublist.cons x (List.Sublist.refl _)
  have sub₂ : [x, y, z] <+ [x, y, z, t] :=
    List.Sublist.cons_cons x (List.Sublist.cons_cons y
      (List.Sublist.cons_cons z (List.nil_sublist [t])))
  rw [← hk, List.rotate_eq_drop_append_take_mod, List.drop_append, List.take_append] at hs
  generalize k % (V ++ W).length = k' at hs
  by_cases hle : k' ≤ V.length
  · rw [Nat.sub_eq_zero_of_le hle, List.drop_zero, List.take_zero, List.append_nil] at hs
    have hP : ∀ u ∈ V.drop k', A u := fun u hu => hV u (List.mem_of_mem_drop hu)
    have hR : ∀ u ∈ V.take k', A u := fun u hu => hV u (List.mem_of_mem_take hu)
    refine ⟨fun ⟨_, hy, hz, ht⟩ => ?_, fun ⟨hx, hy, hz, _⟩ => ?_⟩
    · exact not_sublist_triple_of_blocks hP hW hR (sub₁.trans hs) hy hz ht
    · exact not_sublist_triple_of_blocks hP hW hR (sub₂.trans hs) hx hy hz
  · have hle' : V.length ≤ k' := by omega
    rw [List.drop_eq_nil_of_le hle', List.take_of_length_le hle', List.nil_append,
      ← List.append_assoc] at hs
    have hP : ∀ u ∈ W.drop (k' - V.length), ¬ A u :=
      fun u hu => hW u (List.mem_of_mem_drop hu)
    have hR : ∀ u ∈ W.take (k' - V.length), ¬ A u :=
      fun u hu => hW u (List.mem_of_mem_take hu)
    have hQ : ∀ u ∈ V, ¬ ¬ A u := fun u hu h => h (hV u hu)
    refine ⟨fun ⟨hx, hy, hz, _⟩ => ?_, fun ⟨_, hy, hz, ht⟩ => ?_⟩
    · exact not_sublist_triple_of_blocks (B := fun u => ¬ A u) hP hQ hR (sub₂.trans hs)
        (fun h => h hx) hy (fun h => h hz)
    · exact not_sublist_triple_of_blocks (B := fun u => ¬ A u) hP hQ hR (sub₁.trans hs)
        (fun h => h hy) hz (fun h => h ht)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.cyclicNoInterleave_of_rotate_eq_append

/-- Every entry of an append satisfies `p` when every entry of both parts does. -/
theorem all_append {p : α → Prop} {l₁ l₂ : List α} (h₁ : ∀ x ∈ l₁, p x) (h₂ : ∀ x ∈ l₂, p x) :
    ∀ x ∈ l₁ ++ l₂, p x :=
  fun x hx => (List.mem_append.mp hx).elim (h₁ x) (h₂ x)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.all_append

/-- Rotating four blocks by the length of the first three. -/
theorem rotate_four_last {l U₁ U₂ U₃ U₄ : List α} {n : ℕ}
    (hrot : l.rotate n = U₁ ++ U₂ ++ U₃ ++ U₄) :
    l.rotate (n + (U₁ ++ U₂ ++ U₃).length) = U₄ ++ U₁ ++ U₂ ++ U₃ := by
  rw [← List.rotate_rotate, hrot, List.rotate_append_length_eq]
  simp only [List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.rotate_four_last

/-- Rotating four blocks by the length of the first two. -/
theorem rotate_four_mid {l U₁ U₂ U₃ U₄ : List α} {n : ℕ}
    (hrot : l.rotate n = U₁ ++ U₂ ++ U₃ ++ U₄) :
    l.rotate (n + (U₁ ++ U₂).length) = U₃ ++ U₄ ++ U₁ ++ U₂ := by
  rw [← List.rotate_rotate, hrot, List.append_assoc (U₁ ++ U₂), List.rotate_append_length_eq]
  simp only [List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.rotate_four_mid

/-- **Four uniform blocks do not interleave.**  Suppose a rotation of `l` reads
`U₁ ++ U₂ ++ U₃ ++ U₄`, with `U₁` inside `A`, `U₃` outside `A`, and `U₂`, `U₄` each uniform.
Then `l` does not interleave in `A`. -/
theorem cyclicNoInterleave_of_four_blocks {A : α → Prop} {l U₁ U₂ U₃ U₄ : List α} {n : ℕ}
    (hrot : l.rotate n = U₁ ++ U₂ ++ U₃ ++ U₄) (h₁ : ∀ x ∈ U₁, A x) (h₃ : ∀ x ∈ U₃, ¬ A x)
    (h₂ : (∀ x ∈ U₂, A x) ∨ ∀ x ∈ U₂, ¬ A x) (h₄ : (∀ x ∈ U₄, A x) ∨ ∀ x ∈ U₄, ¬ A x) :
    CyclicNoInterleave A l := by
  rcases h₄ with h₄ | h₄
  · rcases h₂ with h₂ | h₂
    · exact cyclicNoInterleave_of_rotate_eq_append (V := U₄ ++ U₁ ++ U₂) (W := U₃)
        (rotate_four_last hrot) (all_append (all_append h₄ h₁) h₂) h₃
    · exact cyclicNoInterleave_of_rotate_eq_append (V := U₄ ++ U₁) (W := U₂ ++ U₃)
        ((rotate_four_last hrot).trans (List.append_assoc (U₄ ++ U₁) U₂ U₃))
        (all_append h₄ h₁) (all_append h₂ h₃)
  · rcases h₂ with h₂ | h₂
    · exact cyclicNoInterleave_of_rotate_eq_append (V := U₁ ++ U₂) (W := U₃ ++ U₄)
        (hrot.trans (List.append_assoc (U₁ ++ U₂) U₃ U₄)) (all_append h₁ h₂) (all_append h₃ h₄)
    · exact cyclicNoInterleave_of_rotate_eq_append (V := U₁) (W := U₂ ++ U₃ ++ U₄)
        (hrot.trans (by simp only [List.append_assoc])) h₁ (all_append (all_append h₂ h₃) h₄)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.cyclicNoInterleave_of_four_blocks

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece
