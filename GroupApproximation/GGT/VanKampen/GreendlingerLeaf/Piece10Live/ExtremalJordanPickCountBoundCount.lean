import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Vertices and faces of the walk map

Lane gl-p10-42 (the Bound half of `ExtremalJordanPickCountEulerStatement`).  For a dart list `c`
with walk map `P = walkMap M c`:

* `extremalJordanPickCountBound_vertexCount_le`.  If every dart of `c` starts where some dart of
  `c` ends, then `V_P ≤ #{vertexOf (α d) : d ∈ c}`.  Send a vertex of `P` to the ambient vertex of
  a representative.  This is injective, because `P` is a restriction (distinct `P`-vertices lie in
  distinct ambient vertices).  A retained dart is `d` or `α d` with `d ∈ c`, and both start at the
  end of a dart of `c`.
* `extremalJordanPickCountBound_faceCount_le`.  If `M` is planar, `P` is connected and `c` is the
  boundary of a face set `faces`, then `F_P ≤ #In + #Out`.  Here `In` is the set of face classes
  off `c` of the darts of `c`, and `Out` is the set of those of the darts outside `faces`.  Send a
  face of `P` to the face class of a representative.  This is injective, because face classes of
  a connected planar restriction do not join distinct faces
  (`CombMap.IsRestriction.faceOf_eq_of_faceClass`).  A retained dart based in `faces` is a dart of
  `c`, since the reverse of a dart of `c` is based outside `faces`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u

open SimpleClosedWalkSides
open scoped Classical

section BoundCount

variable (M : CombMap.{u}) (c : List M.Dart)

/-- **Vertices of the walk map** are at most the ends of the walk darts. -/
theorem extremalJordanPickCountBound_vertexCount_le [DecidableEq M.Vertex] (B : Finset M.Dart)
    (hB : ∀ d ∈ c, d ∈ B)
    (hv : ∀ d ∈ c, ∃ d' ∈ c, M.vertexOf d = M.vertexOf (M.alpha d')) :
    (walkMap M c).vertexCount ≤ (B.image fun d => M.vertexOf (M.alpha d)).card := by
  have hmaps : ∀ v : (walkMap M c).Vertex,
      M.vertexOf v.out.1 ∈ B.image fun d => M.vertexOf (M.alpha d) := by
    intro v
    rcases v.out.2 with h | h
    · obtain ⟨d', hd', hv'⟩ := hv _ h
      exact Finset.mem_image.mpr ⟨d', hB d' hd', hv'.symm⟩
    · exact Finset.mem_image.mpr
        ⟨_, hB _ h, congrArg M.vertexOf (M.alpha_involutive v.out.1)⟩
  let f : (walkMap M c).Vertex → (B.image fun d => M.vertexOf (M.alpha d) : Finset M.Vertex) :=
    fun v => ⟨M.vertexOf v.out.1, hmaps v⟩
  have hf : Function.Injective f := by
    intro v v' hvv
    have h1 : M.vertexOf v.out.1 = M.vertexOf v'.out.1 := congrArg Subtype.val hvv
    have h2 : (walkMap M c).vertexOf v.out = (walkMap M c).vertexOf v'.out :=
      ((walkMap_isRestriction M c).vertexOf_eq_iff _ _).mpr h1
    calc v = Quotient.mk'' v.out := (Quotient.out_eq' v).symm
      _ = Quotient.mk'' v'.out := h2
      _ = v' := Quotient.out_eq' v'
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at hle
  exact hle

/-- **Faces of the walk map** are at most the inside and outside face classes. -/
theorem extremalJordanPickCountBound_faceCount_le (hM : M.IsPlanar)
    (hconn : (walkMap M c).IsConnected) (faces : Finset M.Face)
    (hc : ∀ d, d ∈ c ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces)
    (B O : Finset M.Dart) (hB : ∀ d ∈ c, d ∈ B) (hO : ∀ r, M.faceOf r ∉ faces → r ∈ O) :
    (walkMap M c).faceCount ≤
      (B.image (Quot.mk (CombMap.FaceClassStep M (walkKeep M c)))).card +
        (O.image (Quot.mk (CombMap.FaceClassStep M (walkKeep M c)))).card := by
  have hmaps : ∀ F : (walkMap M c).Face,
      Quot.mk (CombMap.FaceClassStep M (walkKeep M c)) F.out.1 ∈
        B.image (Quot.mk (CombMap.FaceClassStep M (walkKeep M c))) ∪
          O.image (Quot.mk (CombMap.FaceClassStep M (walkKeep M c))) := by
    intro F
    by_cases hF : M.faceOf F.out.1 ∈ faces
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨F.out.1, hB _ ?_, rfl⟩)
      rcases F.out.2 with h | h
      · exact h
      · refine (((hc _).mp h).2 ?_).elim
        rw [M.alpha_involutive F.out.1]
        exact hF
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨F.out.1, hO _ hF, rfl⟩)
  let f : (walkMap M c).Face →
      (B.image (Quot.mk (CombMap.FaceClassStep M (walkKeep M c))) ∪
        O.image (Quot.mk (CombMap.FaceClassStep M (walkKeep M c))) :
          Finset (Quot (CombMap.FaceClassStep M (walkKeep M c)))) :=
    fun F => ⟨Quot.mk (CombMap.FaceClassStep M (walkKeep M c)) F.out.1, hmaps F⟩
  have hf : Function.Injective f := by
    intro F F' hFF
    have h1 : Quot.mk (CombMap.FaceClassStep M (walkKeep M c)) F.out.1 =
        Quot.mk (CombMap.FaceClassStep M (walkKeep M c)) F'.out.1 := congrArg Subtype.val hFF
    have h2 := faceClass_mono M (keep := walkKeep M c)
      (keep' := (· ∈ Set.range (Function.Embedding.subtype (walkKeep M c))))
      (fun x hx => by
        rintro ⟨z, rfl⟩
        exact hx z.2) (Quot.eqvGen_exact h1)
    have h3 : (walkMap M c).faceOf F.out = (walkMap M c).faceOf F'.out :=
      (walkMap_isRestriction M c).faceOf_eq_of_faceClass hM hconn h2
    calc F = Quotient.mk'' F.out := (Quotient.out_eq' F).symm
      _ = Quotient.mk'' F'.out := h3
      _ = F' := Quotient.out_eq' F'
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at hle
  exact hle.trans (Finset.card_union_le _ _)

end BoundCount

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_vertexCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_faceCount_le
