import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: list-level facts

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-55.

List-level facts for the winding choice of `F'` (`Piece10Live/GFaceWind`).

* `gfaceWind_lind_split`: the dart indicator of a disjoint union.
* `gfaceWind_bd_iff`: for a `0/1`-valued face function cobounded by `c` (and `c` using no edge in
  both directions), `d` is a boundary dart of its support exactly when `d ∈ c`.
* `gfaceWind_filter_sub`: filtering a walk `C` by a sub-list of `c = C.filter (· ∈ c)`.

## Truth check

List-level identities; the Python check concerns the assembled construction, see
`Piece10Live/GFaceWind`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

open scoped Classical

/-- **The dart indicator of a disjoint union.** -/
theorem gfaceWind_lind_split {α : Type*} {c A B : List α} (h : ∀ x, x ∈ c ↔ x ∈ A ∨ x ∈ B)
    (hd : ∀ x ∈ A, x ∉ B) (x : α) :
    gfaceWind_lind c x = gfaceWind_lind A x + gfaceWind_lind B x := by
  by_cases hA : x ∈ A
  · linarith [gfaceWind_lind_pos ((h x).mpr (Or.inl hA)), gfaceWind_lind_pos hA,
      gfaceWind_lind_neg (hd x hA)]
  · by_cases hB : x ∈ B
    · linarith [gfaceWind_lind_pos ((h x).mpr (Or.inr hB)), gfaceWind_lind_neg hA,
        gfaceWind_lind_pos hB]
    · linarith [gfaceWind_lind_neg (show x ∉ c from fun hc => ((h x).mp hc).elim hA hB),
        gfaceWind_lind_neg hA, gfaceWind_lind_neg hB]

/-- **Boundary darts of a `0/1` support**: if `a - b = [d ∈ c] - [e ∈ c]` with `a, b ∈ {0, 1}`
and not both `d, e ∈ c`, then `a = 1 ∧ b ≠ 1` exactly when `d ∈ c`. -/
theorem gfaceWind_bd_iff {α : Type*} {c : List α} {d e : α} {a b : ℤ}
    (hcob : a - b = gfaceWind_lind c d - gfaceWind_lind c e) (ha : a = 0 ∨ a = 1)
    (hb : b = 0 ∨ b = 1) (hne : d ∈ c → e ∉ c) : (a = 1 ∧ ¬ b = 1) ↔ d ∈ c := by
  by_cases hd : d ∈ c
  · have hab : a - b = 1 := by
      linarith [gfaceWind_lind_pos hd, gfaceWind_lind_neg (hne hd)]
    refine ⟨fun _ => hd, fun _ => ⟨?_, ?_⟩⟩
    · rcases ha with ha | ha
      · rcases hb with hb | hb
        · exfalso
          linarith
        · exfalso
          linarith
      · exact ha
    · intro hb1
      rcases ha with ha | ha
      · linarith
      · linarith
  · constructor
    · rintro ⟨h1, h2⟩
      exfalso
      have hb0 : b = 0 := hb.resolve_right h2
      by_cases he : e ∈ c
      · linarith [gfaceWind_lind_neg hd, gfaceWind_lind_pos he]
      · linarith [gfaceWind_lind_neg hd, gfaceWind_lind_neg he]
    · intro h
      exact absurd h hd

/-- **Filtering by a sub-list**: if `C.filter (· ∈ c) = c` and `c'` lies on `c`, then filtering
`C` by `c'` is filtering `c` by `c'`. -/
theorem gfaceWind_filter_sub {α : Type*} {C c c' : List α}
    (hfil : C.filter (gfaceWind_mem c) = c) (hsub : ∀ x ∈ c', x ∈ c) :
    C.filter (gfaceWind_mem c') = c.filter (gfaceWind_mem c') := by
  have key : C.filter (gfaceWind_mem c') =
      (C.filter (gfaceWind_mem c)).filter (gfaceWind_mem c') := by
    rw [List.filter_filter]
    refine List.filter_congr fun x _ => ?_
    show gfaceWind_mem c' x = (gfaceWind_mem c' x && gfaceWind_mem c x)
    cases h : gfaceWind_mem c' x
    · rw [Bool.false_and]
    · have h2 : gfaceWind_mem c x = true :=
        gfaceWind_mem_eq_true_iff.mpr (hsub x (gfaceWind_mem_eq_true_iff.mp h))
      rw [Bool.true_and]
      exact h2.symm
  rw [key, hfil]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_lind_split
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_bd_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_filter_sub
