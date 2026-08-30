import GroupApproximation.GGT.OsinGeodesicWord

/-!
# The unconditional part of Osin's §4–§5

`GGT/OsinTheorem54Lemma24.lean` leaves `OsinEnlargement.SepDataStatement` as the
single remaining leaf of Osin's Theorem 5.4: the separating-coset construction of
*Acylindrically hyperbolic groups* §4–§5, with `SepData` bundling one field per
cited lemma.  This module proves the part of that construction that needs no
geometry, so that a later module has to supply only the geometric fields.

## The relative metric is a metric

Osin uses `d̂_λ` as a left-invariant metric on `H_λ` throughout §4, and
`GGT/WPDHyperbolicallyEmbedded.lean` defines only its balls.  The three
properties every argument of §4 uses are proved here, at the level of the balls:

* `one_mem_relBall`, `relBall_mono_radius` — `d̂_λ(1,1) = 0`, and balls grow.
* `relBall_mul` — **subadditivity**, `d̂_λ(1, h₁h₂) ≤ d̂_λ(1,h₁) + d̂_λ(1,h₂)`.
  Concatenating two avoiding paths gives an avoiding path, because reading the
  second one from `h₁ ∈ H_λ` rather than from `1` changes no vertex's membership
  in `H_λ`.  That is `avoidsFrom_smul_left`, and it is the only place the
  subgroup property of `H_λ` is used.
* `mem_relBall_of_mem_base` — an element of `H_λ ∩ X` is at `d̂_λ`-distance at
  most one from `1`, because a single `X`-letter traverses no edge of `Γ_{H_λ}`,
  whatever its endpoints.

The path calculus underneath is `avoidsFrom_append` and `listVal_append`.

## Two fields of `SepData`, and half of Lemma 5.6

* `sepCard_self` — **`SepData.sep_self` discharged**.  A geodesic from `f` to `f`
  is the empty word, and the empty word has no components, so `S(f,f;D) = ∅`.
* `sepSet_eq_empty_of_mem_base` — **`X ⊆ Y`, the first half of Osin's Lemma 5.6**,
  where `Y = {y | S(1,y;D) = ∅}` is the relative generating set Theorem 5.4
  produces.  For `x ∈ X` every geodesic from `1` to `x` has length at most one,
  so a penetration of it is a single letter `comp λ x`; but then `x ∈ H_λ ∩ X`,
  and `mem_relBall_of_mem_base` puts `x` in the `d̂_λ`-ball of radius one, so the
  penetration is not essential.  The hypothesis is `1 ≤ Dc`, which Osin's
  `D ≥ 3C` with `C > 0` supplies.
* `sepCard_le_wordDist` — `|S(f,g;D)| ≤ d_{X⊔ℋ}(f,g)`, the quantitative form of
  `sepSet_finite'`: by Lemma 4.8 every separating coset is the coset of the
  initial vertex of a component of one fixed geodesic, and a geodesic of length
  `n` has `n` such indices.  This is *not* Lemma 5.10, whose bound is in the
  **enlarged** metric `d_{Y⊔ℋ}`, and enlarging the alphabet shortens distances;
  that is exactly why Lemma 5.10 is hard and this is not.

## What is still missing

The geometric fields of `SepData`: Lemma 4.9 (`sep_triangle`), Lemma 5.6's second
half and Lemma 5.8 (`emb`), Lemma 5.10 (`dist_le_sep`, `sep_le_dist`), and
Lemma 5.11 (`AcylindricalCore`); together with Lemma 4.8, which is
`OsinComponents.LemmaFourEight` and is carried as a hypothesis wherever it is
used here.  `sep_comm` is left too: reversing a path exchanges a letter for its
inverse, and `RelGenSet.base` is not required to be closed under inversion, so
an `X`-letter can only be reversed into an `H_λ`-letter — which creates a
component the original path did not have.  Whether `sep_comm` holds for the
repository's `sepSet` at a base that meets the family and is not symmetric is an
open question, and any construction of `SepData` has to settle it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Concatenating words and paths -/

/-- A concatenated word spells the product. -/
theorem listVal_append (w₁ w₂ : List (RelLetter G Λ)) :
    RelLetter.listVal (w₁ ++ w₂)
      = RelLetter.listVal w₁ * RelLetter.listVal w₂ := by
  show ((w₁ ++ w₂).map RelLetter.val).prod
    = (w₁.map RelLetter.val).prod * (w₂.map RelLetter.val).prod
  rw [List.map_append, List.prod_append]

/-- **Reading a concatenation avoids `Γ_{H lam}` exactly when both halves do**,
the second read from the vertex the first ends at. -/
theorem avoidsFrom_append (H : Λ → Subgroup G) (lam : Λ) :
    ∀ (w₁ w₂ : List (RelLetter G Λ)) (v : G),
      AvoidsFrom H lam (w₁ ++ w₂) v ↔
        AvoidsFrom H lam w₁ v ∧
          AvoidsFrom H lam w₂ (v * RelLetter.listVal w₁) := by
  intro w₁
  induction w₁ with
  | nil =>
      intro w₂ v
      constructor
      · intro h
        refine ⟨trivial, ?_⟩
        rw [RelLetter.listVal_nil, mul_one]
        exact h
      · rintro ⟨-, h2⟩
        rw [RelLetter.listVal_nil, mul_one] at h2
        exact h2
  | cons a t ih =>
      intro w₂ v
      constructor
      · rintro ⟨hhead, htail⟩
        obtain ⟨h1, h2⟩ := (ih w₂ (v * a.val)).mp htail
        refine ⟨⟨hhead, h1⟩, ?_⟩
        rw [listVal_cons, ← mul_assoc]
        exact h2
      · rintro ⟨⟨hhead, h1⟩, h2⟩
        refine ⟨hhead, (ih w₂ (v * a.val)).mpr ⟨h1, ?_⟩⟩
        rw [listVal_cons, ← mul_assoc] at h2
        exact h2

/-- **Avoiding `Γ_{H lam}` is invariant under left translation by `H lam`.**

A vertex `v` lies in `H lam` exactly when `c * v` does, for `c ∈ H lam`, and the
condition defining `AvoidsFrom` reads only that membership.  This is what makes
`d̂_lam` left-invariant on `H lam`, and it is the only use of the subgroup
property. -/
theorem avoidsFrom_smul_left {H : Λ → Subgroup G} {lam : Λ} {c : G}
    (hc : c ∈ H lam) :
    ∀ (w : List (RelLetter G Λ)) (v : G),
      AvoidsFrom H lam w (c * v) ↔ AvoidsFrom H lam w v := by
  intro w
  induction w with
  | nil => intro _; exact Iff.rfl
  | cons a t ih =>
      intro v
      have hmem : c * v ∈ H lam ↔ v ∈ H lam := by
        constructor
        · intro h
          have hstep := mul_mem (inv_mem hc) h
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at hstep
        · intro h
          exact mul_mem hc h
      constructor
      · rintro ⟨hhead, htail⟩
        refine ⟨fun hcon => hhead ⟨hcon.1, hmem.mpr hcon.2⟩, ?_⟩
        rw [← ih (v * a.val), ← mul_assoc]
        exact htail
      · rintro ⟨hhead, htail⟩
        refine ⟨fun hcon => hhead ⟨hcon.1, hmem.mp hcon.2⟩, ?_⟩
        rw [mul_assoc]
        exact (ih (v * a.val)).mpr htail

/-! ## `d̂_lam` is a left-invariant metric -/

/-- The identity lies in every relative ball. -/
theorem one_mem_relBall (D : RelGenSet G Λ) (lam : Λ) (n : ℕ) :
    (1 : G) ∈ D.relBall lam n :=
  ⟨one_mem _, [], by simp, RelLetter.listVal_nil, trivial, by simp⟩

/-- Relative balls grow with the radius. -/
theorem relBall_mono_radius (D : RelGenSet G Λ) (lam : Λ) {n m : ℕ}
    (hnm : n ≤ m) : D.relBall lam n ⊆ D.relBall lam m := by
  rintro h ⟨hh, wrd, hlet, hval, havoid, hlen⟩
  exact ⟨hh, wrd, hlet, hval, havoid, le_trans hlen hnm⟩

/-- **An element of `H lam` that is also a letter of `X` is `d̂_lam`-close to
`1`.**  The one-letter word `base h` spells `h` and traverses no edge of
`Γ_{H lam}`, an `X`-letter never doing so whatever its endpoints.

This is the fact behind `X ⊆ Y`: a coset penetrated by a one-letter geodesic is
never penetrated *essentially*. -/
theorem mem_relBall_of_mem_base (D : RelGenSet G Λ) (lam : Λ) {h : G}
    (hfam : h ∈ D.fam lam) (hbase : h ∈ D.base) : h ∈ D.relBall lam 1 := by
  refine ⟨hfam, [RelLetter.base h], ?_, ?_, ?_, ?_⟩
  · intro a ha
    have hae : a = RelLetter.base h := List.eq_of_mem_singleton ha
    rw [hae]
    exact hbase
  · simp [RelLetter.listVal, RelLetter.val]
  · refine ⟨?_, trivial⟩
    rintro ⟨hc, -⟩
    exact hc
  · simp

/-- **`d̂_lam` is subadditive**: concatenating an avoiding path to `h₁` with an
avoiding path to `h₂` gives an avoiding path to `h₁h₂`.

Reading the second path from `h₁` instead of from `1` is harmless by
`avoidsFrom_smul_left`, `h₁` lying in `H lam`. -/
theorem relBall_mul (D : RelGenSet G Λ) (lam : Λ) {n m : ℕ} {h₁ h₂ : G}
    (hb₁ : h₁ ∈ D.relBall lam n) (hb₂ : h₂ ∈ D.relBall lam m) :
    h₁ * h₂ ∈ D.relBall lam (n + m) := by
  obtain ⟨hf1, w₁, hlet1, hval1, hav1, hlen1⟩ := hb₁
  obtain ⟨hf2, w₂, hlet2, hval2, hav2, hlen2⟩ := hb₂
  refine ⟨mul_mem hf1 hf2, w₁ ++ w₂, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with hleft | hright
    · exact hlet1 a hleft
    · exact hlet2 a hright
  · rw [listVal_append, hval1, hval2]
  · refine (avoidsFrom_append D.fam lam w₁ w₂ 1).mpr ⟨hav1, ?_⟩
    rw [hval1, one_mul]
    have hkey := (avoidsFrom_smul_left hf1 w₂ 1).mpr hav2
    rwa [mul_one] at hkey
  · rw [List.length_append]
    omega

/-! ## `S(f,f;D)` is empty -/

/-- **`SepData.sep_self`, discharged.**  A geodesic word from `f` to `f` has
length `d(f,f) = 0`, so it is the empty word, and the empty word has no
components: `IsComp` asks for `i < k ≤ 0`. -/
theorem sepSet_self (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f : G) :
    sepSet D lam Dc f f = (∅ : Set (G ⧸ D.fam lam)) := by
  ext c
  constructor
  · rintro ⟨wrd, i, k, hgeo, hpen, -⟩
    exfalso
    obtain ⟨-, -, hlen⟩ := hgeo
    rw [wordDist_self] at hlen
    obtain ⟨hik, hkw, -, -, -⟩ := hpen.1
    omega
  · intro hc
    exact absurd hc (Set.notMem_empty c)

/-- The separating-coset count vanishes on the diagonal. -/
theorem sepCard_self (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f : G) :
    sepCard D lam Dc f f = 0 := by
  unfold sepCard
  rw [sepSet_self, Set.ncard_empty]

/-! ## `X ⊆ Y`: Osin's Lemma 5.6, first half -/

/-- **Osin, Lemma 5.6, first half**: `X ⊆ Y`, where `Y = {y | S(1,y;D) = ∅}`.

A geodesic from `1` to `x ∈ X` has length at most one, `x` being a letter.  A
penetration of it is therefore a single letter, and a *component* is a letter of
some `H_λ`, so the letter is `comp λ x` and `x ∈ H_λ`.  Then `x ∈ H_λ ∩ X`, so
`mem_relBall_of_mem_base` puts `x` in the `d̂_λ`-ball of radius one and, `Dc`
being at least one, in the ball of radius `Dc`: the penetration is not
essential.

The hypothesis `1 ≤ Dc` is Osin's `D ≥ 3C` with `C > 0` from his Lemma 4.2. -/
theorem sepSet_eq_empty_of_mem_base (D : RelGenSet G Λ) (lam : Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) {x : G} (hx : x ∈ D.base) :
    sepSet D lam Dc 1 x = (∅ : Set (G ⧸ D.fam lam)) := by
  ext c
  constructor
  · rintro ⟨wrd, i, k, hgeo, hpen, -⟩
    exfalso
    obtain ⟨hlet, hprod, hlen⟩ := hgeo
    obtain ⟨hcomp, hspan⟩ := hpen
    obtain ⟨hik, hkw, hrange, -, -⟩ := hcomp
    -- the geodesic has length at most one
    have hxA : x ∈ D.alphabet.carrier := Set.mem_union_left _ hx
    have hnorm : wordNorm D.alphabet.carrier x ≤ 1 := wordNorm_le_one_of_mem hxA
    have hlen1 : wrd.length ≤ 1 := by
      rw [hlen, wordDist_one_left]
      exact hnorm
    have hi0 : i = 0 := by omega
    have hk1 : k = 1 := by omega
    have hwlen : wrd.length = 1 := by omega
    subst hi0
    subst hk1
    -- so it is a single letter, and that letter is a component
    rcases wrd with _ | ⟨a, t⟩
    · simp at hwlen
    · have ht : t = [] := by
        refine List.length_eq_zero_iff.mp ?_
        have hcons := hwlen
        simp only [List.length_cons] at hcons
        omega
      subst ht
      have h0 : (a : RelLetter G Λ).IsCompOf lam := by
        have hget := hrange 0 (le_refl 0) (by omega) (by simp)
        simpa using hget
      cases a with
      | base y => exact h0.elim
      | comp mu y =>
          have hmu : mu = lam := h0
          have hyfam : y ∈ D.fam lam := by
            have hy : y ∈ D.fam mu :=
              hlet (RelLetter.comp mu y) (by simp)
            rwa [hmu] at hy
          have hlv : RelLetter.listVal [RelLetter.comp mu y] = y := by
            simp [RelLetter.listVal, RelLetter.val]
          rw [hlv, one_mul] at hprod
          -- the span of the component is `y`, and `y = x` lies in `X`
          refine hspan ?_
          have hv0 : vertex (1 : G) [RelLetter.comp mu y] 0 = 1 :=
            vertex_zero 1 _
          have hv1 : vertex (1 : G) [RelLetter.comp mu y] 1 = y := by
            show (1 : G) * y = y
            exact one_mul y
          rw [hv0, hv1, inv_one, one_mul]
          refine relBall_mono_radius D lam hDc ?_
          refine mem_relBall_of_mem_base D lam hyfam ?_
          rw [hprod]
          exact hx
  · intro hc
    exact absurd hc (Set.notMem_empty c)

/-! ## The counting bound one geodesic gives -/

/-- **`|S(f,g;D)| ≤ d_{X⊔ℋ}(f,g)`**, the quantitative form of
`sepSet_finite'`.  Lemma 4.8 makes every separating coset the coset of the
initial vertex of a component of one fixed geodesic, and a geodesic of length
`n` has `n` indices to offer.

This is **not** Osin's Lemma 5.10, whose bound `|S(f,g;D)| ≤ 3 d(f,g)` is in the
*enlarged* metric `d_{Y⊔ℋ}`; enlarging the alphabet shortens distances, so the
bound proved here does not imply it. -/
theorem sepCard_le_wordDist {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) (f g : G) :
    sepCard D lam Dc f g ≤ wordDist D.alphabet.carrier f g := by
  obtain ⟨wrd, hw⟩ := existsGeodesicWord D f g
  have hfin : ((↑(Finset.range wrd.length) : Set ℕ)).Finite :=
    (Finset.range wrd.length).finite_toSet
  have hsub : sepSet D lam Dc f g ⊆
      (fun i : ℕ => (QuotientGroup.mk (vertex f wrd i) : G ⧸ D.fam lam)) ''
        (↑(Finset.range wrd.length) : Set ℕ) := by
    intro c hc
    obtain ⟨i, k, hpen, hceq⟩ := h48.1 f g wrd hw c hc
    obtain ⟨hik, hkw, -, -, -⟩ := hpen
    exact ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), hceq.symm⟩
  unfold sepCard
  refine le_trans (Set.ncard_le_ncard hsub (hfin.image _)) ?_
  refine le_trans (Set.ncard_image_le hfin) ?_
  rw [Set.ncard_coe_finset, Finset.card_range]
  exact le_of_eq hw.2.2

end OsinComponents
end GGT
end GroupApproximation
