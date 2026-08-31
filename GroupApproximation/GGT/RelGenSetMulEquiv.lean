import GroupApproximation.Algebra.HyperbolicTransport
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# Transporting relative generating sets across group isomorphisms

The natural quotient in Hull's Lemma 4.4 is unique only up to group
isomorphism.  This file proves that the repository's concrete
`RelGenSet.IsHyperbolicallyEmbedded` structure transports across such an
isomorphism, including its relative balls.  The result is exact: word lengths
and relative-ball radii are unchanged.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace RelLetter

/-- Push a relative letter forward along a homomorphism. -/
def mapHom {G : Type u} {Q : Type v} [Group G] [Group Q] {Λ : Type w}
    (f : G →* Q) : RelLetter G Λ → RelLetter Q Λ
  | base g => base (f g)
  | comp lam h => comp lam (f h)

@[simp] theorem val_mapHom {G : Type u} {Q : Type v} [Group G] [Group Q]
    {Λ : Type w} (f : G →* Q) (a : RelLetter G Λ) :
    (mapHom f a).val = f a.val := by
  cases a <;> rfl

@[simp] theorem isCompOf_mapHom {G : Type u} {Q : Type v} [Group G] [Group Q]
    {Λ : Type w} (f : G →* Q) (lam : Λ) (a : RelLetter G Λ) :
    IsCompOf lam (mapHom f a) ↔ IsCompOf lam a := by
  cases a <;> rfl

@[simp] theorem listVal_map_mapHom {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (f : G →* Q)
    (word : List (RelLetter G Λ)) :
    listVal (word.map (mapHom f)) = f (listVal word) := by
  induction word with
  | nil => simp [listVal]
  | cons a word ih =>
      change (mapHom f a).val * listVal (word.map (mapHom f)) =
        f (a.val * listVal word)
      rw [val_mapHom, ih, map_mul]

end RelLetter

namespace RelGenSet

/-- Transport a relative generating set across a group isomorphism. -/
noncomputable def mapMulEquiv {G : Type u} {Q : Type v} [Group G] [Group Q]
    {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q) : RelGenSet Q Λ where
  base := (e : G →* Q) '' D.base
  fam := fun lam => (D.fam lam).map (e : G →* Q)
  symmetricGenerating := by
    have hcarrier :
        (e : G →* Q) '' (D.base ∪ ⋃ lam : Λ, (D.fam lam : Set G)) =
          ((e : G →* Q) '' D.base) ∪
            ⋃ lam : Λ, (((D.fam lam).map (e : G →* Q) : Subgroup Q) : Set Q) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with hx | hx
        · exact Set.mem_union_left _ ⟨x, hx, rfl⟩
        · rcases Set.mem_iUnion.mp hx with ⟨lam, hx⟩
          exact Set.mem_union_right _ (Set.mem_iUnion.mpr
            ⟨lam, ⟨x, hx, rfl⟩⟩)
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩ | hy
        · exact ⟨x, Set.mem_union_left _ hx, rfl⟩
        · rcases Set.mem_iUnion.mp hy with ⟨lam, hy⟩
          change ∃ z, z ∈ D.fam lam ∧ e z = y at hy
          rcases hy with ⟨z, hz, hzy⟩
          exact ⟨z, Set.mem_union_right _
            (Set.mem_iUnion.mpr ⟨lam, hz⟩), hzy⟩
    rw [← hcarrier]
    exact Hyperbolic.isSymmetricGeneratingSet_image (e : G →* Q)
      (Hyperbolic.surjective_mulEquiv_toMonoidHom e) D.symmetricGenerating

@[simp] theorem base_mapMulEquiv {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q) :
    (D.mapMulEquiv e).base = (e : G →* Q) '' D.base := rfl

@[simp] theorem fam_mapMulEquiv {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q)
    (lam : Λ) :
    (D.mapMulEquiv e).fam lam = (D.fam lam).map (e : G →* Q) := rfl

theorem alphabet_carrier_mapMulEquiv {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q) :
    (D.mapMulEquiv e).alphabet.carrier =
      (e : G →* Q) '' D.alphabet.carrier := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, Set.mem_union_left _ hx, rfl⟩
    · rcases Set.mem_iUnion.mp hy with ⟨lam, x, hx, rfl⟩
      exact ⟨x, Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨lam, hx⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · exact Set.mem_union_left _ ⟨x, hx, rfl⟩
    · rcases Set.mem_iUnion.mp hx with ⟨lam, hx⟩
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr
        ⟨lam, ⟨x, hx, rfl⟩⟩)

@[simp] theorem isLetter_mapHom_iff {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q)
    (a : RelLetter G Λ) :
    (D.mapMulEquiv e).IsLetter (RelLetter.mapHom (e : G →* Q) a) ↔
      D.IsLetter a := by
  cases a with
  | base g =>
      simp only [IsLetter, RelLetter.mapHom, base_mapMulEquiv, Set.mem_image]
      constructor
      · rintro ⟨x, hx, hxe⟩
        exact (e.injective hxe).symm ▸ hx
      · intro hg
        exact ⟨g, hg, rfl⟩
  | comp lam h =>
      simp only [IsLetter, RelLetter.mapHom, fam_mapMulEquiv]
      constructor
      · rintro ⟨x, hx, hxe⟩
        exact (e.injective hxe).symm ▸ hx
      · intro hh
        exact ⟨h, hh, rfl⟩

theorem avoidsFrom_mapHom_iff {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q)
    (lam : Λ) (word : List (RelLetter G Λ)) (g : G) :
    AvoidsFrom (D.mapMulEquiv e).fam lam
        (word.map (RelLetter.mapHom (e : G →* Q))) (e g) ↔
      AvoidsFrom D.fam lam word g := by
  induction word generalizing g with
  | nil => rfl
  | cons a word ih =>
      simp only [List.map_cons, AvoidsFrom, RelLetter.isCompOf_mapHom,
        RelLetter.val_mapHom]
      have hmem : e g ∈ (D.fam lam).map (e : G →* Q) ↔ g ∈ D.fam lam := by
        constructor
        · rintro ⟨x, hx, hxe⟩
          exact (e.injective hxe).symm ▸ hx
        · intro hg
          exact ⟨g, hg, rfl⟩
      rw [fam_mapMulEquiv, hmem]
      exact and_congr Iff.rfl (by simpa using ih (g * a.val))

theorem mem_relBall_mapMulEquiv_iff {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} (D : RelGenSet G Λ) (e : G ≃* Q)
    (lam : Λ) (n : ℕ) (g : G) :
    e g ∈ (D.mapMulEquiv e).relBall lam n ↔ g ∈ D.relBall lam n := by
  constructor
  · rintro ⟨hg, word, hword, hval, havoid, hlen⟩
    have hg' : g ∈ D.fam lam := by
      rcases hg with ⟨x, hx, hxe⟩
      exact (e.injective hxe).symm ▸ hx
    let source : List (RelLetter G Λ) :=
      word.map (RelLetter.mapHom (e.symm : Q →* G))
    refine ⟨hg', source, ?_, ?_, ?_, ?_⟩
    · intro a ha
      simp only [source, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have hb' := hword b hb
      cases b with
      | base y =>
          change e.symm y ∈ D.base
          change y ∈ (e : G →* Q) '' D.base at hb'
          rcases hb' with ⟨x, hx, rfl⟩
          simpa using hx
      | comp mu y =>
          change e.symm y ∈ D.fam mu
          change y ∈ (D.fam mu).map (e : G →* Q) at hb'
          rcases hb' with ⟨x, hx, rfl⟩
          simpa using hx
    · have h := congrArg e.symm hval
      simpa [source] using h
    · have hround :
          source.map (RelLetter.mapHom (e : G →* Q)) = word := by
        clear hword hval havoid hlen
        simp only [source, List.map_map]
        induction word with
        | nil => rfl
        | cons b word ih =>
            dsimp at ih
            rw [List.map_cons, ih]
            congr 1
            cases b <;> simp [RelLetter.mapHom]
      have havoid' : AvoidsFrom (D.mapMulEquiv e).fam lam
          (source.map (RelLetter.mapHom (e : G →* Q))) (e 1) := by
        simpa [hround] using havoid
      exact (avoidsFrom_mapHom_iff D e lam source 1).mp havoid'
    · simpa [source] using hlen
  · rintro ⟨hg, word, hword, hval, havoid, hlen⟩
    refine ⟨⟨g, hg, rfl⟩,
      word.map (RelLetter.mapHom (e : G →* Q)), ?_, ?_, ?_, ?_⟩
    · intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      exact (isLetter_mapHom_iff D e b).mpr (hword b hb)
    · simp [hval]
    · simpa using (avoidsFrom_mapHom_iff D e lam word 1).mpr havoid
    · simpa using hlen

/-- Hyperbolic embeddedness is invariant under group isomorphism, with every
relative-ball radius preserved exactly. -/
theorem IsHyperbolicallyEmbedded.mapMulEquiv {G : Type u} {Q : Type v}
    [Group G] [Group Q] {Λ : Type w} {D : RelGenSet G Λ}
    (hD : D.IsHyperbolicallyEmbedded) (e : G ≃* Q) :
    (D.mapMulEquiv e).IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · obtain ⟨delta, hdelta⟩ := hD.hyperbolic
    refine ⟨delta, ?_⟩
    intro a b c d
    obtain ⟨a', rfl⟩ := Hyperbolic.surjective_mulEquiv_toMonoidHom e a
    obtain ⟨b', rfl⟩ := Hyperbolic.surjective_mulEquiv_toMonoidHom e b
    obtain ⟨c', rfl⟩ := Hyperbolic.surjective_mulEquiv_toMonoidHom e c
    obtain ⟨d', rfl⟩ := Hyperbolic.surjective_mulEquiv_toMonoidHom e d
    have hdist (x y : G) :
        dist (Cayley.of (D.mapMulEquiv e).alphabet (e x))
            (Cayley.of (D.mapMulEquiv e).alphabet (e y)) =
          dist (Cayley.of D.alphabet x) (Cayley.of D.alphabet y) := by
      simp only [Cayley.dist_eq, Cayley.val_of,
        alphabet_carrier_mapMulEquiv]
      exact_mod_cast
        Hyperbolic.wordDist_image_mulEquiv e D.symmetricGenerating x y
    have hgp (x y z : G) :
        gromovProduct
            (Cayley.of (D.mapMulEquiv e).alphabet (e x))
            (Cayley.of (D.mapMulEquiv e).alphabet (e y))
            (Cayley.of (D.mapMulEquiv e).alphabet (e z)) =
          gromovProduct (Cayley.of D.alphabet x) (Cayley.of D.alphabet y)
            (Cayley.of D.alphabet z) := by
      unfold gromovProduct
      rw [hdist, hdist, hdist]
    change min
        (gromovProduct
          (Cayley.of (D.mapMulEquiv e).alphabet (e b'))
          (Cayley.of (D.mapMulEquiv e).alphabet (e c'))
          (Cayley.of (D.mapMulEquiv e).alphabet (e a')))
        (gromovProduct
          (Cayley.of (D.mapMulEquiv e).alphabet (e c'))
          (Cayley.of (D.mapMulEquiv e).alphabet (e d'))
          (Cayley.of (D.mapMulEquiv e).alphabet (e a'))) - delta ≤
      gromovProduct
        (Cayley.of (D.mapMulEquiv e).alphabet (e b'))
        (Cayley.of (D.mapMulEquiv e).alphabet (e d'))
        (Cayley.of (D.mapMulEquiv e).alphabet (e a'))
    rw [hgp, hgp, hgp]
    exact hdelta a' b' c' d'
  · intro lam n
    have heq : (D.mapMulEquiv e).relBall lam n =
        (e : G →* Q) '' D.relBall lam n := by
      ext y
      obtain ⟨g, rfl⟩ := Hyperbolic.surjective_mulEquiv_toMonoidHom e y
      constructor
      · intro h
        exact ⟨g, (mem_relBall_mapMulEquiv_iff D e lam n g).mp h, rfl⟩
      · rintro ⟨x, hx, hxe⟩
        apply (mem_relBall_mapMulEquiv_iff D e lam n g).mpr
        exact (e.injective hxe).symm ▸ hx
    rw [heq]
    exact (hD.locallyFinite lam n).image e

end RelGenSet
end GGT
end GroupApproximation
