import GroupApproximation.GGT.HullSCCommonQuotientCorrected

/-!
# The free factors are non-elementary on the union alphabet

`HullSC.FreeProductAlphabetStatement` is what Hull's Corollary 7.4 is still
owed: a Hull alphabet on `E ∗ H` in which both free factors act
non-elementarily.  `HullSC.not_freeProductStatement`'s companion observation is
that no *tree-shaped* alphabet can supply it --- the factors fix a vertex of the
Bass-Serre tree, and have syllable length one in the Cayley graph of the union
alphabet read as a tree.  This module proves that the union alphabet does supply
it, once the two clauses that are genuinely geometric are granted.

Write `A` for Hull's alphabet on `E`, `B` for Hull's alphabet on `H`, and take
the alphabet on `E ∗ H` whose letters are the letters of `A` in the left factor
and the letters of `B` in the right one.  Then

> a free factor is **isometrically embedded**: `|ι w|_C = |w|_A`.

`≤` is the trivial half --- an `A`-word for `w` is a `C`-word for `ι w`.  The
other half is the retraction `ρ : E ∗ H → E` that kills `H`: it carries a letter
of `C` either to a letter of `A` or to the identity, so it does not increase
word length (`wordNorm_map_le_length`), and `ρ ∘ ι = id`.  That is
`wordNorm_of_retraction`, stated for an arbitrary retracted subgroup rather than
for the free product, so that the left and the right factor are one theorem and
not two.

Loxodromy and independence are then inherited verbatim, because every distance
that enters them is a distance between two points of the factor's orbit of the
basepoint: `isLoxodromic_of_wordDist_eq`, `independent_of_wordDist_eq`,
`actsNonElementarily_range_of_wordDist_eq`.  So the whole of
`FreeProductAlphabetStatement` follows from `FreeProductUnionAlphabetStatement`
--- Hull's alphabet on the free product can be taken to be the union of Hull's
alphabets on the factors --- in which the only content left is that the Cayley
graph of that union is hyperbolic and that the translation action on it is
acylindrical.  Those are the two clauses of the tree of spaces, and they are
what the lane still owes.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Word length under a homomorphism -/

/-- **A homomorphism carrying every letter to a letter or to the identity does
not increase word length.**  Induction on the word: a letter that dies costs
nothing, and a letter that survives costs at most one. -/
theorem wordNorm_map_le_length {G : Type u} {E : Type v} [Group G] [Group E]
    {S : Set G} {T : Set E} (hT : IsSymmetricGeneratingSet T) (φ : G →* E)
    (hφ : ∀ x ∈ S, φ x ∈ T ∨ φ x = 1) :
    ∀ (l : List G) (g : G), IsWord S l g → wordNorm T (φ g) ≤ l.length := by
  intro l
  induction l with
  | nil =>
      intro g hg
      have hg1 : g = 1 := hg.prod_eq.symm.trans List.prod_nil
      rw [hg1, map_one, wordNorm_one]
      exact Nat.zero_le _
  | cons a l ih =>
      intro g hg
      have ha : a ∈ S := hg.letters a (by simp)
      have hl : IsWord S l l.prod :=
        ⟨fun x hx => hg.letters x (by simp [hx]), rfl⟩
      have hprod : g = a * l.prod := hg.prod_eq.symm.trans List.prod_cons
      have hih : wordNorm T (φ l.prod) ≤ l.length := ih l.prod hl
      rw [hprod, map_mul, List.length_cons]
      rcases hφ a ha with hmem | h1
      · have hle : wordNorm T (φ a * φ l.prod)
            ≤ wordNorm T (φ a) + wordNorm T (φ l.prod) :=
          wordNorm_mul_le hT _ _
        have hone : wordNorm T (φ a) ≤ 1 := wordNorm_le_one_of_mem hmem
        omega
      · rw [h1, one_mul]
        omega

/-- **A retracted subgroup is isometrically embedded.**

`ι` carries the letters of `A` to letters of `C`, so `|ι w|_C ≤ |w|_A`; the
retraction `ρ` carries the letters of `C` to letters of `A` or to the identity,
so `|w|_A = |ρ (ι w)|_A ≤ |ι w|_C`.  Both halves are
`wordNorm_map_le_length`. -/
theorem wordNorm_of_retraction {E : Type u} {Gam : Type u} [Group E] [Group Gam]
    {A : Set E} {C : Set Gam} (hA : IsSymmetricGeneratingSet A)
    (hC : IsSymmetricGeneratingSet C) (ι : E →* Gam) (ρ : Gam →* E)
    (hρι : ∀ w : E, ρ (ι w) = w) (hιA : ∀ a ∈ A, ι a ∈ C)
    (hρC : ∀ x ∈ C, ρ x ∈ A ∨ ρ x = 1) (w : E) :
    wordNorm C (ι w) = wordNorm A w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hA w
    have h := wordNorm_map_le_length hC ι (fun x hx => Or.inl (hιA x hx)) l w hl
    rw [hlen] at h
    exact h
  · obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hC (ι w)
    have h := wordNorm_map_le_length hA ρ hρC l (ι w) hl
    rw [hρι, hlen] at h
    exact h

/-! ## Distances in the Cayley graph, from the basepoint -/

/-- `d(1, u·1) = |u|`. -/
theorem cayleyDist_base_smul {G : Type u} [Group G] (A : Alphabet G) (u : G) :
    dist (Cayley.base A) (u • Cayley.base A) = (wordDist A.carrier 1 u : ℝ) := by
  rw [Cayley.dist_eq, Cayley.val_smul, Cayley.val_base, mul_one]

/-- `d(u·1, 1) = |u⁻¹|`. -/
theorem cayleyDist_smul_base {G : Type u} [Group G] (A : Alphabet G) (u : G) :
    dist (u • Cayley.base A) (Cayley.base A) = (wordDist A.carrier u 1 : ℝ) := by
  rw [Cayley.dist_eq, Cayley.val_smul, Cayley.val_base, mul_one]

/-- `d(u·1, v·1) = |u⁻¹v|`. -/
theorem cayleyDist_smul_smul {G : Type u} [Group G] (A : Alphabet G) (u v : G) :
    dist (u • Cayley.base A) (v • Cayley.base A)
      = (wordDist A.carrier u v : ℝ) := by
  rw [Cayley.dist_eq, Cayley.val_smul, Cayley.val_smul, Cayley.val_base,
    mul_one, mul_one]

/-! ## Transport along an isometrically embedded subgroup -/

section Map

variable {E : Type u} {Gam : Type u} [Group E] [Group Gam] {A : Alphabet E}
  {C : Alphabet Gam}

/-- The orbit of the basepoint under the subgroup is isometric to the orbit in
the subgroup's own Cayley graph, at the basepoint on the left. -/
theorem cayleyDist_base_smul_map (ι : E →* Gam)
    (hdist : ∀ u v : E, wordDist C.carrier (ι u) (ι v) = wordDist A.carrier u v)
    (u : E) :
    dist (Cayley.base C) ((ι u) • Cayley.base C)
      = dist (Cayley.base A) (u • Cayley.base A) := by
  have h := hdist 1 u
  rw [map_one] at h
  rw [cayleyDist_base_smul, cayleyDist_base_smul, h]

/-- The same with the basepoint on the right. -/
theorem cayleyDist_smul_base_map (ι : E →* Gam)
    (hdist : ∀ u v : E, wordDist C.carrier (ι u) (ι v) = wordDist A.carrier u v)
    (u : E) :
    dist ((ι u) • Cayley.base C) (Cayley.base C)
      = dist (u • Cayley.base A) (Cayley.base A) := by
  have h := hdist u 1
  rw [map_one] at h
  rw [cayleyDist_smul_base, cayleyDist_smul_base, h]

/-- The same between two orbit points. -/
theorem cayleyDist_smul_smul_map (ι : E →* Gam)
    (hdist : ∀ u v : E, wordDist C.carrier (ι u) (ι v) = wordDist A.carrier u v)
    (u v : E) :
    dist ((ι u) • Cayley.base C) ((ι v) • Cayley.base C)
      = dist (u • Cayley.base A) (v • Cayley.base A) := by
  rw [cayleyDist_smul_smul, cayleyDist_smul_smul, hdist]

/-- **Loxodromy is inherited.**  Every distance in the definition is a distance
between two points of the orbit of the basepoint. -/
theorem isLoxodromic_of_wordDist_eq (ι : E →* Gam)
    (hdist : ∀ u v : E, wordDist C.carrier (ι u) (ι v) = wordDist A.carrier u v)
    {g : E} (hg : IsLoxodromic g (Cayley.base A)) :
    IsLoxodromic (ι g) (Cayley.base C) := by
  obtain ⟨l, hl, D, hD, hle⟩ := hg
  refine ⟨l, hl, D, hD, fun n => ?_⟩
  rw [← map_pow, cayleyDist_base_smul_map ι hdist]
  exact hle n

/-- **Independence is inherited**, for the same reason: the three points whose
Gromov product is bounded all lie in the orbit of the basepoint. -/
theorem independent_of_wordDist_eq (ι : E →* Gam)
    (hdist : ∀ u v : E, wordDist C.carrier (ι u) (ι v) = wordDist A.carrier u v)
    {g h : E} (hind : Independent g h (Cayley.base A)) :
    Independent (ι g) (ι h) (Cayley.base C) := by
  obtain ⟨D, hD⟩ := hind
  refine ⟨D, fun n m => ?_⟩
  have key : gromovProduct ((ι (g ^ n)) • Cayley.base C)
        ((ι (h ^ m)) • Cayley.base C) (Cayley.base C)
      = gromovProduct ((g ^ n) • Cayley.base A) ((h ^ m) • Cayley.base A)
        (Cayley.base A) := by
    unfold gromovProduct
    rw [cayleyDist_smul_base_map ι hdist, cayleyDist_smul_base_map ι hdist,
      cayleyDist_smul_smul_map ι hdist]
  rw [← map_zpow, ← map_zpow, key]
  exact hD n m

/-- **Non-elementarity is inherited by the image.**  If the subgroup acts
non-elementarily on its own Cayley graph and is isometrically embedded, its
image acts non-elementarily on the ambient one. -/
theorem actsNonElementarily_range_of_wordDist_eq (ι : E →* Gam)
    (hdist : ∀ u v : E, wordDist C.carrier (ι u) (ι v) = wordDist A.carrier u v)
    (hne : ActsNonElementarily (⊤ : Subgroup E) (Cayley.base A)) :
    ActsNonElementarily ι.range (Cayley.base C) := by
  obtain ⟨g, -, h, -, hg, hh, hind⟩ := hne
  exact ⟨ι g, MonoidHom.mem_range.mpr ⟨g, rfl⟩, ι h,
    MonoidHom.mem_range.mpr ⟨h, rfl⟩, isLoxodromic_of_wordDist_eq ι hdist hg,
    isLoxodromic_of_wordDist_eq ι hdist hh, independent_of_wordDist_eq ι hdist hind⟩

end Map

/-! ## The two factors of a free product -/

section Coprod

variable {E H : Type} [Group E] [Group H] {A : Alphabet E} {B : Alphabet H}
  {C : Alphabet (Monoid.Coprod E H)}

/-- The union alphabet: the letters of `A` in the left factor and the letters
of `B` in the right one. -/
def UnionCarrier (A₀ : Alphabet E) (B₀ : Alphabet H) : Set (Monoid.Coprod E H) :=
  ((Monoid.Coprod.inl : E →* Monoid.Coprod E H) : E → Monoid.Coprod E H)
      '' A₀.carrier ∪
    ((Monoid.Coprod.inr : H →* Monoid.Coprod E H) : H → Monoid.Coprod E H)
      '' B₀.carrier

/-- Membership in the union alphabet, unfolded once so that the proofs below
never have to see through the definition. -/
theorem mem_unionCarrier {x : Monoid.Coprod E H} :
    x ∈ UnionCarrier A B ↔
      (∃ a ∈ A.carrier, (Monoid.Coprod.inl a : Monoid.Coprod E H) = x) ∨
        (∃ b ∈ B.carrier, (Monoid.Coprod.inr b : Monoid.Coprod E H) = x) :=
  Iff.rfl

/-- **The left factor is isometrically embedded in the union alphabet.**  The
retraction is `Monoid.Coprod.lift (id) 1`, which kills the letters of the right
factor and fixes those of the left. -/
theorem wordNorm_inl_eq (hcar : C.carrier = UnionCarrier A B) (w : E) :
    wordNorm C.carrier (Monoid.Coprod.inl w) = wordNorm A.carrier w := by
  refine wordNorm_of_retraction A.symmetricGenerating C.symmetricGenerating
    Monoid.Coprod.inl (Monoid.Coprod.lift (MonoidHom.id E) (1 : H →* E))
    ?_ ?_ ?_ w
  · intro x
    show (Monoid.Coprod.lift (MonoidHom.id E) (1 : H →* E))
      (Monoid.Coprod.inl x) = (MonoidHom.id E) x
    rw [Monoid.Coprod.lift_apply_inl]
  · intro a ha
    rw [hcar]
    exact mem_unionCarrier.mpr (Or.inl ⟨a, ha, rfl⟩)
  · intro x hx
    rw [hcar] at hx
    rcases mem_unionCarrier.mp hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · left
      rw [Monoid.Coprod.lift_apply_inl, MonoidHom.id_apply]
      exact ha
    · right
      show (Monoid.Coprod.lift (MonoidHom.id E) (1 : H →* E))
        (Monoid.Coprod.inr b) = (1 : H →* E) b
      rw [Monoid.Coprod.lift_apply_inr]

/-- **The right factor is isometrically embedded in the union alphabet.** -/
theorem wordNorm_inr_eq (hcar : C.carrier = UnionCarrier A B) (w : H) :
    wordNorm C.carrier (Monoid.Coprod.inr w) = wordNorm B.carrier w := by
  refine wordNorm_of_retraction B.symmetricGenerating C.symmetricGenerating
    Monoid.Coprod.inr (Monoid.Coprod.lift (1 : E →* H) (MonoidHom.id H))
    ?_ ?_ ?_ w
  · intro x
    show (Monoid.Coprod.lift (1 : E →* H) (MonoidHom.id H))
      (Monoid.Coprod.inr x) = (MonoidHom.id H) x
    rw [Monoid.Coprod.lift_apply_inr]
  · intro b hb
    rw [hcar]
    exact mem_unionCarrier.mpr (Or.inr ⟨b, hb, rfl⟩)
  · intro x hx
    rw [hcar] at hx
    rcases mem_unionCarrier.mp hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · right
      show (Monoid.Coprod.lift (1 : E →* H) (MonoidHom.id H))
        (Monoid.Coprod.inl a) = (1 : E →* H) a
      rw [Monoid.Coprod.lift_apply_inl]
    · left
      rw [Monoid.Coprod.lift_apply_inr, MonoidHom.id_apply]
      exact hb

/-- The word metric of the union alphabet, restricted to the left factor, is
the word metric of `A`. -/
theorem wordDist_inl_eq (hcar : C.carrier = UnionCarrier A B) (u v : E) :
    wordDist C.carrier (Monoid.Coprod.inl u) (Monoid.Coprod.inl v)
      = wordDist A.carrier u v := by
  have hmul : (Monoid.Coprod.inl u : Monoid.Coprod E H)⁻¹ * Monoid.Coprod.inl v
      = Monoid.Coprod.inl (u⁻¹ * v) := by
    rw [map_mul, map_inv]
  unfold wordDist
  rw [hmul, wordNorm_inl_eq hcar]

/-- The word metric of the union alphabet, restricted to the right factor, is
the word metric of `B`. -/
theorem wordDist_inr_eq (hcar : C.carrier = UnionCarrier A B) (u v : H) :
    wordDist C.carrier (Monoid.Coprod.inr u) (Monoid.Coprod.inr v)
      = wordDist B.carrier u v := by
  have hmul : (Monoid.Coprod.inr u : Monoid.Coprod E H)⁻¹ * Monoid.Coprod.inr v
      = Monoid.Coprod.inr (u⁻¹ * v) := by
    rw [map_mul, map_inv]
  unfold wordDist
  rw [hmul, wordNorm_inr_eq hcar]

end Coprod

/-! ## What is left of the free product input -/

/-- **The geometry of the union alphabet, and nothing else.**

Hull's alphabet on `E ∗ H` can be taken to be the union of Hull's alphabets on
the two factors.  Unfolded, the three clauses of `HullGeneratingSet` say that
the Cayley graph of that union is hyperbolic, that the translation action on it
is acylindrical, and that `E ∗ H` acts non-elementarily; the first two are the
tree of spaces, and the third follows from either factor.

This is the whole of what `FreeProductAlphabetStatement` --- and so, by
`hullCommonQuotient_of_oneStep_of_alphabet`, the whole of what Hull's Corollary
7.4 --- still needs beyond Hull's Theorem 7.1. -/
def FreeProductUnionAlphabetStatement : Prop :=
  ∀ (E H : Type) [Group E] [Group H],
    Group.IsFinitelyPresented E → Group.IsFinitelyPresented H →
      IsPowerTorsionFree E → IsPowerTorsionFree H →
        IsAcylindricallyHyperbolic E → Infinite H →
          GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
            HasKazhdanPropertyT.{0, 0} H →
              ∃ (A : HullGeneratingSet E) (B : HullGeneratingSet H)
                (C : HullGeneratingSet (Monoid.Coprod E H)),
                C.alphabet.carrier = UnionCarrier A.alphabet B.alphabet

/-- **Both free factors are suitable on the union alphabet.**  Each of them acts
non-elementarily on its own Cayley graph --- that is the third field of its Hull
generating set --- and is isometrically embedded in the union, so its image
inherits two independent loxodromics. -/
theorem freeProductAlphabetStatement_of_union
    (h : FreeProductUnionAlphabetStatement) : FreeProductAlphabetStatement := by
  intro E H instE instH hEfp hHfp hEtf hHtf hEah hHinf hHhyp hHT
  letI := instE
  letI := instH
  obtain ⟨A, B, C, hcar⟩ := h E H hEfp hHfp hEtf hHtf hEah hHinf hHhyp hHT
  refine ⟨C, ?_, ?_⟩
  · exact actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H)
      (wordDist_inl_eq hcar) A.nonElementary
  · exact actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inr : H →* Monoid.Coprod E H)
      (wordDist_inr_eq hcar) B.nonElementary

/-- **Hull's Corollary 7.4 from Hull's Theorem 7.1 for one relator and the
geometry of one Cayley graph.** -/
theorem hullCommonQuotient_of_oneStep_of_union (h : HullOneStepStatement.{0})
    (hunion : FreeProductUnionAlphabetStatement) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement :=
  hullCommonQuotient_of_oneStep_of_alphabet h
    (freeProductAlphabetStatement_of_union hunion)

end HullSC
end GroupApproximation
