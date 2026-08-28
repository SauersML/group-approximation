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

/-- **A group acts non-elementarily as soon as one of its subgroups does.**  The
two independent loxodromics of the subgroup are two independent loxodromics of
the whole group. -/
theorem actsNonElementarily_top_of_subgroup {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {S : Subgroup G} {x : X}
    (h : ActsNonElementarily S x) : ActsNonElementarily (⊤ : Subgroup G) x := by
  obtain ⟨g, -, k, -, hg, hk, hind⟩ := h
  exact ⟨g, Subgroup.mem_top g, k, Subgroup.mem_top k, hg, hk, hind⟩

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

/-- **A subgroup of a free product containing both factors is everything.**
`Monoid.Coprod.lift` of the two corestrictions is a section of the inclusion of
the subgroup, and `Monoid.Coprod.hom_ext` identifies the composite with the
identity. -/
theorem eq_top_of_inl_inr_mem {K : Subgroup (Monoid.Coprod E H)}
    (hinl : ∀ a : E, (Monoid.Coprod.inl a : Monoid.Coprod E H) ∈ K)
    (hinr : ∀ b : H, (Monoid.Coprod.inr b : Monoid.Coprod E H) ∈ K) :
    K = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  have hid : K.subtype.comp (Monoid.Coprod.lift
        (MonoidHom.codRestrict Monoid.Coprod.inl K hinl)
        (MonoidHom.codRestrict Monoid.Coprod.inr K hinr))
      = MonoidHom.id (Monoid.Coprod E H) := by
    refine Monoid.Coprod.hom_ext ?_ ?_
    · refine MonoidHom.ext fun a => ?_
      show K.subtype (Monoid.Coprod.lift
          (MonoidHom.codRestrict Monoid.Coprod.inl K hinl)
          (MonoidHom.codRestrict Monoid.Coprod.inr K hinr)
          (Monoid.Coprod.inl a)) = Monoid.Coprod.inl a
      rw [Monoid.Coprod.lift_apply_inl]
      rfl
    · refine MonoidHom.ext fun b => ?_
      show K.subtype (Monoid.Coprod.lift
          (MonoidHom.codRestrict Monoid.Coprod.inl K hinl)
          (MonoidHom.codRestrict Monoid.Coprod.inr K hinr)
          (Monoid.Coprod.inr b)) = Monoid.Coprod.inr b
      rw [Monoid.Coprod.lift_apply_inr]
      rfl
  have hx : K.subtype (Monoid.Coprod.lift
      (MonoidHom.codRestrict Monoid.Coprod.inl K hinl)
      (MonoidHom.codRestrict Monoid.Coprod.inr K hinr) x) = x :=
    DFunLike.congr_fun hid x
  rw [← hx]
  exact (Monoid.Coprod.lift (MonoidHom.codRestrict Monoid.Coprod.inl K hinl)
    (MonoidHom.codRestrict Monoid.Coprod.inr K hinr) x).2

/-- Membership in the union alphabet, unfolded once so that the proofs below
never have to see through the definition. -/
theorem mem_unionCarrier {x : Monoid.Coprod E H} :
    x ∈ UnionCarrier A B ↔
      (∃ a ∈ A.carrier, (Monoid.Coprod.inl a : Monoid.Coprod E H) = x) ∨
        (∃ b ∈ B.carrier, (Monoid.Coprod.inr b : Monoid.Coprod E H) = x) :=
  Iff.rfl

/-- **The union alphabet generates the free product.**  Each factor alphabet
generates its factor, so the closure of the union contains both factors, and a
subgroup containing both factors is everything. -/
theorem closure_unionCarrier (A₀ : Alphabet E) (B₀ : Alphabet H) :
    Subgroup.closure (UnionCarrier A₀ B₀) = ⊤ := by
  refine eq_top_of_inl_inr_mem ?_ ?_
  · intro a
    have hle : (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range
        ≤ Subgroup.closure (UnionCarrier A₀ B₀) := by
      rw [MonoidHom.range_eq_map, ← A₀.symmetricGenerating.closure_eq,
        MonoidHom.map_closure]
      exact Subgroup.closure_mono Set.subset_union_left
    exact hle (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  · intro b
    have hle : (Monoid.Coprod.inr : H →* Monoid.Coprod E H).range
        ≤ Subgroup.closure (UnionCarrier A₀ B₀) := by
      rw [MonoidHom.range_eq_map, ← B₀.symmetricGenerating.closure_eq,
        MonoidHom.map_closure]
      exact Subgroup.closure_mono Set.subset_union_right
    exact hle (MonoidHom.mem_range.mpr ⟨b, rfl⟩)

/-- **The union alphabet**, as an alphabet of the free product: symmetric
because both factor alphabets are, and generating by `closure_unionCarrier`. -/
def unionAlphabet (A₀ : Alphabet E) (B₀ : Alphabet H) :
    Alphabet (Monoid.Coprod E H) where
  carrier := UnionCarrier A₀ B₀
  symmetricGenerating :=
    { inv_mem := by
        intro x hx
        rcases mem_unionCarrier.mp hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · refine mem_unionCarrier.mpr
            (Or.inl ⟨a⁻¹, A₀.symmetricGenerating.inv_mem a ha, ?_⟩)
          rw [map_inv]
        · refine mem_unionCarrier.mpr
            (Or.inr ⟨b⁻¹, B₀.symmetricGenerating.inv_mem b hb, ?_⟩)
          rw [map_inv]
      closure_eq := closure_unionCarrier A₀ B₀ }

@[simp] theorem unionAlphabet_carrier (A₀ : Alphabet E) (B₀ : Alphabet H) :
    (unionAlphabet A₀ B₀).carrier = UnionCarrier A₀ B₀ := rfl

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

/-! ## The four-point condition on a Cayley graph is a condition at the identity -/

/-- **The Gromov product at the basepoint of `Γ(G,A)`**, in word lengths. -/
theorem gromovProduct_base_eq {G : Type u} [Group G] (A : Alphabet G) (x y : G) :
    gromovProduct (Cayley.of A x) (Cayley.of A y) (Cayley.base A)
      = ((wordNorm A.carrier x : ℝ) + (wordNorm A.carrier y : ℝ)
          - (wordDist A.carrier x y : ℝ)) / 2 := by
  have hx : dist (Cayley.of A x) (Cayley.base A)
      = (wordNorm A.carrier x : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_base,
      wordDist_comm A.symmetricGenerating, wordDist_one_left]
  have hy : dist (Cayley.of A y) (Cayley.base A)
      = (wordNorm A.carrier y : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_base,
      wordDist_comm A.symmetricGenerating, wordDist_one_left]
  have hxy : dist (Cayley.of A x) (Cayley.of A y)
      = (wordDist A.carrier x y : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of]
  unfold gromovProduct
  rw [hx, hy, hxy]

/-- **The four-point condition on a Cayley graph is a condition at the
identity.**

The word metric is left invariant, so translating by `w⁻¹` carries an arbitrary
basepoint to the basepoint `1`; the Gromov products of the translated points are
the Gromov products of the original ones.  So hyperbolicity of `Γ(G,A)` has to be
checked only at the identity, which is where a normal form is available. -/
theorem isHyperbolicSpace_cayley_of_base {G : Type u} [Group G] (A : Alphabet G)
    {δ : ℝ}
    (h : ∀ x y z : G,
      min (gromovProduct (Cayley.of A x) (Cayley.of A y) (Cayley.base A))
          (gromovProduct (Cayley.of A y) (Cayley.of A z) (Cayley.base A)) - δ
        ≤ gromovProduct (Cayley.of A x) (Cayley.of A z) (Cayley.base A)) :
    IsHyperbolicSpace δ (Cayley A) := by
  intro w x y z
  have key : ∀ a b : Cayley A, dist a b
      = dist (Cayley.of A ((Cayley.val w)⁻¹ * Cayley.val a))
          (Cayley.of A ((Cayley.val w)⁻¹ * Cayley.val b)) := by
    intro a b
    rw [Cayley.dist_eq, Cayley.dist_eq, Cayley.val_of, Cayley.val_of]
    exact_mod_cast (wordDist_left_invariant A.carrier (Cayley.val w)⁻¹
      (Cayley.val a) (Cayley.val b)).symm
  have hw : Cayley.of A ((Cayley.val w)⁻¹ * Cayley.val w) = Cayley.base A := by
    rw [inv_mul_cancel]
    rfl
  have hgp : ∀ a b : Cayley A, gromovProduct a b w
      = gromovProduct (Cayley.of A ((Cayley.val w)⁻¹ * Cayley.val a))
          (Cayley.of A ((Cayley.val w)⁻¹ * Cayley.val b)) (Cayley.base A) := by
    intro a b
    unfold gromovProduct
    rw [key a w, key b w, key a b, hw]
  rw [hgp x y, hgp y z, hgp x z]
  exact h _ _ _

/-! ## The residue, with the alphabet constructed -/

/-- **Two geometric clauses, and nothing else.**

`FreeProductUnionAlphabetStatement` still asks for a `HullGeneratingSet` on the
free product, whose three fields are hyperbolicity, acylindricity and
non-elementarity, and whose alphabet has to be symmetric and generating.  Two of
those five are theorems: the union alphabet is symmetric and generating
(`unionAlphabet`), and `E ∗ H` acts non-elementarily on it because either factor
does (`actsNonElementarily_top_of_subgroup`).  What is left is the pair

* `Γ(E ∗ H, A ⊔ B)` is hyperbolic;
* the translation action on it is acylindrical.

Both are statements about the tree of spaces obtained by replacing each vertex
of the Bass-Serre tree by a copy of `Γ(E, A)` or `Γ(H, B)`.  This is the
smallest form the free product input takes: by
`hullCommonQuotient_of_oneStep_of_geometry` it is all that Hull's Corollary 7.4
needs beyond Hull's Theorem 7.1 for a single relator.

## The plan for the two clauses

Write `Γ = E ∗ H`, `A` for the union alphabet, `|·|` for its word length.

**(0) The syllable-sum formula.**  `|g| = Σᵢ |gᵢ|_{A_i}` over the syllables of
the normal form of `g` — Mathlib's `Monoid.CoprodI.Word.equiv`, after the binary
to indexed identification `Higman.toCoprodI`.  Both inequalities are elementary
and neither needs geometry: `≤` spells each syllable by a geodesic word of its
own factor and concatenates, `≥` is `WordMetric.wordNorm_le_length` against the
weight `Σᵢ |gᵢ|`, which is subadditive and at most one on letters — the argument
`OsinWeightedMetric.RelativeLength.len_prod_le` runs for the syllable count.
This is the only step that needs normal forms, and everything else is arithmetic
on top of it.

**(1) Reduce to the identity.**  `isHyperbolicSpace_cayley_of_base`, proved
above: the word metric is left invariant, so the four-point condition at an
arbitrary basepoint is the four-point condition at `1`, which is where the
normal form lives.

**(2) The Gromov product at `1`, in syllables.**  Let `x, y ∈ Γ` have normal
forms with maximal common syllable prefix `p`, and let `u, v` be the syllables
that follow.  By (0),

    (x|y)₁ = |p| + (u|v)₁^F   when `u` and `v` lie in the same factor `F`,
    (x|y)₁ = |p|              otherwise,

where the second term is the Gromov product of `Γ(F, A_F)`.  The computation is
`|x⁻¹y| = |x''| + |u⁻¹v| + |y''|` — no cancellation across the seams, because
the syllables on either side lie in the other factor — fed into
`gromovProduct_base_eq`.

**(3) Hyperbolicity at `δ = max δ_E δ_H`.**  Feed (2) into (1).  For `x, y, z`
the three common prefixes obey the tree ultrametric exactly; the only defect is
the case where two of the three pairs branch inside the *same* factor at the
*same* node, and there the defect is that factor's four-point defect.  So the
case split is on whether the three normal forms diverge at a common syllable.

**(4) Acylindricity.**  Given `ε`, let `R_E, N_E` and `R_H, N_H` be what the two
factors' acylindricity supplies at `ε`, and take `R = 2ε + R_E + R_H + 2` and
`N = max N_E N_H`.  If `d(x,y) ≥ R` then the geodesic from `x` to `y` crosses a
syllable boundary, and a `g` displacing both `x` and `y` by at most `ε` cannot
move that boundary: crossing it costs a whole syllable, and the syllables in
between are longer than `2ε`.  So `g` fixes the branch point, hence lies in a
single vertex group `w F w⁻¹`, and the count is that factor's count at `ε`.  The
step that makes this an equality rather than a bound is that the Bass-Serre tree
of a free product has trivial edge stabilisers, so nothing survives the crossing.

Step (4) is the one whose constants have to be checked against the definition
rather than read off; `HullGeometry.IsAcylindrical` quantifies `R` and `N` after
`ε`, which is the order this plan uses. -/
def FreeProductUnionGeometryStatement : Prop :=
  ∀ (E H : Type) [Group E] [Group H],
    Group.IsFinitelyPresented E → Group.IsFinitelyPresented H →
      IsPowerTorsionFree E → IsPowerTorsionFree H →
        IsAcylindricallyHyperbolic E → Infinite H →
          GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
            HasKazhdanPropertyT.{0, 0} H →
              ∃ (A : HullGeneratingSet E) (B : HullGeneratingSet H) (δ : ℝ),
                IsHyperbolicSpace δ
                    (Cayley (unionAlphabet A.alphabet B.alphabet)) ∧
                  IsAcylindrical (Monoid.Coprod E H)
                    (Cayley (unionAlphabet A.alphabet B.alphabet))

/-- **The union alphabet is a Hull generating set** once its Cayley graph is
hyperbolic and the action on it is acylindrical: the third field comes from the
left factor. -/
theorem freeProductUnionAlphabetStatement_of_geometry
    (h : FreeProductUnionGeometryStatement) :
    FreeProductUnionAlphabetStatement := by
  intro E H instE instH hEfp hHfp hEtf hHtf hEah hHinf hHhyp hHT
  letI := instE
  letI := instH
  obtain ⟨A, B, δ, hhyp, hacyl⟩ := h E H hEfp hHfp hEtf hHtf hEah hHinf hHhyp hHT
  have hcar : (unionAlphabet A.alphabet B.alphabet).carrier
      = UnionCarrier A.alphabet B.alphabet := rfl
  have hne : ActsNonElementarily
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range
      (Cayley.base (unionAlphabet A.alphabet B.alphabet)) :=
    actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H)
      (wordDist_inl_eq hcar) A.nonElementary
  exact ⟨A, B,
    ⟨unionAlphabet A.alphabet B.alphabet, δ, hhyp, hacyl,
      actsNonElementarily_top_of_subgroup hne⟩, hcar⟩

/-- **Hull's Corollary 7.4, from Hull's Theorem 7.1 for one relator and two
clauses about one Cayley graph.** -/
theorem hullCommonQuotient_of_oneStep_of_geometry (h : HullOneStepStatement.{0})
    (hgeom : FreeProductUnionGeometryStatement) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement :=
  hullCommonQuotient_of_oneStep_of_union h
    (freeProductUnionAlphabetStatement_of_geometry hgeom)

end HullSC
end GroupApproximation
