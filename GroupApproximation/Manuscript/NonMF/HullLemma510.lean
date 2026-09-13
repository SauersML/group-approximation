import GroupApproximation.Manuscript.NonMF.HullFiniteRadical
import GroupApproximation.Algebra.HyperbolicTransport
import GroupApproximation.GGT.HyperbolicAdditiveTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull, Lemma 5.10

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, arXiv:1308.4345, §5.
`non_mf_groups_exist.tex` cites Hull's Corollary 7.4 (tex line 1682), whose proof begins with
this lemma.

> **Lemma 5.10.** Let `G ∈ AH`. Then `G/K(G) ∈ AH₀`.

## The proof

This is Hull's proof, simplified in one place.  Let `q : G → Q` be onto with finite kernel, and let
`A₀ = q(A)` for Hull's alphabet `A` of `G`.  A shortest `A₀`-word for `q(g)` lifts letter by
letter to an `A`-word for `gk` with `k ∈ ker q`, so

`d_A(x, y) - M ≤ d_{A₀}(q x, q y) ≤ d_A(x, y)`,

where `M` bounds the `A`-length of the finitely many elements of `ker q`.  Hull first adjoins
`K(G)` to `A` (his Lemma 2.6) to get `M = 1`.  Any constant works, so that step is skipped here.
With this estimate:

* `Γ(Q, A₀)` is hyperbolic: a section of `q` changes distances by at most `M`, and
  hyperbolicity pulls back along such a map (`GGT.isHyperbolicSpace_of_additiveDistortion`);
* the action of `Q` is acylindrical: the `ε`-stabilizer of a pair in `Q` is the image of the
  `(ε + M)`-stabilizer of a pair of lifts in `G`;
* images of independent loxodromics are independent loxodromics.

Finally, the preimage of a finite normal subgroup of `G/K(G)` is a finite normal subgroup of
`G`.  It therefore lies in `K(G)`, so the subgroup is trivial.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullLemma510

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullFiniteRadical

universe u v

/-! ## The image alphabet and its word metric -/

section Image

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- **The alphabet `q(A)`**: the image of an alphabet under a surjective homomorphism. -/
def imageAlphabet (A : Alphabet G) (q : G →* Q) (hq : Function.Surjective q) : Alphabet Q :=
  ⟨q '' A.carrier, Hyperbolic.isSymmetricGeneratingSet_image q hq A.symmetricGenerating⟩

@[simp] theorem imageAlphabet_carrier (A : Alphabet G) (q : G →* Q)
    (hq : Function.Surjective q) : (imageAlphabet A q hq).carrier = q '' A.carrier :=
  rfl

/-- A word in `q(S)` lifts letter by letter to a word in `S`. -/
theorem exists_lift_list (S : Set G) (q : G →* Q) (l : List Q) (hl : ∀ y ∈ l, y ∈ q '' S) :
    ∃ s : List G, (∀ x ∈ s, x ∈ S) ∧ s.map q = l := by
  induction l with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons y tail ih =>
    obtain ⟨x, hx, hxy⟩ := hl y (by simp)
    obtain ⟨s, hs, hmap⟩ := ih fun z hz => hl z (by simp [hz])
    refine ⟨x :: s, fun z hz => ?_, by rw [List.map_cons, hxy, hmap]⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact hs z hz

/-- **`|g|_S ≤ |q g|_{q(S)} + M`**, where `M` bounds the `S`-length of `ker q`: lift a shortest
`q(S)`-word for `q g`, and correct the lift by an element of the kernel. -/
theorem wordNorm_le_image_add {S : Set G} (hS : IsSymmetricGeneratingSet S) {q : G →* Q}
    (hq : Function.Surjective q) {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm S k ≤ M) (g : G) :
    wordNorm S g ≤ wordNorm (q '' S) (q g) + M := by
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq (Hyperbolic.isSymmetricGeneratingSet_image q hq hS) (q g)
  obtain ⟨s, hs, hmap⟩ := exists_lift_list S q l hl.letters
  have hslen : s.length = l.length := by rw [← hmap, List.length_map]
  have hprod : q s.prod = q g := by rw [← hl.prod_eq, ← hmap, List.prod_hom]
  have hk : s.prod⁻¹ * g ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hprod, inv_mul_cancel]
  have h1 : wordNorm S s.prod ≤ s.length := wordNorm_le_length ⟨hs, rfl⟩
  have h2 := hM _ hk
  calc wordNorm S g = wordNorm S (s.prod * (s.prod⁻¹ * g)) := by rw [mul_inv_cancel_left]
    _ ≤ wordNorm S s.prod + wordNorm S (s.prod⁻¹ * g) := wordNorm_mul_le hS _ _
    _ ≤ wordNorm (q '' S) (q g) + M := by omega

/-- `d_{q(S)}(q x, q y) ≤ d_S(x, y)`. -/
theorem cast_wordDist_image_le {S : Set G} (hS : IsSymmetricGeneratingSet S) (q : G →* Q)
    (x y : G) : ((wordDist (q '' S) (q x) (q y) : ℕ) : ℝ) ≤ (wordDist S x y : ℕ) := by
  have h : wordNorm (q '' S) (q (x⁻¹ * y)) ≤ wordNorm S (x⁻¹ * y) :=
    Hyperbolic.wordNorm_map_le q hS _
  rw [map_mul, map_inv] at h
  show ((wordNorm (q '' S) ((q x)⁻¹ * q y) : ℕ) : ℝ) ≤ (wordNorm S (x⁻¹ * y) : ℕ)
  exact_mod_cast h

/-- `d_S(x, y) ≤ d_{q(S)}(q x, q y) + M`. -/
theorem cast_wordDist_le_image_add {S : Set G} (hS : IsSymmetricGeneratingSet S) {q : G →* Q}
    (hq : Function.Surjective q) {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm S k ≤ M) (x y : G) :
    ((wordDist S x y : ℕ) : ℝ) ≤ (wordDist (q '' S) (q x) (q y) : ℕ) + M := by
  have h := wordNorm_le_image_add hS hq hM (x⁻¹ * y)
  rw [map_mul, map_inv] at h
  show ((wordNorm S (x⁻¹ * y) : ℕ) : ℝ) ≤ (wordNorm (q '' S) ((q x)⁻¹ * q y) : ℕ) + M
  exact_mod_cast h

/-! ## The geometry of `Γ(Q, q(A))` -/

/-- **A section of `q` has additive distortion `M`.** -/
theorem hasAdditiveDistortion_section (A : Alphabet G) {q : G →* Q}
    (hq : Function.Surjective q) {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm A.carrier k ≤ M)
    {s : Q → G} (hs : ∀ c, q (s c) = c) :
    GGT.HasAdditiveDistortion (M : ℝ)
      (fun c : Cayley (imageAlphabet A q hq) => Cayley.of A (s (Cayley.val c))) := by
  intro a b
  have h1 := cast_wordDist_image_le A.symmetricGenerating q
    (s (Cayley.val a)) (s (Cayley.val b))
  have h2 := cast_wordDist_le_image_add A.symmetricGenerating hq hM
    (s (Cayley.val a)) (s (Cayley.val b))
  rw [hs, hs] at h1 h2
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  simp only [Cayley.dist_eq, Cayley.val_of, imageAlphabet_carrier]
  rw [abs_le]
  constructor <;> linarith

/-- **Loxodromics map to loxodromics**, at the same rate. -/
theorem isLoxodromic_image (A : Alphabet G) {q : G →* Q} (hq : Function.Surjective q)
    {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm A.carrier k ≤ M) {g : G}
    (hg : IsLoxodromic g (Cayley.base A)) :
    IsLoxodromic (q g) (Cayley.base (imageAlphabet A q hq)) := by
  obtain ⟨l, hl, B, hB, hlox⟩ := hg
  refine ⟨l, hl, B + M, add_nonneg hB (Nat.cast_nonneg M), fun n => ?_⟩
  have h1 := hlox n
  have h2 := cast_wordDist_le_image_add A.symmetricGenerating hq hM 1 (g ^ n)
  rw [map_one, map_pow] at h2
  simp only [Cayley.dist_eq, Cayley.val_smul, Cayley.val_base, imageAlphabet_carrier,
    mul_one] at h1 ⊢
  linarith

/-- **Independent elements map to independent elements.** -/
theorem independent_image (A : Alphabet G) {q : G →* Q} (hq : Function.Surjective q)
    {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm A.carrier k ≤ M) {g h : G}
    (hgh : HullGeometry.Independent g h (Cayley.base A)) :
    HullGeometry.Independent (q g) (q h) (Cayley.base (imageAlphabet A q hq)) := by
  obtain ⟨C, hC⟩ := hgh
  refine ⟨C + M, fun n m => ?_⟩
  have h0 := hC n m
  have h1 := cast_wordDist_image_le A.symmetricGenerating q (g ^ n) 1
  have h2 := cast_wordDist_image_le A.symmetricGenerating q (h ^ m) 1
  have h3 := cast_wordDist_le_image_add A.symmetricGenerating hq hM (g ^ n) (h ^ m)
  rw [map_zpow, map_one] at h1 h2
  rw [map_zpow, map_zpow] at h3
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  simp only [gromovProduct, Cayley.dist_eq, Cayley.val_smul, Cayley.val_base,
    imageAlphabet_carrier, mul_one] at h0 ⊢
  linarith

/-- **The action of `Q` on `Γ(Q, q(A))` is acylindrical.**  The `ε`-stabilizer of a pair of
points is the image of the `(ε + M)`-stabilizer of a pair of lifts. -/
theorem isAcylindrical_image (A : Alphabet G) {q : G →* Q} (hq : Function.Surjective q)
    {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm A.carrier k ≤ M)
    (hA : IsAcylindrical G (Cayley A)) : IsAcylindrical Q (Cayley (imageAlphabet A q hq)) := by
  obtain ⟨s, hs⟩ : ∃ s : Q → G, ∀ c, q (s c) = c :=
    ⟨Function.surjInv hq, Function.surjInv_eq hq⟩
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hA (ε + M) (add_pos_of_pos_of_nonneg hε hM0)
  refine ⟨R, N, fun x₀ y₀ hxy => ?_⟩
  have hdist : R ≤ dist (Cayley.of A (s (Cayley.val x₀))) (Cayley.of A (s (Cayley.val y₀))) := by
    have h := cast_wordDist_image_le A.symmetricGenerating q
      (s (Cayley.val x₀)) (s (Cayley.val y₀))
    rw [hs, hs] at h
    simp only [Cayley.dist_eq, Cayley.val_of, imageAlphabet_carrier] at hxy ⊢
    linarith
  obtain ⟨hfin, hcard⟩ := hRN _ _ hdist
  have hsub : {c : Q | dist x₀ (c • x₀) ≤ ε ∧ dist y₀ (c • y₀) ≤ ε} ⊆
      q '' {g : G |
        dist (Cayley.of A (s (Cayley.val x₀))) (g • Cayley.of A (s (Cayley.val x₀))) ≤ ε + M ∧
        dist (Cayley.of A (s (Cayley.val y₀))) (g • Cayley.of A (s (Cayley.val y₀))) ≤ ε + M} := by
    rintro c ⟨hcx, hcy⟩
    refine ⟨s c, ⟨?_, ?_⟩, hs c⟩
    · have h := cast_wordDist_le_image_add A.symmetricGenerating hq hM
        (s (Cayley.val x₀)) (s c * s (Cayley.val x₀))
      rw [map_mul, hs, hs] at h
      simp only [Cayley.dist_eq, Cayley.val_smul, Cayley.val_of, imageAlphabet_carrier] at hcx ⊢
      linarith
    · have h := cast_wordDist_le_image_add A.symmetricGenerating hq hM
        (s (Cayley.val y₀)) (s c * s (Cayley.val y₀))
      rw [map_mul, hs, hs] at h
      simp only [Cayley.dist_eq, Cayley.val_smul, Cayley.val_of, imageAlphabet_carrier] at hcy ⊢
      linarith
  exact ⟨(hfin.image q).subset hsub,
    (Set.ncard_le_ncard hsub (hfin.image q)).trans ((Set.ncard_image_le hfin).trans hcard)⟩

/-- **`Q` acts non-elementarily on `Γ(Q, q(A))`.** -/
theorem actsNonElementarily_image (A : Alphabet G) {q : G →* Q} (hq : Function.Surjective q)
    {M : ℕ} (hM : ∀ k ∈ q.ker, wordNorm A.carrier k ≤ M)
    (hne : ActsNonElementarily (⊤ : Subgroup G) (Cayley.base A)) :
    ActsNonElementarily (⊤ : Subgroup Q) (Cayley.base (imageAlphabet A q hq)) := by
  obtain ⟨g, -, h, -, hg, hh, hgh⟩ := hne
  exact ⟨q g, Subgroup.mem_top _, q h, Subgroup.mem_top _, isLoxodromic_image A hq hM hg,
    isLoxodromic_image A hq hM hh, independent_image A hq hM hgh⟩

end Image

/-! ## Quotients by finite normal subgroups -/

/-- **A quotient of an `AH` group with finite kernel is `AH`**, with the image of Hull's
alphabet. -/
theorem isAcylindricallyHyperbolic_of_finite_ker {G : Type u} {Q : Type v} [Group G] [Group Q]
    [IsAcylindricallyHyperbolic G] {q : G →* Q} (hq : Function.Surjective q)
    (hker : Finite q.ker) : IsAcylindricallyHyperbolic Q := by
  obtain ⟨A⟩ := exists_hullGeneratingSet G
  have hkfin : (q.ker : Set G).Finite := Set.finite_coe_iff.mp hker
  obtain ⟨M, hM⟩ := (hkfin.image fun k : G => wordNorm A.alphabet.carrier k).bddAbove
  have hM' : ∀ k ∈ q.ker, wordNorm A.alphabet.carrier k ≤ M := fun k hk => hM ⟨k, hk, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Q → G, ∀ c, q (s c) = c :=
    ⟨Function.surjInv hq, Function.surjInv_eq hq⟩
  exact ⟨⟨imageAlphabet A.alphabet q hq, A.delta + 3 * M,
    GGT.isHyperbolicSpace_of_additiveDistortion
      (hasAdditiveDistortion_section A.alphabet hq hM' hs) A.hyperbolic,
    isAcylindrical_image A.alphabet hq hM' A.acylindrical,
    actsNonElementarily_image A.alphabet hq hM' A.nonElementary⟩⟩

#audit_axioms isAcylindricallyHyperbolic_of_finite_ker

/-- **`G/K(G)` has no nontrivial finite normal subgroup.**  The preimage of one is a finite
normal subgroup of `G`, so it lies in `K(G)`, and its image is trivial. -/
theorem hasTrivialFiniteRadical_quotient (G : Type u) [Group G]
    [IsAcylindricallyHyperbolic G] : HasTrivialFiniteRadical (G ⧸ finiteRadical G) := by
  intro F hFn hF
  have hK : (finiteRadical G : Set G).Finite := Set.finite_coe_iff.mp (finite_finiteRadical G)
  have hFset : (F : Set (G ⧸ finiteRadical G)).Finite := Set.finite_coe_iff.mp hF
  have hcomap :
      ((F.comap (QuotientGroup.mk' (finiteRadical G)) : Subgroup G) : Set G).Finite := by
    rw [Subgroup.coe_comap]
    refine hFset.preimage' fun b _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (finiteRadical G) b
    refine (hK.image fun k => g * k).subset fun x hx => ⟨g⁻¹ * x, ?_, mul_inv_cancel_left g x⟩
    have hx' : QuotientGroup.mk' (finiteRadical G) x = QuotientGroup.mk' (finiteRadical G) g :=
      hx
    have hmem : g⁻¹ * x ∈ (QuotientGroup.mk' (finiteRadical G)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx', inv_mul_cancel]
    rw [QuotientGroup.ker_mk'] at hmem
    exact hmem
  have hle : F.comap (QuotientGroup.mk' (finiteRadical G)) ≤ finiteRadical G :=
    le_finiteRadical (hFn.comap _) hcomap.to_subtype
  rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (finiteRadical G)) F]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hle)

#audit_axioms hasTrivialFiniteRadical_quotient

/-! ## The printed lemma -/

/-- **Hull, Lemma 5.10.**  *"Let `G ∈ AH`. Then `G/K(G) ∈ AH₀`."* -/
def PrintedHullLemma510 : Prop :=
  ∀ {G : Type u} [Group G], IsAcylindricallyHyperbolic G → IsAH0 (G ⧸ finiteRadical G)

theorem printedHullLemma510 : PrintedHullLemma510.{u} := by
  intro G _ _
  refine ⟨isAcylindricallyHyperbolic_of_finite_ker (QuotientGroup.mk'_surjective _) ?_,
    hasTrivialFiniteRadical_quotient G⟩
  rw [QuotientGroup.ker_mk']
  exact finite_finiteRadical G

#audit_closed_axioms printedHullLemma510

end HullLemma510
end NonMF
end Manuscript
end GroupApproximation
