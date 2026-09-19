import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Computability.CodedMicrostate
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Computability.MFRecognitionPi02

/-!
# Locality and finite certificates: the printed section `sec:local`

This module carries, one Lean declaration per printed sentence, the opening of
Section `sec:local` of `mf_recognition_complexity.tex`:

* the two readings of the MF property that the section contrasts
  (`sequential_models_iff_finite_data`);
* Korchagin's fixed-separation reformulation
  (`korchagin_fixed_separation_reformulation`);
* the printed **Lemma `lem:local-models`** in its normalised finite-domain
  form, `LocalModel` / `IsLocallyModelled`, together with its three printed
  proof sentences;
* the Kleene--Mostowski vocabulary the section fixes (`PrintedSigma01`,
  `PrintedPi01`, `PrintedSigma02`, `PrintedPi02` and their transfers into the
  repository's `ArithmeticalHierarchy`);
* the effective coding of finite presentations, the two sets
  `MFfp` and `NONMFfp`, and Korchagin's Proposition 8.

The certificate calculus used by Proposition `prop:mf-upper-bound` is the
executable challenge/answer checker in `Computability.MFRecognitionPi02`.

## Relation to the existing repository route

`Computability.MFRecognitionPi02` proves the `Π⁰₂` upper bound through an
executable rational-witness checker.  The manuscript now uses that same route:
a finite challenge receives either a word-problem witness or a rational unitary
microstate with decidable upper- and lower-norm certificates.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Certificates

open Matrix PresentationCodes ArithmeticalHierarchy

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

/-! ## The two readings of the MF property (`sec:local`, opening) -/

/-- `sec:local`, sentence `c097041316ba`: "The MF property is defined through
sequences of models on all of `G`, but it is determined by finite data with a
fixed separation constant."

The left-hand side is the definition of `IsOperatorMF` written out --- a
sequence of finite models on all of `G`, and an injective homomorphism into
their norm corona.  The right-hand side is the finite-data condition, with the
separation constant pinned at `1`. -/
theorem sequential_models_iff_finite_data [Countable G] :
    (∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
        ∃ rho : G →* NormMatrixCoronaUnitary X, Function.Injective rho) ↔
      IsNormApproximable G 1 :=
  OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one

/-- `sec:local`, sentence `ad41737d6b2a`: "The reformulation is due to
Korchagin~\cite{Korchagin}."

The content of the reformulation is that the separation constant of a
weak-MF system carries no information: an arbitrary positive separation can be
normalised to exactly `1`.  Korchagin's amplification
(`amplification_raises_separation`) is what does this; the repository proves it
at the level of a single pair, and `OperatorMFLocalNormalization` assembles the
pairs. -/
theorem korchagin_fixed_separation_reformulation [Countable G] :
    IsWeakMF G ↔ IsNormApproximable G 1 := by
  constructor
  · intro h
    exact OperatorMFLocalNormalization.isNormApproximable_one h.isOperatorMF
  · intro h
    exact ⟨1, zero_lt_one, h⟩

/-! ## The printed Lemma `lem:local-models` -/

/-- The finite-domain data of the printed Lemma `lem:local-models`: a dimension
`d ≥ 1` and a map `V` into `U(d)` with `V 1 = 1`, multiplicative to within `ε`
on the part of `F` where the product stays inside `F`, and separating every
nonidentity element of `F` from `1` by at least `1`.

As in the repository's `NormModel`, the map is carried as a matrix-valued
function together with its unitarity; the printed conditions are imposed only
on `F`, which is what "a map `V : F → U(d)`" means. -/
structure LocalModel (G : Type u) [Group G] (F : Finset G) (ε : ℝ) where
  /-- the finite model of dimension `d`. -/
  carrier : FiniteModel
  /-- `d ≥ 1`. -/
  nonempty : 0 < Fintype.card carrier
  /-- the map `V`. -/
  V : G → Matrix carrier carrier ℂ
  /-- `V` takes unitary values. -/
  isUnitary : ∀ g, V g ∈ Matrix.unitaryGroup carrier ℂ
  /-- `V 1 = 1`. -/
  V_one : V 1 = 1
  /-- `‖V (g * h) - V g * V h‖ ≤ ε` whenever `g`, `h` and `g * h` lie in `F`. -/
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → ‖V (g * h) - V g * V h‖ ≤ ε
  /-- `‖V g - 1‖ ≥ 1` for `g ∈ F \ {1}`. -/
  separated : ∀ g ∈ F, g ≠ 1 → 1 ≤ ‖V g - 1‖

/-- The right-hand side of the printed Lemma `lem:local-models`: for every
finite `F ∋ 1` and every `ε > 0` there is a local model. -/
def IsLocallyModelled (G : Type u) [Group G] : Prop :=
  ∀ F : Finset G, (1 : G) ∈ F → ∀ ε : ℝ, 0 < ε → Nonempty (LocalModel G F ε)

/-- `lem:local-models`, proof sentence `5b820d443dbd`: "Korchagin's
amplification --- replacing `V_n(g)` by a direct sum of its tensor powers ---
raises the separation of finitely many nonidentity elements above `1` while
multiplying the defects by a constant~\cite[Proposition~7]{Korchagin}."

Both halves at once, for one pair: a bounded tensor exponent `p ≤ N` that
raises the separation of the designated pair above `1`, and the constant `p` by
which every defect is multiplied. -/
theorem amplification_raises_separation {Y : Type} [Fintype Y] [DecidableEq Y]
    (hY : Nonempty Y) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : δ ≤ ‖A - B‖)
    (N : ℕ) (hN : 8 < (N : ℝ) * δ ^ 2) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ N ∧
      1 < ‖opTensorPow A p - opTensorPow B p‖ ∧
      ∀ X Z : Matrix Y Y ℂ, X ∈ Matrix.unitaryGroup Y ℂ →
        Z ∈ Matrix.unitaryGroup Y ℂ →
          ‖opTensorPow X p - opTensorPow Z p‖ ≤ (p : ℝ) * ‖X - Z‖ := by
  obtain ⟨p, hp1, hpN, hpsep⟩ :=
    OperatorNormAmplification.exists_tensorPower_pair_far hY hA hB hδ hsep N hN
  exact ⟨p, hp1, hpN, hpsep, fun X Z hX hZ =>
    l2_opNorm_opTensorPow_sub_le hY hX hZ p⟩

/-- `lem:local-models`, proof sentence `2ac1d99eb82f`: "A block direct sum of
late amplified models, one summand for each `g ∈ F \ {1}`, gives the stated
map."

The block sum is `OperatorMFLocalNormalization.isNormApproximable_one`; what
remains here is the normalisation `V 1 = 1`, obtained by translating the whole
model by `V(1)^*` and halving the tolerance. -/
theorem exists_localModel_of_isOperatorMF [Countable G] (hMF : IsOperatorMF G)
    (F : Finset G) (hF : (1 : G) ∈ F) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (LocalModel G F ε) := by
  classical
  obtain ⟨N⟩ :=
    OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.1 hMF
      F (ε / 2) (by linarith)
  have hstar : (N.map 1)ᴴ * N.map 1 = 1 := by
    have h := N.isUnitary 1
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hstarmem : (N.map 1)ᴴ ∈ Matrix.unitaryGroup N.carrier ℂ :=
    conjTranspose_mem_unitaryGroup (N.isUnitary 1)
  have hone : ‖(1 : Matrix N.carrier N.carrier ℂ) - N.map 1‖ ≤ ε / 2 := by
    have h := N.multiplicative 1 hF 1 hF
    rw [one_mul,
      show N.map 1 - N.map 1 * N.map 1
          = N.map 1 * ((1 : Matrix N.carrier N.carrier ℂ) - N.map 1) by
        rw [mul_sub, mul_one],
      CStarRing.norm_mem_unitary_mul _ (N.isUnitary 1)] at h
    exact h
  have hunit1 : ‖(1 : Matrix N.carrier N.carrier ℂ) - (N.map 1)ᴴ‖ ≤ ε / 2 := by
    rw [show (1 : Matrix N.carrier N.carrier ℂ) - (N.map 1)ᴴ
        = ((1 : Matrix N.carrier N.carrier ℂ) - N.map 1)ᴴ by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one],
      Matrix.l2_opNorm_conjTranspose]
    exact hone
  refine ⟨{
    carrier := N.carrier
    nonempty := N.nonempty
    V := fun g => (N.map 1)ᴴ * N.map g
    isUnitary := fun g => mul_mem hstarmem (N.isUnitary g)
    V_one := hstar
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh _
    have hsplit :
        (N.map 1)ᴴ * N.map (g * h) -
            ((N.map 1)ᴴ * N.map g) * ((N.map 1)ᴴ * N.map h)
          = (N.map 1)ᴴ *
              (N.map (g * h) - N.map g * ((N.map 1)ᴴ * N.map h)) := by
      rw [mul_sub]
      simp only [mul_assoc]
    have hmid : ‖N.map g * N.map h -
        N.map g * ((N.map 1)ᴴ * N.map h)‖ ≤ ε / 2 := by
      rw [show N.map g * N.map h - N.map g * ((N.map 1)ᴴ * N.map h)
          = N.map g *
              (((1 : Matrix N.carrier N.carrier ℂ) - (N.map 1)ᴴ) * N.map h) by
        rw [sub_mul, one_mul, mul_sub],
        CStarRing.norm_mem_unitary_mul _ (N.isUnitary g),
        CStarRing.norm_mul_mem_unitary _ (N.isUnitary h)]
      exact hunit1
    calc ‖(N.map 1)ᴴ * N.map (g * h) -
            ((N.map 1)ᴴ * N.map g) * ((N.map 1)ᴴ * N.map h)‖
        = ‖N.map (g * h) - N.map g * ((N.map 1)ᴴ * N.map h)‖ := by
          rw [hsplit, CStarRing.norm_mem_unitary_mul _ hstarmem]
      _ ≤ ‖N.map (g * h) - N.map g * N.map h‖ +
            ‖N.map g * N.map h - N.map g * ((N.map 1)ᴴ * N.map h)‖ := by
          rw [← sub_add_sub_cancel (N.map (g * h)) (N.map g * N.map h)
            (N.map g * ((N.map 1)ᴴ * N.map h))]
          exact norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 :=
          add_le_add (N.multiplicative g hg h hh) hmid
      _ = ε := by ring
  · intro g hg hgne
    rw [show (N.map 1)ᴴ * N.map g - 1
        = (N.map 1)ᴴ * (N.map g - N.map 1) by rw [mul_sub, hstar],
      CStarRing.norm_mem_unitary_mul _ hstarmem]
    exact N.separated g hg 1 hF hgne

/-- `lem:local-models`, proof sentence `4784ac860360`: "Maps for an exhaustion
`(F_n, 1/n)` of `G`, extended by `1` outside `F_n`, form an MF model."

The converse direction of the lemma.  A local model on the enlargement of `F`
by all products `gh` and all quotients `g⁻¹h` is already an operator-norm model
on `F` with separation `1/2`, and any positive separation constant is enough
for weak MF, hence for MF. -/
theorem isOperatorMF_of_isLocallyModelled [Countable G]
    (h : IsLocallyModelled G) : IsOperatorMF G := by
  classical
  refine (show IsWeakMF G from ⟨1 / 2, by norm_num, ?_⟩).isOperatorMF
  intro F ε hε
  set F' : Finset G :=
    insert 1 (F ∪ (F ×ˢ F).image (fun q => q.1 * q.2) ∪
      (F ×ˢ F).image (fun q => q.1⁻¹ * q.2)) with hF'def
  have h1 : (1 : G) ∈ F' := Finset.mem_insert_self _ _
  have hFsub : ∀ g ∈ F, g ∈ F' := by
    intro g hg
    rw [hF'def]
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
  have hprod : ∀ g ∈ F, ∀ k ∈ F, g * k ∈ F' := by
    intro g hg k hk
    rw [hF'def]
    refine Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    exact Finset.mem_image.2 ⟨(g, k), Finset.mem_product.2 ⟨hg, hk⟩, rfl⟩
  have hquot : ∀ g ∈ F, ∀ k ∈ F, g⁻¹ * k ∈ F' := by
    intro g hg k hk
    rw [hF'def]
    refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
    exact Finset.mem_image.2 ⟨(g, k), Finset.mem_product.2 ⟨hg, hk⟩, rfl⟩
  obtain ⟨L⟩ := h F' h1 (min ε (1 / 2)) (lt_min hε (by norm_num))
  refine ⟨{
    carrier := L.carrier
    nonempty := L.nonempty
    map := L.V
    isUnitary := L.isUnitary
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg k hk
    exact (L.multiplicative g (hFsub g hg) k (hFsub k hk)
      (hprod g hg k hk)).trans (min_le_left _ _)
  · intro g hg k hk hne
    have hsne : g⁻¹ * k ≠ 1 := fun hcon => hne (inv_mul_eq_one.mp hcon)
    have hsep1 : (1 : ℝ) ≤ ‖L.V (g⁻¹ * k) - 1‖ :=
      L.separated _ (hquot g hg k hk) hsne
    have hgs : g * (g⁻¹ * k) = k := by group
    have hmul2 : ‖L.V k - L.V g * L.V (g⁻¹ * k)‖ ≤ min ε (1 / 2) := by
      have hstep := L.multiplicative g (hFsub g hg) (g⁻¹ * k)
        (hquot g hg k hk) (by rw [hgs]; exact hFsub k hk)
      rwa [hgs] at hstep
    have hAstar : (L.V g)ᴴ * L.V g = 1 := by
      have hu := L.isUnitary g
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
      exact hu
    have hAAstar : L.V g * (L.V g)ᴴ = 1 := by
      have hu := L.isUnitary g
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu
      exact hu
    have hAmem : (L.V g)ᴴ ∈ Matrix.unitaryGroup L.carrier ℂ :=
      conjTranspose_mem_unitaryGroup (L.isUnitary g)
    have hkey : ‖L.V g - L.V k‖
        = ‖(1 : Matrix L.carrier L.carrier ℂ) - (L.V g)ᴴ * L.V k‖ := by
      rw [show (1 : Matrix L.carrier L.carrier ℂ) - (L.V g)ᴴ * L.V k
          = (L.V g)ᴴ * (L.V g - L.V k) by rw [mul_sub, hAstar],
        CStarRing.norm_mem_unitary_mul _ hAmem]
    have hclose : ‖(L.V g)ᴴ * L.V k - L.V (g⁻¹ * k)‖ ≤ min ε (1 / 2) := by
      rw [show L.V k - L.V g * L.V (g⁻¹ * k)
          = L.V g * ((L.V g)ᴴ * L.V k - L.V (g⁻¹ * k)) by
        rw [mul_sub, ← mul_assoc, hAAstar, one_mul],
        CStarRing.norm_mem_unitary_mul _ (L.isUnitary g)] at hmul2
      exact hmul2
    have htri : ‖(1 : Matrix L.carrier L.carrier ℂ) - L.V (g⁻¹ * k)‖
        ≤ ‖(1 : Matrix L.carrier L.carrier ℂ) - (L.V g)ᴴ * L.V k‖
          + ‖(L.V g)ᴴ * L.V k - L.V (g⁻¹ * k)‖ := by
      rw [← sub_add_sub_cancel (1 : Matrix L.carrier L.carrier ℂ)
        ((L.V g)ᴴ * L.V k) (L.V (g⁻¹ * k))]
      exact norm_add_le _ _
    have hrev : (1 : ℝ) ≤ ‖(1 : Matrix L.carrier L.carrier ℂ) - L.V (g⁻¹ * k)‖ := by
      rwa [norm_sub_rev]
    have hhalf : min ε (1 / 2) ≤ 1 / 2 := min_le_right _ _
    rw [hkey]
    linarith

/-- The printed **Lemma `lem:local-models`** (locality with fixed separation),
sentence `40a6148737bf`: "The following finite-domain formulation is derived
from Korchagin~\cite[Proposition~7]{Korchagin}."

A countable group is MF if and only if every finite `F ∋ 1` and every `ε > 0`
admit a `d ≥ 1` and a `V : F → U(d)` with `V 1 = 1`, defect at most `ε` on `F`,
and `‖V g - 1‖ ≥ 1` for `g ∈ F \ {1}`. -/
theorem isOperatorMF_iff_isLocallyModelled [Countable G] :
    IsOperatorMF G ↔ IsLocallyModelled G := by
  constructor
  · intro hMF F hF ε hε
    exact exists_localModel_of_isOperatorMF hMF F hF hε
  · exact isOperatorMF_of_isLocallyModelled

/-! ## The Kleene--Mostowski vocabulary (`sec:local`, after the lemma) -/

/-- `sec:local`, sentence `b4a096a92e57`, first clause: "a set `A ⊆ ℕ` is
`Σ⁰₁` if `A = {x : ∃ y, R x y}` for a decidable relation `R`." -/
def PrintedSigma01 {A : Type} [Primcodable A] (p : A → Prop) : Prop :=
  ∃ R : A × ℕ → Bool, Computable R ∧ ∀ a, p a ↔ ∃ y : ℕ, R (a, y) = true

/-- `sec:local`, sentence `b4a096a92e57`, second clause: "it is `Π⁰₁` if its
complement is `Σ⁰₁`." -/
def PrintedPi01 {A : Type} [Primcodable A] (p : A → Prop) : Prop :=
  PrintedSigma01 fun a => ¬ p a

/-- `sec:local`, sentence `b4a096a92e57`, third clause: `Σ⁰₂` is the class
`{x : ∃ y ∀ z, R x y z}` with `R` decidable. -/
def PrintedSigma02 {A : Type} [Primcodable A] (p : A → Prop) : Prop :=
  ∃ R : (A × ℕ) × ℕ → Bool, Computable R ∧
    ∀ a, p a ↔ ∃ y : ℕ, ∀ z : ℕ, R ((a, y), z) = true

/-- `sec:local`, sentence `b4a096a92e57`, fourth clause: `Π⁰₂` is the class
`{x : ∀ y ∃ z, R x y z}` with `R` decidable. -/
def PrintedPi02 {A : Type} [Primcodable A] (p : A → Prop) : Prop :=
  ∃ R : (A × ℕ) × ℕ → Bool, Computable R ∧
    ∀ a, p a ↔ ∀ y : ℕ, ∃ z : ℕ, R ((a, y), z) = true

/-- The printed `Σ⁰₁` normal form is the repository's first existential
level. -/
theorem sigma01_of_printedSigma01 {A : Type} [Primcodable A] {p : A → Prop}
    (h : PrintedSigma01 p) : Sigma01 p := by
  obtain ⟨R, hR, hiff⟩ := h
  exact (WordProblemRE.rePred_exists_eq_true (g := fun (a : A) (y : ℕ) => R (a, y))
    hR.to₂).of_eq fun a => (hiff a).symm

/-- The printed `Π⁰₁` normal form is the repository's first universal level. -/
theorem pi01_of_printedPi01 {A : Type} [Primcodable A] {p : A → Prop}
    (h : PrintedPi01 p) : Pi01 p :=
  sigma01_of_printedSigma01 h

/-- The printed `Π⁰₂` normal form is the repository's `Pi02`. -/
theorem pi02_of_printedPi02 {A : Type} [Primcodable A] {p : A → Prop}
    (h : PrintedPi02 p) : Pi02 p := by
  obtain ⟨R, hR, hiff⟩ := h
  refine pi02_of_re_family
    (q := fun z : A × ℕ => ∃ c : ℕ, R (z, c) = true) ?_ hiff
  exact WordProblemRE.rePred_exists_eq_true
    (g := fun (z : A × ℕ) (c : ℕ) => R (z, c)) hR.to₂

/-- The printed `Σ⁰₂` normal form is the repository's `Sigma02`. -/
theorem sigma02_of_printedSigma02 {A : Type} [Primcodable A] {p : A → Prop}
    (h : PrintedSigma02 p) : Sigma02 p := by
  obtain ⟨R, hR, hiff⟩ := h
  refine pi02_of_printedPi02 (p := fun a => ¬ p a) ⟨fun w => !R w, ?_, ?_⟩
  · refine (Computable.cond hR (Computable.const false)
      (Computable.const true)).of_eq ?_
    intro w
    cases R w <;> rfl
  · intro a
    change (¬ p a) ↔
      ∀ y : ℕ, ∃ z : ℕ, (fun w => !R w) ((a, y), z) = true
    rw [hiff]
    constructor
    · intro hn y
      by_contra hcon
      refine hn ⟨y, fun z => ?_⟩
      by_contra hz
      exact hcon ⟨z, by simpa using hz⟩
    · rintro hall ⟨y, hy⟩
      obtain ⟨z, hz⟩ := hall y
      have := hy z
      simp [this] at hz

/-! ## The effective coding of finite presentations -/

/-- `sec:local`, sentence `8d2338091a30`: "Fix an effective coding of finite
presentations by natural numbers, under which a code determines computably its
number of generators and its finite list of relator words, and write `G_P` for
the group presented by the code `P`."

The coding is `PresentationCodes.PresentationCode`; `genCount` is the number of
generators, `P.2` the list of relator words, and `Carrier P` the group `G_P`,
which is finitely presented. -/
theorem effective_presentation_coding :
    Computable (fun P : PresentationCode => genCount P) ∧
      Computable (fun P : PresentationCode => P.2) ∧
        ∀ P : PresentationCode, Group.IsFinitelyPresented (Carrier P) := by
  refine ⟨(Primrec.succ.comp Primrec.fst).to_comp, Primrec.snd.to_comp,
    fun _ => inferInstance⟩

/-- `sec:local`, sentence `bbf9fb702b83`, first half: `MF_fp` is the set of
codes `P` such that `G_P` is MF. -/
def MFfp : Set PresentationCode := {P | IsOperatorMF (Carrier P)}

/-- `sec:local`, sentence `bbf9fb702b83`, second half: `NONMF_fp` is the
complement of `MF_fp`. -/
def NONMFfp : Set PresentationCode := MFfpᶜ

/-- Membership in the two sets, unfolded.  This is the witness theorem that
pins the two set-valued definitions to the recognition predicate. -/
theorem mem_MFfp_iff (P : PresentationCode) :
    P ∈ MFfp ↔ IsOperatorMF (Carrier P) := by
  simp [MFfp]

/-- Membership in the complement, unfolded. -/
theorem mem_NONMFfp_iff (P : PresentationCode) :
    P ∈ NONMFfp ↔ ¬ IsOperatorMF (Carrier P) := by
  simp [NONMFfp, MFfp]

/-- `sec:local`, sentence `932c401654c9`, first clause: "Korchagin's
Proposition~8~\cite{Korchagin} is the finite-presentation form of
Lemma~\ref{lem:local-models}."

Literally Lemma `lem:local-models` read at a presentation code: the coded group
is countable, so the lemma applies to it verbatim. -/
theorem korchagin_proposition_eight (P : PresentationCode) :
    IsOperatorMF (Carrier P) ↔ IsLocallyModelled (Carrier P) :=
  isOperatorMF_iff_isLocallyModelled

/-! ## The executable finite-certificate proposition -/

/-- The manuscript's decidable relation `C(P,n,c)`, using the total challenge
and answer decoders of the executable checker. -/
def PrintedFiniteCertificate (P : PresentationCode) (n c : ℕ) : Bool :=
  MFRecognitionPi02.MFChecker P n c

/-- Validity of one printed certificate is primitive recursive. -/
theorem printedFiniteCertificate_primrec :
    Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      PrintedFiniteCertificate z.1.1 z.1.2 z.2 :=
  MFRecognitionPi02.primrec_MFChecker

/-- **Proposition `prop:mf-upper-bound`, checker equivalence.** -/
theorem isOperatorMF_iff_forall_exists_printedFiniteCertificate
    (P : PresentationCode) :
    IsOperatorMF (Carrier P) ↔
      ∀ n, ∃ c, PrintedFiniteCertificate P n c = true :=
  MFRecognitionPi02.isOperatorMF_iff_forall_exists_MFChecker P

/-- **Proposition `prop:mf-upper-bound`, hierarchy conclusion.** -/
theorem manuscriptFiniteCertificatesUpperBound :
    Pi02 (fun P : PresentationCode => IsOperatorMF (Carrier P)) ∧
      Sigma02 (fun P : PresentationCode => ¬ IsOperatorMF (Carrier P)) :=
  ⟨MFRecognitionPi02.operatorMFCode_pi02,
    MFRecognitionPi02.nonOperatorMFCode_sigma02⟩

end

end Certificates
end MFRecognition
end Manuscript
end GroupApproximation
