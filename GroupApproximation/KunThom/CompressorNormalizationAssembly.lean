import GroupApproximation.KunThom.NormalizationFromCriterion

/-!
# Assembling the forward inclusion for one compressor

Kun--Thom's Theorem 4.1 (arXiv:2608.06222v3, §4) reduces, by
`hasSequentialCentralizerNormalization_of_compressorNormalization`, to the
forward inclusion `SeqNormalizes Γ t` for a single compressor `t`.  Fix a sofic
approximation `A` of `G` and a sequence `v` almost commuting with `A(Γ)`.  The
proof in the paper runs as follows.

1. Decompose `A|Γ` and `A` into expander components (Kun's theorem).
2. Record the matching error of `t` on the full partition of `Γ`-components,
   and the generator defect of `v`.
3. Choose the cluster threshold so slowly that both error sequences are
   `o` of it, and build the cluster groupoid at that threshold
   (Lemma 4.2(1)--(3)).
4. Represent `v` by patched total bisections `â` (Lemma 4.2(4)).
5. Build the relative functor of `t` (Lemma 4.3), prove the one-sided orbit
   and isotropy inequalities, amplify them by the median lemma (Lemma 4.4), and
   count: this gives transported total bisections `b`.
6. Bound `d_H(b̂, A(t) â A(t)⁻¹)` (the last estimate of the proof).
7. Patched bisections almost commute with `A(Γ)` (Lemma 4.2(4), converse),
   so `A(t) v A(t)⁻¹`, being close to `b̂`, almost commutes with `A(Γ)`.

`seqNormalizes_of_compressor_of_steps` carries out steps 3 and 7: the joint
scale choice and the final comparison.  Every other step enters as an explicit
hypothesis about abstract data: decompositions, cluster frames with their
thresholds, total bisections and their patched permutations, relative data of
the compressor, and the Props recording the one-sided inequalities,
concentration and the counting output.  A later module instantiates the
abstract data with the concrete constructions and discharges the hypotheses.

`almostCommutes_conjSeq_of_transport` is the final comparison on its own.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

/-- **The final comparison.**  If `v` is close to `a`, `b` is close to
`A(t) a A(t)⁻¹`, and `b` almost commutes with `A(γ)`, then `A(t) v A(t)⁻¹`
almost commutes with `A(γ)`. -/
theorem almostCommutes_conjSeq_of_transport {G : Type} [Group G]
    (A : SoficApproximation G) {t γ : G} {v a b : ∀ n, Equiv.Perm (A.model n)}
    (hva : Vanishing fun n ↦ hammingDistance (A.model n) (v n) (a n))
    (hab : Vanishing fun n ↦ hammingDistance (A.model n) (b n)
      (A.map n t * a n * (A.map n t)⁻¹))
    (hb : A.AlmostCommutes b γ) :
    A.AlmostCommutes (A.conjSeq t v) γ := by
  have hconj : Vanishing fun n ↦ hammingDistance (A.model n)
      (A.map n t * a n * (A.map n t)⁻¹) (A.map n t * v n * (A.map n t)⁻¹) :=
    A.hamming_conj_close (a := fun n ↦ A.map n t) (b := fun n ↦ A.map n t)
      (v := a) (w := v)
      (Vanishing.zero.congr fun _ ↦ (hammingDistance_self _ _).symm)
      (hva.congr fun _ ↦ hammingDistance_comm _ _ _)
  have hclose : Vanishing fun n ↦ hammingDistance (A.model n) (b n)
      (A.map n t * v n * (A.map n t)⁻¹) :=
    Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _)
      (fun n ↦ hammingDistance_triangle (A.model n) (b n)
        (A.map n t * a n * (A.map n t)⁻¹) (A.map n t * v n * (A.map n t)⁻¹))
      (hab.add hconj)
  exact A.almostCommutes_of_close hb hclose

/-- **The forward inclusion for one compressor, from its steps.**

The abstract data, for a sofic approximation `A` of `G`:
* `Decomp A`: the decomposition data of step 1;
* `generatorDefect D v` and `matchingError D`: the two error sequences of
  step 2;
* `Frame A D`: cluster frames over `D`, with candidate threshold
  `threshold F`, total bisections `Bis F n` at index `n` and their patched
  permutations `patch F n`;
* `Rel F`: relative data of `t` at the frame `F` (component matching and
  relative functor);
* `OneSided R`, `Concentrated R` and `Transported R a b`: the one-sided orbit
  and isotropy inequalities, their concentration, and the counting output
  relating a sequence `a` of total bisections to a sequence `b`.

The hypotheses, one per open step of Kun--Thom §4, with the lanes that own
them:
* `hdecomp` (kt41-seq-decomp): decomposition data exist;
* `hdefect` (kt41-seq-decomp): for `v` almost commuting with `A(Γ)`, the
  generator defect is nonnegative and vanishes;
* `hmatching` (kt41-matching, kt-norm-repo): the matching error of `t` is
  nonnegative and vanishes;
* `hframe` (kt-norm-paper, kt41-g1-build, kt41-g1-uniform): for every
  nonnegative vanishing sequence `ρ` there is a frame whose threshold is
  positive, vanishes, and satisfies `ρ = o(threshold)`; Lemma 4.2(1)--(3) with
  the joint scale choice;
* `hrep` (kt41-bisection-rep): at every frame whose threshold dominates the
  generator defect of `v`, some sequence of total bisections has patched
  permutations close to `v`; Lemma 4.2(4);
* `hconv` (kt41-bisection-rep-b, kt41-scale): when the threshold vanishes,
  patched permutations of total bisections almost commute with `A(Γ)`; the
  converse half of Lemma 4.2(4);
* `hfunctor` (kt41-functor, kt41-functor-estimate): at every frame whose
  threshold dominates the matching error, relative data exist; Lemma 4.3 with
  estimate (7);
* `honesided` (kt41-counting-endgame): relative data satisfy the one-sided
  inequalities (2) and (3);
* `hmedian` (kt41-median-vertex): the one-sided inequalities concentrate;
  Lemma 4.4;
* `hcounting` (kt41-counting-endgame): under concentration every sequence of
  total bisections has a transported sequence;
* `hhamming` (kt41-hamming): the patched permutations of a transported
  sequence are close to the conjugates by `A(t)` of the original ones;
* `hwrapper` (kt41-seq-wrapper): `SeqNormalizes Γ t` holds once no sofic
  approximation carries an almost-centralizer of `Γ` whose conjugate by `A(t)`
  keeps its commutator with some `A(γ)` at least a fixed `ε > 0` at every index.

The proof works inside `hwrapper`.  Given such `A`, `v`, `γ` and `ε`, it makes
the joint scale choice, runs the steps along the full sequence, and obtains that
`A(t) v A(t)⁻¹` almost commutes with `A(γ)`, which contradicts the lower
bound. -/
theorem seqNormalizes_of_compressor_of_steps {G : Type} [Group G] {Γ : Subgroup G} {t : G}
    (Decomp : SoficApproximation G → Type*)
    (Frame : ∀ A : SoficApproximation G, Decomp A → Type*)
    (threshold : ∀ {A : SoficApproximation G} {D : Decomp A}, Frame A D → ℕ → ℝ)
    (Bis : ∀ {A : SoficApproximation G} {D : Decomp A}, Frame A D → ℕ → Type*)
    (patch : ∀ {A : SoficApproximation G} {D : Decomp A} (F : Frame A D) (n : ℕ),
      Bis F n → Equiv.Perm (A.model n))
    (generatorDefect : ∀ {A : SoficApproximation G}, Decomp A →
      (∀ n, Equiv.Perm (A.model n)) → ℕ → ℝ)
    (matchingError : ∀ {A : SoficApproximation G}, Decomp A → ℕ → ℝ)
    (Rel : ∀ {A : SoficApproximation G} {D : Decomp A}, Frame A D → Type*)
    (OneSided : ∀ {A : SoficApproximation G} {D : Decomp A} {F : Frame A D},
      Rel F → Prop)
    (Concentrated : ∀ {A : SoficApproximation G} {D : Decomp A} {F : Frame A D},
      Rel F → Prop)
    (Transported : ∀ {A : SoficApproximation G} {D : Decomp A} {F : Frame A D},
      Rel F → (∀ n, Bis F n) → (∀ n, Bis F n) → Prop)
    (hdecomp : ∀ A : SoficApproximation G, Nonempty (Decomp A))
    (hdefect : ∀ (A : SoficApproximation G) (D : Decomp A)
      (v : ∀ n, Equiv.Perm (A.model n)), (∀ γ ∈ Γ, A.AlmostCommutes v γ) →
        (∀ n, 0 ≤ generatorDefect D v n) ∧ Vanishing (generatorDefect D v))
    (hmatching : ∀ (A : SoficApproximation G) (D : Decomp A),
      (∀ n, 0 ≤ matchingError D n) ∧ Vanishing (matchingError D))
    (hframe : ∀ (A : SoficApproximation G) (D : Decomp A) (ρ : ℕ → ℝ),
      (∀ n, 0 ≤ ρ n) → Vanishing ρ →
        ∃ F : Frame A D, (∀ n, 0 < threshold F n) ∧ Vanishing (threshold F) ∧
          Vanishing fun n ↦ ρ n / threshold F n)
    (hrep : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D)
      (v : ∀ n, Equiv.Perm (A.model n)), (∀ γ ∈ Γ, A.AlmostCommutes v γ) →
        (Vanishing fun n ↦ generatorDefect D v n / threshold F n) →
          ∃ a : ∀ n, Bis F n,
            Vanishing fun n ↦ hammingDistance (A.model n) (v n) (patch F n (a n)))
    (hconv : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D),
      Vanishing (threshold F) → ∀ b : ∀ n, Bis F n, ∀ γ ∈ Γ,
        A.AlmostCommutes (fun n ↦ patch F n (b n)) γ)
    (hfunctor : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D),
      (Vanishing fun n ↦ matchingError D n / threshold F n) → Nonempty (Rel F))
    (honesided : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D)
      (R : Rel F), OneSided R)
    (hmedian : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D)
      (R : Rel F), OneSided R → Concentrated R)
    (hcounting : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D)
      (R : Rel F), Concentrated R → ∀ a : ∀ n, Bis F n, ∃ b : ∀ n, Bis F n,
        Transported R a b)
    (hhamming : ∀ (A : SoficApproximation G) (D : Decomp A) (F : Frame A D)
      (R : Rel F) (a b : ∀ n, Bis F n), Transported R a b →
        Vanishing fun n ↦ hammingDistance (A.model n) (patch F n (b n))
          (A.map n t * patch F n (a n) * (A.map n t)⁻¹))
    (hwrapper : (∀ (A : SoficApproximation G) (v : ∀ n, Equiv.Perm (A.model n)),
      (∀ γ ∈ Γ, A.AlmostCommutes v γ) → ∀ γ ∈ Γ, ∀ ε : ℝ, 0 < ε →
        (∀ n, ε ≤ hammingDistance (A.model n) (A.conjSeq t v n * A.map n γ)
          (A.map n γ * A.conjSeq t v n)) → False) → SeqNormalizes Γ t) :
    SeqNormalizes Γ t := by
  refine hwrapper fun A v hv γ hγ ε hε hbound ↦ ?_
  have hcomm : A.AlmostCommutes (A.conjSeq t v) γ := by
    obtain ⟨D⟩ := hdecomp A
    obtain ⟨hτ₀, hτ⟩ := hdefect A D v hv
    obtain ⟨he₀, he⟩ := hmatching A D
    obtain ⟨F, hpos, hthr, hdom⟩ :=
      hframe A D (fun n ↦ generatorDefect D v n + matchingError D n)
        (fun n ↦ add_nonneg (hτ₀ n) (he₀ n)) (hτ.add he)
    have hdomτ : Vanishing fun n ↦ generatorDefect D v n / threshold F n :=
      Vanishing.squeeze (fun n ↦ div_nonneg (hτ₀ n) (hpos n).le)
        (fun n ↦ div_le_div_of_nonneg_right (le_add_of_nonneg_right (he₀ n)) (hpos n).le)
        hdom
    have hdome : Vanishing fun n ↦ matchingError D n / threshold F n :=
      Vanishing.squeeze (fun n ↦ div_nonneg (he₀ n) (hpos n).le)
        (fun n ↦ div_le_div_of_nonneg_right (le_add_of_nonneg_left (hτ₀ n)) (hpos n).le)
        hdom
    obtain ⟨α, hα⟩ := hrep A D F v hv hdomτ
    obtain ⟨R⟩ := hfunctor A D F hdome
    obtain ⟨β, hβ⟩ := hcounting A D F R (hmedian A D F R (honesided A D F R)) α
    exact almostCommutes_conjSeq_of_transport A hα (hhamming A D F R α β hβ)
      (hconv A D F hthr β γ hγ)
  obtain ⟨N, hN⟩ := hcomm ε hε
  have h₁ : ε ≤ hammingDistance (A.model N) (A.conjSeq t v N * A.map N γ)
      (A.map N γ * A.conjSeq t v N) := hbound N
  have h₂ : hammingDistance (A.model N) (A.conjSeq t v N * A.map N γ)
      (A.map N γ * A.conjSeq t v N) < ε := lt_of_abs_lt (hN N le_rfl)
  linarith

end CompressorNormalizationAssembly
end GroupApproximation
