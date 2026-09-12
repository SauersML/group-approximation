import GroupApproximation.KunThom.CompressorNormalizationAssemblyThreshold
import GroupApproximation.KunThom.SequentialContradiction

/-!
# The per-compressor assembly over concrete cluster frames

`seqNormalizes_of_compressor_of_steps` runs over abstract frames.  Here the
frames are `ClusterFrame`s over the retained components of each decomposition,
with the repair factor of the decomposition and a vanishing threshold, and three
of its hypotheses are discharged.

* `hframe`: `exists_clusterFrame`, once the generators of the retained
  components contain a Kazhdan pair and the repair factor is at least `4`.
* `hconv`: `ClusterFrame.almostCommutes_patch`.
* `hwrapper`: `seqNormalizes_of_forall_not_uniform_lower_bound`.

The remaining hypotheses of `seqNormalizes_of_compressor_of_frameSteps` are
stated for `ClusterFrame`, `ClusterFrame.Bis` and `ClusterFrame.patch`.  In
particular `hrep`, the forward half of Kun--Thom Lemma 4.2(4), reads: for a frame
with the repair factor of the decomposition and a vanishing threshold `h`, and a
sequence `v` almost commuting with `A(Γ)` whose generator defect is `o(h)`, some
sequence of total bisections has patched permutations close to `v`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

/-- **The forward inclusion for one compressor, over cluster frames.**

The decomposition data `Decomp A` of a sofic approximation `A` carry retained
components `retained D` of `Γ` and a repair factor `repairFactor D`.  Relative
data `Rel F` of the compressor `t` sit over every cluster frame `F`.

The hypotheses, with the lanes that own them:
* `hdecomp`, `hdefect` (kt41-seq-decomp): decomposition data exist, and the
  generator defect of an almost-centralizer is nonnegative and vanishes;
* `hkazhdan` (kt41-seq-decomp): the repair factor is at least `4` and the
  generators contain a Kazhdan pair;
* `hmatching` (kt41-matching): the matching error is nonnegative and vanishes;
* `hrep` (kt41-bisection-rep): Kun--Thom Lemma 4.2(4), forward half;
* `hfunctor` (kt41-functor, kt41-functor-estimate): Lemma 4.3 at frames whose
  threshold dominates the matching error;
* `honesided`, `hcounting` (kt41-counting-endgame), `hmedian`
  (kt41-median-vertex): the one-sided inequalities, their concentration, and the
  transported bisections;
* `hhamming` (kt41-hamming): transported bisections are close to the
  conjugates. -/
theorem seqNormalizes_of_compressor_of_frameSteps {G : Type} [Group G] {Γ : Subgroup G}
    {t : G}
    (Decomp : SoficApproximation G → Type*)
    (retained : ∀ {A : SoficApproximation G}, Decomp A → RetainedComponents A ↥Γ Γ.subtype)
    (repairFactor : ∀ {A : SoficApproximation G}, Decomp A → ℝ)
    (generatorDefect : ∀ {A : SoficApproximation G}, Decomp A →
      (∀ n, Equiv.Perm (A.model n)) → ℕ → ℝ)
    (matchingError : ∀ {A : SoficApproximation G}, Decomp A → ℕ → ℝ)
    (Rel : ∀ {A : SoficApproximation G} {D : Decomp A}, ClusterFrame (retained D) → Type*)
    (OneSided : ∀ {A : SoficApproximation G} {D : Decomp A} {F : ClusterFrame (retained D)},
      Rel F → Prop)
    (Concentrated : ∀ {A : SoficApproximation G} {D : Decomp A}
      {F : ClusterFrame (retained D)}, Rel F → Prop)
    (Transported : ∀ {A : SoficApproximation G} {D : Decomp A}
      {F : ClusterFrame (retained D)}, Rel F → (∀ n, F.Bis n) → (∀ n, F.Bis n) → Prop)
    (hdecomp : ∀ A : SoficApproximation G, Nonempty (Decomp A))
    (hkazhdan : ∀ (A : SoficApproximation G) (D : Decomp A), 4 ≤ repairFactor D ∧
      ∃ (Q : Finset ↥Γ) (κ : ℝ), IsKazhdanPair.{0, 0} ↥Γ Q κ ∧
        Q ⊆ (retained D).data.generators ∧ κ ≤ 1)
    (hdefect : ∀ (A : SoficApproximation G) (D : Decomp A)
      (v : ∀ n, Equiv.Perm (A.model n)), (∀ γ ∈ Γ, A.AlmostCommutes v γ) →
        (∀ n, 0 ≤ generatorDefect D v n) ∧ Vanishing (generatorDefect D v))
    (hmatching : ∀ (A : SoficApproximation G) (D : Decomp A),
      (∀ n, 0 ≤ matchingError D n) ∧ Vanishing (matchingError D))
    (hrep : ∀ (A : SoficApproximation G) (D : Decomp A) (F : ClusterFrame (retained D)),
      F.repairFactor = repairFactor D → Vanishing F.threshold →
        ∀ v : ∀ n, Equiv.Perm (A.model n), (∀ γ ∈ Γ, A.AlmostCommutes v γ) →
          (Vanishing fun n ↦ generatorDefect D v n / F.threshold n) →
            ∃ a : ∀ n, F.Bis n,
              Vanishing fun n ↦ hammingDistance (A.model n) (v n) (F.patch n (a n)))
    (hfunctor : ∀ (A : SoficApproximation G) (D : Decomp A) (F : ClusterFrame (retained D)),
      F.repairFactor = repairFactor D → Vanishing F.threshold →
        (Vanishing fun n ↦ matchingError D n / F.threshold n) → Nonempty (Rel F))
    (honesided : ∀ (A : SoficApproximation G) (D : Decomp A) (F : ClusterFrame (retained D))
      (R : Rel F), OneSided R)
    (hmedian : ∀ (A : SoficApproximation G) (D : Decomp A) (F : ClusterFrame (retained D))
      (R : Rel F), OneSided R → Concentrated R)
    (hcounting : ∀ (A : SoficApproximation G) (D : Decomp A) (F : ClusterFrame (retained D))
      (R : Rel F), Concentrated R → ∀ a : ∀ n, F.Bis n, ∃ b : ∀ n, F.Bis n,
        Transported R a b)
    (hhamming : ∀ (A : SoficApproximation G) (D : Decomp A) (F : ClusterFrame (retained D))
      (R : Rel F) (a b : ∀ n, F.Bis n), Transported R a b →
        Vanishing fun n ↦ hammingDistance (A.model n) (F.patch n (b n))
          (A.map n t * F.patch n (a n) * (A.map n t)⁻¹)) :
    SeqNormalizes Γ t := by
  refine seqNormalizes_of_compressor_of_steps Decomp
    (fun A D ↦ {F : ClusterFrame (retained (A := A) D) //
      F.repairFactor = repairFactor D ∧ Vanishing F.threshold})
    (fun F ↦ F.1.threshold) (fun F n ↦ F.1.Bis n) (fun F n b ↦ F.1.patch n b)
    generatorDefect matchingError (fun F ↦ Rel F.1) (fun R ↦ OneSided R)
    (fun R ↦ Concentrated R) (fun R a b ↦ Transported R a b) hdecomp hdefect hmatching
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro A D ρ hρ0 hρ
    obtain ⟨hK₀, Q, κ, hQ, hQT, hκ⟩ := hkazhdan A D
    obtain ⟨F, hF, hpos, hthr, hdom⟩ :=
      exists_clusterFrame (retained D) hQ hQT hκ (repairFactor D) hK₀ ρ hρ0 hρ
    exact ⟨⟨F, hF, hthr⟩, hpos, hthr, hdom⟩
  · intro A D F v hv hdom
    exact hrep A D F.1 F.2.1 F.2.2 v hv hdom
  · intro A D F hthr b γ hγ
    exact F.1.almostCommutes_patch hthr b γ hγ
  · intro A D F hdom
    exact hfunctor A D F.1 F.2.1 F.2.2 hdom
  · intro A D F R
    exact honesided A D F.1 R
  · intro A D F R h
    exact hmedian A D F.1 R h
  · intro A D F R h a
    exact hcounting A D F.1 R h a
  · intro A D F R a b h
    exact hhamming A D F.1 R a b h
  · exact seqNormalizes_of_forall_not_uniform_lower_bound

end CompressorNormalizationAssembly
end GroupApproximation
