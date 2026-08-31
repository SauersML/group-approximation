import GroupApproximation.GGT.DGOQuasiGeodesicChainAt
import GroupApproximation.GGT.HullSCSmallCancellation
import GroupApproximation.GGT.HullSCRelatorFamily

/-!
# Hull's published small-cancellation and prime-piece inputs

Hull's Lemmas 4.4 and 4.9 use more than the repository's original
`RelWord.IsSmallCancellation` structure.  These definitions are kept in a
small dependency module so every quotient and relator interface can share the
same source-faithful premise without importing the later filling machinery.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-- Hull's published `ε`-piece relation with both compared subwords exposed. -/
def RelWord.IsPublishedPiece {G : Type u} [Group G] {Λ : Type*}
    (D : GGT.RelGenSet G Λ) (W : Set (List (GGT.RelLetter G Λ)))
    (eps : ℕ) (u u' v : List (GGT.RelLetter G Λ)) : Prop :=
  v ∈ W ∧ (∃ s, v = u ++ s) ∧
    ∃ v' ∈ W, ∃ s', v' = u' ++ s' ∧
      ∃ y z : G, WordMetric.wordNorm D.base y ≤ eps ∧
        WordMetric.wordNorm D.base z ≤ eps ∧
        GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z ∧
        GGT.RelLetter.listVal v' ≠
          y * GGT.RelLetter.listVal v * y⁻¹

/-- Hull's published `ε`-primepiece relation. -/
def RelWord.IsPrimePiece {G : Type u} [Group G] {Λ : Type*}
    (D : GGT.RelGenSet G Λ) (W : Set (List (GGT.RelLetter G Λ)))
    (eps : ℕ) (u u' v : List (GGT.RelLetter G Λ)) : Prop :=
  v ∈ W ∧
    ∃ middle tail, v = u ++ middle ++ u' ++ tail ∧
      ∃ y z : G, WordMetric.wordNorm D.base y ≤ eps ∧
        WordMetric.wordNorm D.base z ≤ eps ∧
        (GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z ∨
          GGT.RelLetter.listVal u' = y * (GGT.RelLetter.listVal u)⁻¹ * z)

/-- The branch of a published piece whose two exposed prefixes belong to the
same word.  The older `IsPiece` predicate covers the complementary branch,
where the second word is syntactically distinct. -/
def RelWord.IsSameWordPublishedPiece {G : Type u} [Group G] {Λ : Type*}
    (D : GGT.RelGenSet G Λ) (W : Set (List (GGT.RelLetter G Λ)))
    (eps : ℕ) (u u' v : List (GGT.RelLetter G Λ)) : Prop :=
  v ∈ W ∧ (∃ s, v = u ++ s) ∧ (∃ s', v = u' ++ s') ∧
    ∃ y z : G, WordMetric.wordNorm D.base y ≤ eps ∧
      WordMetric.wordNorm D.base z ≤ eps ∧
      GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z ∧
      GGT.RelLetter.listVal v ≠
        y * GGT.RelLetter.listVal v * y⁻¹

/-- Every published piece is either already an old-style piece, to which the
existing separation theorem applies, or is the precise same-word branch that
must be handled by Hull's prime-piece/aperiodicity argument. -/
theorem RelWord.IsPublishedPiece.toIsPiece_or_sameWord
    {G : Type u} [Group G] {Λ : Type*}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps : ℕ} {u u' v : List (GGT.RelLetter G Λ)}
    (h : RelWord.IsPublishedPiece D W eps u u' v) :
    RelWord.IsPiece D W eps u v ∨
      RelWord.IsSameWordPublishedPiece D W eps u u' v := by
  rcases h with ⟨hv, hpre, v', hv', s', hv'pre, y, z, hy, hz, huv, hneq⟩
  by_cases hvv : v' = v
  · have hvpreSame : v = u' ++ s' := by simpa only [hvv] using hv'pre
    have hneqSame : GGT.RelLetter.listVal v ≠
        y * GGT.RelLetter.listVal v * y⁻¹ := by simpa only [hvv] using hneq
    exact Or.inr ⟨hv, hpre, ⟨s', hvpreSame⟩,
      y, z, hy, hz, huv, hneqSame⟩
  · exact Or.inl ⟨hv, hpre, v', hv', hvv, u', s', hv'pre,
      y, z, hy, hz, huv, hneq⟩

/-- In the distinct-word branch, a published piece gives old-style pieces in
both directions.  The reverse direction uses the inverse short connectors;
symmetry of the base preserves their word norms, and the published exclusion
is invariant under reversing the conjugacy equation. -/
theorem RelWord.IsPublishedPiece.isPiece_pair_of_distinct
    {G : Type u} [Group G] {Λ : Type*}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps : ℕ} {u u' v v' : List (GGT.RelLetter G Λ)}
    (hbase : IsSymmetricGeneratingSet D.base)
    (hv : v ∈ W) (hpre : ∃ s, v = u ++ s)
    (hv' : v' ∈ W) (hpre' : ∃ s', v' = u' ++ s')
    (hne : v' ≠ v) {y z : G}
    (hy : WordMetric.wordNorm D.base y ≤ eps)
    (hz : WordMetric.wordNorm D.base z ≤ eps)
    (huv : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z)
    (hneq : GGT.RelLetter.listVal v' ≠
      y * GGT.RelLetter.listVal v * y⁻¹) :
    RelWord.IsPiece D W eps u v ∧ RelWord.IsPiece D W eps u' v' := by
  obtain ⟨s, hs⟩ := hpre
  obtain ⟨s', hs'⟩ := hpre'
  have hyinv : WordMetric.wordNorm D.base y⁻¹ ≤ eps := by
    rw [WordMetric.wordNorm_inv hbase y]
    exact hy
  have hzinv : WordMetric.wordNorm D.base z⁻¹ ≤ eps := by
    rw [WordMetric.wordNorm_inv hbase z]
    exact hz
  have huv' : GGT.RelLetter.listVal u =
      y⁻¹ * GGT.RelLetter.listVal u' * z⁻¹ := by
    rw [huv]
    group
  have hneq' : GGT.RelLetter.listVal v ≠
      y⁻¹ * GGT.RelLetter.listVal v' * (y⁻¹)⁻¹ := by
    intro heq
    apply hneq
    rw [heq]
    group
  exact ⟨⟨hv, ⟨s, hs⟩, v', hv', hne, u', s', hs',
      y, z, hy, hz, huv, hneq⟩,
    ⟨hv', ⟨s', hs'⟩, v, hv, Ne.symm hne, u, s, hs,
      y⁻¹, z⁻¹, hyinv, hzinv, huv', hneq'⟩⟩

/-- For a symmetrized one-relator family, the old one-sided piece estimate
already controls both prefix lengths in every distinct-word published piece.
Only the same-word branch remains to be supplied. -/
theorem RelWord.publishedPiecesSmall_symmetrized_of_piecesSmall_of_sameWord
    {G : Type u} [Group G] {Λ : Type*}
    {D : GGT.RelGenSet G Λ} {r : List (GGT.RelLetter G Λ)}
    {eps rho : ℕ} {mu : ℝ}
    (hbase : IsSymmetricGeneratingSet D.base)
    (hsc : RelWord.IsSmallCancellation D (RelWord.symmetrized r) eps mu rho)
    (hsame : ∀ u u' v,
      RelWord.IsSameWordPublishedPiece D (RelWord.symmetrized r) eps u u' v →
        max (u.length : ℝ) (u'.length : ℝ) < mu * v.length) :
    ∀ u u' v,
      RelWord.IsPublishedPiece D (RelWord.symmetrized r) eps u u' v →
        max (u.length : ℝ) (u'.length : ℝ) < mu * v.length := by
  intro u u' v hpub
  rcases hpub with ⟨hv, hpre, v', hv', s', hv'pre,
    y, z, hy, hz, huv, hneq⟩
  by_cases hne : v' = v
  · have hvpreSame : v = u' ++ s' := by simpa only [hne] using hv'pre
    have hneqSame : GGT.RelLetter.listVal v ≠
        y * GGT.RelLetter.listVal v * y⁻¹ := by simpa only [hne] using hneq
    exact hsame u u' v ⟨hv, hpre, ⟨s', hvpreSame⟩,
      y, z, hy, hz, huv, hneqSame⟩
  · obtain ⟨hu, hu'⟩ :=
      RelWord.IsPublishedPiece.isPiece_pair_of_distinct hbase hv hpre hv'
        ⟨s', hv'pre⟩ hne hy hz huv hneq
    have hlu : (u.length : ℝ) < mu * v.length := hsc.pieces_small u v hu
    have hlu' : (u'.length : ℝ) < mu * v.length := by
      have hraw := hsc.pieces_small u' v' hu'
      have hvlen : v.length = r.length :=
        RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hv)
      have hv'len : v'.length = r.length :=
        RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hv')
      rw [hv'len, ← hvlen] at hraw
      exact hraw
    exact max_lt hlu hlu'

/-- The full hypotheses used by Hull's Lemma 4.4. -/
structure RelWord.IsLemma44Input {G : Type u} [Group G] {Λ : Type*}
    (D : GGT.RelGenSet G Λ) (W : Set (List (GGT.RelLetter G Λ)))
    (eps : ℕ) (mu : ℝ) (rho : ℕ) : Prop extends
    RelWord.IsSmallCancellation D W eps mu rho where
  quasiGeodesic : ∀ v ∈ W,
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      (fun i => GGT.RelLetter.listVal (v.take i)) v.length
  publishedPiecesSmall : ∀ u u' v,
    RelWord.IsPublishedPiece D W eps u u' v →
      max (u.length : ℝ) (u'.length : ℝ) < mu * v.length
  stronglyBounded :
    {a : GGT.RelLetter G Λ |
      (∃ lam h, a = GGT.RelLetter.comp lam h) ∧ ∃ v ∈ W, a ∈ v}.Finite

/-- Hull Lemma 4.9's actual `C₁` input, including prime-piece control. -/
structure RelWord.IsLemma49Input {G : Type u} [Group G] {Λ : Type*}
    (D : GGT.RelGenSet G Λ) (W : Set (List (GGT.RelLetter G Λ)))
    (eps : ℕ) (mu : ℝ) (rho : ℕ) : Prop extends
    RelWord.IsLemma44Input D W eps mu rho where
  primePiecesSmall : ∀ u u' v, RelWord.IsPrimePiece D W eps u u' v →
    max (u.length : ℝ) (u'.length : ℝ) < mu * v.length

/-- The component-letter support of the symmetrized closure of one finite word
is finite.  Thus Hull's strong-boundedness field is automatic for the one-
relator family used by Theorem 7.1; it is not a remaining geometric input. -/
theorem RelWord.finite_componentLetters_symmetrized
    {G : Type u} [Group G] {Λ : Type*}
    (v : List (GGT.RelLetter G Λ)) :
    {a : GGT.RelLetter G Λ |
      (∃ lam h, a = GGT.RelLetter.comp lam h) ∧
        ∃ w ∈ RelWord.symmetrized v, a ∈ w}.Finite := by
  let V : Set (GGT.RelLetter G Λ) := {a | a ∈ v}
  have hV : V.Finite := by
    induction v with
    | nil => simp [V]
    | cons b tail ih =>
        rw [show V = ({b} : Set (GGT.RelLetter G Λ)) ∪ {a | a ∈ tail} by
          ext a
          simp [V]]
        exact (Set.finite_singleton b).union ih
  have hsupport : (V ∪ RelWord.inv '' V).Finite := hV.union (hV.image RelWord.inv)
  refine hsupport.subset ?_
  intro a ha
  obtain ⟨_, w, hw, haw⟩ := ha
  rcases RelWord.Sym.letters (RelWord.mem_symmetrized.mp hw) a haw with hav | hinv
  · exact Set.mem_union_left _ hav
  · refine Set.mem_union_right _ ⟨RelWord.inv a, hinv, ?_⟩
    exact RelWord.inv_inv_letter a

/-- Assemble Hull's Lemma 4.4 input for a one-relator symmetrized family.
Strong boundedness is discharged by finiteness, leaving exactly the ordinary
small-cancellation, quasi-geodesic, and published-piece clauses. -/
theorem RelWord.isLemma44Input_symmetrized_of
    {G : Type u} [Group G] {Λ : Type*} (D : GGT.RelGenSet G Λ)
    (v : List (GGT.RelLetter G Λ)) (eps : ℕ) (mu : ℝ) (rho : ℕ)
    (hsc : RelWord.IsSmallCancellation D (RelWord.symmetrized v) eps mu rho)
    (hqg : ∀ w ∈ RelWord.symmetrized v,
      GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
        (fun i => GGT.RelLetter.listVal (w.take i)) w.length)
    (hpieces : ∀ u u' w,
      RelWord.IsPublishedPiece D (RelWord.symmetrized v) eps u u' w →
        max (u.length : ℝ) (u'.length : ℝ) < mu * w.length) :
    RelWord.IsLemma44Input D (RelWord.symmetrized v) eps mu rho where
  toIsSmallCancellation := hsc
  quasiGeodesic := hqg
  publishedPiecesSmall := hpieces
  stronglyBounded := RelWord.finite_componentLetters_symmetrized v

/-- Assemble Hull's Lemma 4.9 `C₁` input for one relator.  After the preceding
theorem, the only additional obligation is the prime-piece estimate. -/
theorem RelWord.isLemma49Input_symmetrized_of
    {G : Type u} [Group G] {Λ : Type*} (D : GGT.RelGenSet G Λ)
    (v : List (GGT.RelLetter G Λ)) (eps : ℕ) (mu : ℝ) (rho : ℕ)
    (hsc : RelWord.IsSmallCancellation D (RelWord.symmetrized v) eps mu rho)
    (hqg : ∀ w ∈ RelWord.symmetrized v,
      GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
        (fun i => GGT.RelLetter.listVal (w.take i)) w.length)
    (hpieces : ∀ u u' w,
      RelWord.IsPublishedPiece D (RelWord.symmetrized v) eps u u' w →
        max (u.length : ℝ) (u'.length : ℝ) < mu * w.length)
    (hprime : ∀ u u' w,
      RelWord.IsPrimePiece D (RelWord.symmetrized v) eps u u' w →
        max (u.length : ℝ) (u'.length : ℝ) < mu * w.length) :
    RelWord.IsLemma49Input D (RelWord.symmetrized v) eps mu rho where
  toIsLemma44Input :=
    RelWord.isLemma44Input_symmetrized_of D v eps mu rho hsc hqg hpieces
  primePiecesSmall := hprime

end HullSC
end GroupApproximation
