import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateDecision

/-!
# The printed certificate of `prop:mf-upper-bound`: the equivalence and the
arithmetical conclusion

The last of three modules.  It carries the printed forward construction, the
printed converse, the equivalence they prove, and the `Π⁰₂` / `Σ⁰₂`
classification read through the printed hierarchy vocabulary of
`LocalityAndCertificates`.

Printed sentences covered here: `48c460e1177d`, `25c28508ebdd`,
`333f0665e7c4`, `c1ae41d7749b`, `5d1b40a454ea`, `8af7203348c7`,
`1648e5a783fe`, `f9f5d4ca572f`, `dcbeea482d7d`, `1a943b7ac0a4`,
`e23eb42e7dcf`, `10e8f19b4062`, `a3fe9676d8c0`, `986567176317`,
`8b7c6fcc3995`, `ac1c2118de5b`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Certificates

open Matrix PresentationCodes AdianRabinWordProblem RawWord MFMicrostate
open ArithmeticalHierarchy

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-- The maximum relator length of a code. -/
def relatorLengthBound (P : PresentationCode) : ℕ :=
  (P.2.map List.length).foldr max 0

theorem length_le_relatorLengthBound (P : PresentationCode)
    {r : List (ℕ × Bool)} (hr : r ∈ P.2) : r.length ≤ relatorLengthBound P :=
  le_foldr_max _ _ (List.mem_map.2 ⟨r, hr, rfl⟩)

open scoped Classical in
/-- A chosen normal-closure derivation for a trivial word, and a placeholder
otherwise.  Only its value on trivial words is used. -/
def chosenExpr (P : PresentationCode) (w : List (ℕ × Bool)) : RawCertificate :=
  if h : WordProblem P w then
    Classical.choose (exists_exprChecks_of_wordProblem P w h)
  else []

theorem exprChecks_chosenExpr (P : PresentationCode) {w : List (ℕ × Bool)}
    (h : WordProblem P w) : ExprChecks P w (chosenExpr P w) := by
  classical
  rw [chosenExpr, dif_pos h]
  exact Classical.choose_spec (exists_exprChecks_of_wordProblem P w h)

/-- `prop:mf-upper-bound`, proof sentences `48c460e1177d`, `25c28508ebdd`,
`333f0665e7c4`, `c1ae41d7749b`, `5d1b40a454ea` and `8af7203348c7`:

"Suppose that `G_P` is MF.  Fix `n`, let `L = max({1,n} ∪ {|r_i|})`, let `F` be
the set of images in `G_P` of all words of length at most `L`, together with
their inverses, and let `ε = 2^{-n}/(4L)`.  Lemma `lem:local-models` gives
`V : F → U(d)` with `V(1) = 1`, defect at most `ε` on `F`, and
`‖V(g) - 1‖ ≥ 1` for `g ∈ F \ {1}`. …  In particular
`‖r_i(U) - 1‖ ≤ 2Lε ≤ 2^{-n}`.  Label a word `w` of length at most `n` by `T`
if `w̄ = 1`, with a normal-closure expression as witness, and by `S` otherwise;
for the latter, `‖w(U) - 1‖ ≥ ‖V(w̄) - 1‖ - 2nε ≥ 1 - 1/2 ≥ 1/4`.  So
`C(P,n,c)` holds for this certificate." -/
theorem exists_certificate_of_isOperatorMF (P : PresentationCode)
    (hMF : IsOperatorMF (Carrier P)) (n : ℕ) :
    ∃ c : PrintedCertificate, PrintedC P n c := by
  classical
  set L : ℕ := max (max 1 n) (relatorLengthBound P)
  have hL1 : 1 ≤ L := le_trans (le_max_left 1 n) (le_max_left _ _)
  have hLn : n ≤ L := le_trans (le_max_right 1 n) (le_max_left _ _)
  have hLrel : ∀ r ∈ P.2, r.length ≤ L := fun r hr =>
    le_trans (length_le_relatorLengthBound P hr) (le_max_right _ _)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  set ε : ℝ := (1 / 2 : ℝ) ^ n / (4 * (L : ℝ)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    positivity
  have hεnonneg : 0 ≤ ε := hεpos.le
  have hscale : 2 * (L : ℝ) * ε = (1 / 2 : ℝ) ^ n / 2 := by
    rw [hεdef]
    field_simp
    ring
  have hhalf0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hhalf1 : (1 / 2 : ℝ) ^ n ≤ 1 := half_pow_le_one n
  set W : List (List (ℕ × Bool)) :=
    rawWordsUpTo P L ++
      P.2.flatMap (fun r => (List.range (r.length + 1)).map (fun i => r.drop i))
    with hWdef
  set Fset : Finset (Carrier P) := (W.map (ev P)).toFinset with hFdef
  have hmemF : ∀ u ∈ W, ev P u ∈ Fset := by
    intro u hu
    rw [hFdef, List.mem_toFinset, List.mem_map]
    exact ⟨u, hu, rfl⟩
  have hshortF : ∀ u : List (ℕ × Bool), u.length ≤ L →
      (∀ p ∈ u, p.1 < genCount P) → ev P u ∈ Fset := by
    intro u hlen hlet
    refine hmemF u ?_
    rw [hWdef]
    exact List.mem_append_left _ ((mem_rawWordsUpTo_iff P L u).2 ⟨hlen, hlet⟩)
  have h1F : (1 : Carrier P) ∈ Fset := by
    have hnil := hshortF [] (by simp) (by simp)
    rwa [ev_nil] at hnil
  have hletterF : ∀ q : ℕ × Bool, ev P [q] ∈ Fset := by
    rintro ⟨j, b⟩
    have hmem := hshortF [(((letterOf P j : Fin (genCount P)) : ℕ), b)]
      (by simpa using hL1)
      (by
        intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        exact (letterOf P j).isLt)
    rwa [ev_letter_mod] at hmem
  obtain ⟨Lm⟩ := exists_localModel_of_isOperatorMF hMF Fset h1F hεpos
  set tlist : List (List (ℕ × Bool) × RawCertificate) :=
    ((shortReducedWords P n).filter fun w => decide (WordProblem P w)).map
      (fun w => (w, chosenExpr P w)) with htdef
  set c : PrintedCertificate := (Fintype.card Lm.carrier, tlist) with hcdef
  have htWords : tWords c
      = (shortReducedWords P n).filter fun w => decide (WordProblem P w) := by
    rw [hcdef, tWords, tEntries, htdef]
    exact map_fst_map_pair (chosenExpr P) _
  have hmem_tWords : ∀ w, w ∈ tWords c ↔
      (w ∈ shortReducedWords P n ∧ WordProblem P w) := by
    intro w
    rw [htWords, List.mem_filter, decide_eq_true_eq]
  have hwf : WellFormed P n c := by
    refine ⟨?_, ?_⟩
    · rw [hcdef, certDim]
      exact Lm.nonempty
    · intro z hz
      rw [hcdef, tEntries, htdef, List.mem_map] at hz
      obtain ⟨w, hw, hzw⟩ := hz
      rw [List.mem_filter, decide_eq_true_eq] at hw
      rw [← hzw]
      exact ⟨(mem_shortReducedWords_iff P n w).1 hw.1,
        exprChecks_chosenExpr P hw.2⟩
  refine ⟨c, hwf, ⟨microstateOfLocalModel Lm, ?_, ?_, ?_⟩⟩
  · rw [hcdef, certDim]
    rfl
  · intro r hr
    have htail : ∀ i : ℕ, ev P (r.drop i) ∈ Fset := by
      intro i
      by_cases hi : i ≤ r.length
      · refine hmemF _ ?_
        rw [hWdef]
        refine List.mem_append_right _ ?_
        rw [List.mem_flatMap]
        exact ⟨r, hr, List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩⟩
      · rw [List.drop_eq_nil_of_le (by omega), ev_nil]
        exact h1F
    have hbound := gap_le Lm hεnonneg h1F hletterF r htail
    have hone : ((localUnitary Lm (ev P r) : Matrix.unitaryGroup Lm.carrier ℂ) :
        Matrix Lm.carrier Lm.carrier ℂ) = 1 := by
      rw [localUnitary_coe,
        show ev P r = 1 from (ev_eq_one_iff P r).2
          (wordProblem_of_mem_relators P hr), Lm.V_one]
    rw [gap, hone] at hbound
    rw [len_microstateOfLocalModel]
    have hrlen : (r.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLrel r hr
    have hstep : 2 * (r.length : ℝ) * ε ≤ 2 * (L : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hεnonneg
    linarith
  · intro w hw
    rw [mem_sWords_iff] at hw
    obtain ⟨hshort, hnotT⟩ := hw
    have hwmem : w ∈ shortReducedWords P n :=
      (mem_shortReducedWords_iff P n w).2 hshort
    have hnontriv : ¬ WordProblem P w := fun hcon =>
      hnotT ((hmem_tWords w).2 ⟨hwmem, hcon⟩)
    have hne : ev P w ≠ 1 := fun hcon => hnontriv ((ev_eq_one_iff P w).1 hcon)
    have hwlen : w.length ≤ L := le_trans hshort.1 hLn
    have htail : ∀ i : ℕ, ev P (w.drop i) ∈ Fset := by
      intro i
      exact hshortF (w.drop i) (le_trans (drop_length_le i w) hwlen)
        (fun p hp => hshort.2.1 p (drop_subset' i w hp))
    have hbound := gap_le Lm hεnonneg h1F hletterF w htail
    rw [gap, localUnitary_coe] at hbound
    have hsep : (1 : ℝ) ≤ ‖Lm.V (ev P w) - 1‖ := by
      refine Lm.separated (ev P w) ?_ hne
      have h0 := htail 0
      rwa [List.drop_zero] at h0
    have htri : ‖Lm.V (ev P w) - 1‖ ≤
        ‖Lm.V (ev P w) -
            ((evalAt Lm w : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ)‖ +
          ‖((evalAt Lm w : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ) - 1‖ := by
      rw [← sub_add_sub_cancel (Lm.V (ev P w))
        ((evalAt Lm w : Matrix.unitaryGroup Lm.carrier ℂ) :
          Matrix Lm.carrier Lm.carrier ℂ) 1]
      exact norm_add_le _ _
    rw [norm_sub_rev] at hbound
    rw [len_microstateOfLocalModel]
    have hwlenR : (w.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hwlen
    have hstep : 2 * (w.length : ℝ) * ε ≤ 2 * (L : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hεnonneg
    linarith

/-! ## The converse direction -/

/-- The identity converting a right quotient to operator-norm distance,
companion to the repository's `opLength_inv_mul`. -/
theorem opLength_mul_inv (Y : FiniteModel) (a b : Matrix.unitaryGroup Y ℂ) :
    opLength Y (a * b⁻¹) = ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ := by
  have hconj : a * b⁻¹ = a * (b⁻¹ * a) * a⁻¹ := by group
  rw [hconj, opLength_conj, opLength_inv_mul]

open scoped Classical in
/-- `prop:mf-upper-bound`, proof sentence `f9f5d4ca572f`, first half: "For each
`g ∈ G_P` fix a reduced word `w_g` representing `g`, with `w_1` the empty
word." -/
def reducedWordOf (P : PresentationCode) (g : Carrier P) : List (ℕ × Bool) :=
  if g = 1 then []
  else (FreeGroup.toWord (wordOf P (Classical.choose (ev_surjective P g)))).map
    fun q => ((q.1 : ℕ), q.2)

/-- `prop:mf-upper-bound`, proof sentence `dcbeea482d7d`: "Then `V_n(1) = 1`."
The representative of the identity is the empty word, whose evaluation is the
identity matrix in every microstate. -/
theorem reducedWordOf_one (P : PresentationCode) :
    reducedWordOf P (1 : Carrier P) = [] := by
  classical
  rw [reducedWordOf, if_pos rfl]

theorem ev_reducedWordOf (P : PresentationCode) (g : Carrier P) :
    ev P (reducedWordOf P g) = g := by
  classical
  by_cases hg : g = 1
  · rw [reducedWordOf, if_pos hg, ev_nil, hg]
  · rw [reducedWordOf, if_neg hg]
    have hspec : ev P (Classical.choose (ev_surjective P g)) = g :=
      Classical.choose_spec (ev_surjective P g)
    have hw : ev P ((FreeGroup.toWord
          (wordOf P (Classical.choose (ev_surjective P g)))).map
        fun q => ((q.1 : ℕ), q.2))
          = ev P (Classical.choose (ev_surjective P g)) := by
      refine congrArg (evHom P) ?_
      rw [wordOf_def, map_letterOf_map_val P (FreeGroup.toWord
        (wordOf P (Classical.choose (ev_surjective P g))))]
      exact FreeGroup.mk_toWord
    rw [hw]
    exact hspec

theorem isReducedRaw_reducedWordOf (P : PresentationCode) (g : Carrier P) :
    IsReducedRaw P (reducedWordOf P g) := by
  classical
  by_cases hg : g = 1
  · rw [reducedWordOf, if_pos hg]
    unfold IsReducedRaw
    simp only [List.map_nil]
    rfl
  · rw [reducedWordOf, if_neg hg]
    unfold IsReducedRaw
    rw [map_letterOf_map_val P (FreeGroup.toWord
      (wordOf P (Classical.choose (ev_surjective P g))))]
    exact FreeGroup.isReduced_toWord.reduce_eq

theorem reducedWordOf_letters (P : PresentationCode) (g : Carrier P) :
    ∀ p ∈ reducedWordOf P g, p.1 < genCount P := by
  classical
  by_cases hg : g = 1
  · rw [reducedWordOf, if_pos hg]
    simp
  · rw [reducedWordOf, if_neg hg]
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, -, hq⟩ := hp
    rw [← hq]
    exact q.1.isLt

theorem not_wordProblem_reducedWordOf (P : PresentationCode) {g : Carrier P}
    (hg : g ≠ 1) : ¬ WordProblem P (reducedWordOf P g) := by
  intro hcon
  refine hg ?_
  rw [← ev_reducedWordOf P g]
  exact (ev_eq_one_iff P _).2 hcon

/-- The reduced representative is a legitimate label-domain element at every
scale at least its length. -/
theorem isShortReduced_reducedWordOf (P : PresentationCode) (g : Carrier P)
    {n : ℕ} (hn : (reducedWordOf P g).length ≤ n) :
    IsShortReduced P n (reducedWordOf P g) :=
  ⟨hn, reducedWordOf_letters P g, isReducedRaw_reducedWordOf P g⟩

/-- The printed word `t = w_g w_h w_{gh}^{-1}`. -/
def tripleWord (P : PresentationCode) (g h : Carrier P) : List (ℕ × Bool) :=
  reducedWordOf P g ++ (reducedWordOf P h ++ invWord (reducedWordOf P (g * h)))

/-- The companion word `w_{g^{-1}h} w_h^{-1} w_g`, which transfers the
separation of `w_{g^{-1}h}` to the pair `(g, h)`. -/
def pairWord (P : PresentationCode) (g h : Carrier P) : List (ℕ × Bool) :=
  reducedWordOf P (g⁻¹ * h) ++ (invWord (reducedWordOf P h) ++ reducedWordOf P g)

theorem wordProblem_tripleWord (P : PresentationCode) (g h : Carrier P) :
    WordProblem P (tripleWord P g h) := by
  refine (ev_eq_one_iff P _).1 ?_
  rw [tripleWord, ev_append, ev_append, ev_invWord, ev_reducedWordOf,
    ev_reducedWordOf, ev_reducedWordOf]
  group

theorem wordProblem_pairWord (P : PresentationCode) (g h : Carrier P) :
    WordProblem P (pairWord P g h) := by
  refine (ev_eq_one_iff P _).1 ?_
  rw [pairWord, ev_append, ev_append, ev_invWord, ev_reducedWordOf,
    ev_reducedWordOf, ev_reducedWordOf]
  group

/-- `prop:mf-upper-bound`, proof sentence `1a943b7ac0a4`: "For `g, h ∈ G_P` the
word `t = w_g w_h w_{gh}^{-1}` is trivial in `G_P`, so it is freely equal to a
product of `A` conjugates of relators and their inverses, for some `A`
depending on `g` and `h` but not on `n`."

The area count `A` is produced once and bounds the displacement of `t` in
*every* microstate in terms of the relator displacement. -/
theorem exists_area_count (P : PresentationCode) (g h : Carrier P) :
    ∃ A : ℕ, ∀ (M : Microstate P) (δ : ℝ), 0 ≤ δ →
      (∀ r ∈ P.2, M.len r ≤ δ) → M.len (tripleWord P g h) ≤ (A : ℝ) * δ := by
  obtain ⟨A, hA⟩ := exists_area_bound P
    (wordOf_mem_normalClosure (wordProblem_tripleWord P g h))
  exact ⟨A, fun M δ hδ hrel => hA M δ hδ (flen_relatorSet_le hrel)⟩

/-- `prop:mf-upper-bound`, proof sentence `1648e5a783fe`: "Conversely, suppose
that for every `n` some certificate `c_n = (d_n, ℓ_n, π_n)` satisfies
`C(P,n,c_n)`, and choose `U^{(n)} ∈ U(d_n)^k` witnessing `Φ(P,n,c_n)`."

What survives of the certificate is the microstate together with the two
printed properties: the relator defect, and the separation of every nontrivial
short reduced word --- the latter because a well-formed certificate cannot
label a nontrivial word `T`. -/
theorem exists_microstate_of_certificate (P : PresentationCode) {n : ℕ}
    {c : PrintedCertificate} (hc : PrintedC P n c) :
    ∃ M : Microstate P, (∀ r ∈ P.2, M.len r ≤ (1 / 2 : ℝ) ^ n) ∧
      ∀ w : List (ℕ × Bool), IsShortReduced P n w → ¬ WordProblem P w →
        (1 / 4 : ℝ) ≤ M.len w := by
  obtain ⟨hwf, M, -, hrel, hsep⟩ := hc
  refine ⟨M, hrel, fun w hshort hntriv => ?_⟩
  exact hsep w (mem_sWords_of_not_wordProblem hwf hshort hntriv)

/-- `prop:mf-upper-bound`, proof sentences `e23eb42e7dcf`, `10e8f19b4062` and
`a3fe9676d8c0`: the estimate
`‖V_n(g)V_n(h) - V_n(gh)‖ = ‖t(U^{(n)}) - 1‖ ≤ A 2^{-n} → 0`, the separation
`‖V_n(g) - 1‖ ≥ 1/4` for `g ≠ 1`, and the conclusion that `G_P` is MF. -/
theorem isOperatorMF_of_forall_certificate (P : PresentationCode)
    (h : ∀ n : ℕ, ∃ c : PrintedCertificate, PrintedC P n c) :
    IsOperatorMF (Carrier P) := by
  classical
  refine (show IsWeakMF (Carrier P) from ⟨1 / 8, by norm_num, ?_⟩).isOperatorMF
  intro Fs ε₀ hε₀
  set δ : ℝ := min ε₀ (1 / 8)
  have hδpos : 0 < δ := lt_min hε₀ (by norm_num)
  set pairs : List (Carrier P × Carrier P) := (Fs ×ˢ Fs).toList with hpairs
  set trivWords : List (List (ℕ × Bool)) :=
    pairs.flatMap fun q => [tripleWord P q.1 q.2, pairWord P q.1 q.2]
    with htw
  have htriv : ∀ u ∈ trivWords, WordProblem P u := by
    intro u hu
    rw [htw, List.mem_flatMap] at hu
    obtain ⟨q, -, hq⟩ := hu
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact wordProblem_tripleWord P q.1 q.2
    · rcases List.mem_cons.1 hq' with rfl | hq''
      · exact wordProblem_pairWord P q.1 q.2
      · simp at hq''
  obtain ⟨N, hN⟩ := exists_area_bound_list P trivWords htriv
  set B : ℕ :=
    (pairs.map fun q => (reducedWordOf P (q.1⁻¹ * q.2)).length).foldr max 0
    with hB
  obtain ⟨n₀, hn₀⟩ := exists_half_pow_mul_le N hδpos
  set n : ℕ := max n₀ B
  have hpowle : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ n₀ :=
    half_pow_antitone (le_max_left _ _)
  have hpownn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hNδ : (N : ℝ) * (1 / 2 : ℝ) ^ n ≤ δ := by
    have hmono : (N : ℝ) * (1 / 2 : ℝ) ^ n ≤ (N : ℝ) * (1 / 2 : ℝ) ^ n₀ :=
      mul_le_mul_of_nonneg_left hpowle (Nat.cast_nonneg N)
    linarith
  have hδε : δ ≤ ε₀ := min_le_left _ _
  have hδ8 : δ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨M, hrelM, hsepM⟩ := exists_microstate_of_certificate P
    (Classical.choose_spec (h n))
  have harea : ∀ u ∈ trivWords, M.len u ≤ (N : ℝ) * (1 / 2 : ℝ) ^ n :=
    hN M ((1 / 2 : ℝ) ^ n) hpownn hrelM
  refine ⟨{
    carrier := M.model
    nonempty := M.card_pos
    map := fun g => ((M.hom (wordOf P (reducedWordOf P g)) :
      Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ)
    isUnitary := fun g => (M.hom (wordOf P (reducedWordOf P g))).2
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg k hk
    have hmemword : tripleWord P g k ∈ trivWords := by
      rw [htw, List.mem_flatMap]
      refine ⟨(g, k), ?_, by simp⟩
      rw [hpairs, Finset.mem_toList, Finset.mem_product]
      exact ⟨hg, hk⟩
    have hval : M.len (tripleWord P g k)
        = opLength M.model ((M.hom (wordOf P (reducedWordOf P g)) *
            M.hom (wordOf P (reducedWordOf P k))) *
          (M.hom (wordOf P (reducedWordOf P (g * k))))⁻¹) := by
      rw [Microstate.len_def]
      congr 1
      simp only [tripleWord, wordOf_append, wordOf_invWord, map_mul, map_inv]
      group
    have hbound := harea _ hmemword
    rw [hval, opLength_mul_inv] at hbound
    have hcoe : ((M.hom (wordOf P (reducedWordOf P g)) *
          M.hom (wordOf P (reducedWordOf P k)) :
            Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ)
        = ((M.hom (wordOf P (reducedWordOf P g)) :
            Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ) *
          ((M.hom (wordOf P (reducedWordOf P k)) :
            Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ) := rfl
    rw [hcoe, norm_sub_rev] at hbound
    linarith
  · intro g hg k hk hne
    have hsne : g⁻¹ * k ≠ 1 := fun hcon => hne (inv_mul_eq_one.mp hcon)
    have hlenB : (reducedWordOf P (g⁻¹ * k)).length ≤ B := by
      rw [hB]
      refine le_foldr_max _ _ (List.mem_map.2 ⟨(g, k), ?_, rfl⟩)
      rw [hpairs, Finset.mem_toList, Finset.mem_product]
      exact ⟨hg, hk⟩
    have hshort : IsShortReduced P n (reducedWordOf P (g⁻¹ * k)) :=
      isShortReduced_reducedWordOf P (g⁻¹ * k)
        (le_trans hlenB (le_max_right _ _))
    have hquarter : (1 / 4 : ℝ) ≤ M.len (reducedWordOf P (g⁻¹ * k)) :=
      hsepM _ hshort (not_wordProblem_reducedWordOf P hsne)
    have hmemword : pairWord P g k ∈ trivWords := by
      rw [htw, List.mem_flatMap]
      refine ⟨(g, k), ?_, by simp⟩
      rw [hpairs, Finset.mem_toList, Finset.mem_product]
      exact ⟨hg, hk⟩
    have hval : M.len (pairWord P g k)
        = opLength M.model (M.hom (wordOf P (reducedWordOf P (g⁻¹ * k))) *
          ((M.hom (wordOf P (reducedWordOf P g)))⁻¹ *
            M.hom (wordOf P (reducedWordOf P k)))⁻¹) := by
      rw [Microstate.len_def]
      congr 1
      simp only [pairWord, wordOf_append, wordOf_invWord, map_mul, map_inv]
      group
    have hbound := harea _ hmemword
    rw [hval, opLength_mul_inv] at hbound
    have hAlen : M.len (reducedWordOf P (g⁻¹ * k))
        = ‖((M.hom (wordOf P (reducedWordOf P (g⁻¹ * k))) :
            Matrix.unitaryGroup M.model ℂ) :
              Matrix M.model M.model ℂ) - 1‖ := by
      rw [Microstate.len_def, opLength]
    have hquot : ‖(((M.hom (wordOf P (reducedWordOf P g)))⁻¹ *
            M.hom (wordOf P (reducedWordOf P k)) :
              Matrix.unitaryGroup M.model ℂ) :
                Matrix M.model M.model ℂ) - 1‖
        = ‖((M.hom (wordOf P (reducedWordOf P k)) :
              Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ) -
            ((M.hom (wordOf P (reducedWordOf P g)) :
              Matrix.unitaryGroup M.model ℂ) :
                Matrix M.model M.model ℂ)‖ := by
      rw [← opLength, opLength_inv_mul]
    have htri : ‖((M.hom (wordOf P (reducedWordOf P (g⁻¹ * k))) :
            Matrix.unitaryGroup M.model ℂ) :
              Matrix M.model M.model ℂ) - 1‖
        ≤ ‖((M.hom (wordOf P (reducedWordOf P (g⁻¹ * k))) :
              Matrix.unitaryGroup M.model ℂ) :
                Matrix M.model M.model ℂ) -
            (((M.hom (wordOf P (reducedWordOf P g)))⁻¹ *
                M.hom (wordOf P (reducedWordOf P k)) :
                  Matrix.unitaryGroup M.model ℂ) :
                    Matrix M.model M.model ℂ)‖ +
          ‖(((M.hom (wordOf P (reducedWordOf P g)))⁻¹ *
                M.hom (wordOf P (reducedWordOf P k)) :
                  Matrix.unitaryGroup M.model ℂ) :
                    Matrix M.model M.model ℂ) - 1‖ := by
      rw [← sub_add_sub_cancel
        (((M.hom (wordOf P (reducedWordOf P (g⁻¹ * k))) :
            Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ))
        ((((M.hom (wordOf P (reducedWordOf P g)))⁻¹ *
            M.hom (wordOf P (reducedWordOf P k)) :
              Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ))
        (1 : Matrix M.model M.model ℂ)]
      exact norm_add_le _ _
    rw [norm_sub_rev]
    rw [hAlen] at hquarter
    rw [hquot] at htri
    linarith

/-! ## The proposition -/

/-- The printed equivalence of `prop:mf-upper-bound`: a code lies in `MF_fp`
if and only if for every `n` there is a certificate at scale `n`. -/
theorem isOperatorMF_iff_forall_exists_printedCertificate
    (P : PresentationCode) :
    IsOperatorMF (Carrier P) ↔
      ∀ n : ℕ, ∃ c : PrintedCertificate, PrintedC P n c :=
  ⟨fun hMF n => exists_certificate_of_isOperatorMF P hMF n,
    isOperatorMF_of_forall_certificate P⟩

/-- Total decoding of a natural number as a certificate. -/
def certificateAt (z : ℕ) : PrintedCertificate :=
  (Encodable.decode (α := PrintedCertificate) z).getD (0, [])

theorem computable_certificateAt : Computable certificateAt :=
  (Primrec.option_getD.comp Primrec.decode
    (Primrec.const ((0, []) : PrintedCertificate))).to_comp

theorem certificateAt_encode (c : PrintedCertificate) :
    certificateAt (Encodable.encode c) = c := by
  rw [certificateAt, Encodable.encodek]
  rfl

/-- `prop:mf-upper-bound`, statement sentence `986567176317`: "There is a
decidable relation `C(P,n,c)` on triples of natural numbers such that a code
`P` lies in `MF_fp` if and only if for every `n` there is `c` with
`C(P,n,c)`." -/
theorem exists_decidable_printed_certificate_relation
    (I : PrintedCertificateInputs) :
    ∃ f : (PresentationCode × ℕ) × PrintedCertificate → Bool, Computable f ∧
      (∀ (P : PresentationCode) (n : ℕ) (c : PrintedCertificate),
        f ((P, n), c) = true ↔ PrintedC P n c) ∧
      ∀ P : PresentationCode,
        P ∈ MFfp ↔ ∀ n : ℕ, ∃ c : PrintedCertificate, PrintedC P n c := by
  obtain ⟨f, hf, hfspec⟩ := decidable_printedC I
  refine ⟨f, hf, hfspec, fun P => ?_⟩
  rw [mem_MFfp_iff]
  exact isOperatorMF_iff_forall_exists_printedCertificate P

/-- `prop:mf-upper-bound`, proof sentence `ac1c2118de5b`, first two clauses:
"The displayed equivalence exhibits `MF_fp` as `{P : ∀ n ∃ c, C(P,n,c)}`, a
`Π⁰₂` set", in the printed normal form of `sec:local`. -/
theorem printedMFfp_printedPi02 (I : PrintedCertificateInputs) :
    PrintedPi02 (fun P : PresentationCode => P ∈ MFfp) := by
  obtain ⟨f, hf, hfspec, hequiv⟩ :=
    exists_decidable_printed_certificate_relation I
  refine ⟨fun w => f (w.1, certificateAt w.2), ?_, ?_⟩
  · exact hf.comp (Computable.pair Computable.fst
      (computable_certificateAt.comp Computable.snd))
  · intro P
    refine Iff.trans (hequiv P) ?_
    constructor
    · intro hall y
      obtain ⟨c, hc⟩ := hall y
      refine ⟨Encodable.encode c, ?_⟩
      show f ((P, y), certificateAt (Encodable.encode c)) = true
      rw [certificateAt_encode]
      exact (hfspec P y c).2 hc
    · intro hall y
      obtain ⟨z, hz⟩ := hall y
      exact ⟨certificateAt z, (hfspec P y (certificateAt z)).1 hz⟩

/-- `prop:mf-upper-bound`, proof sentence `ac1c2118de5b`, third clause: "and
its complement as a `Σ⁰₂` set." -/
theorem printedNONMFfp_printedSigma02 (I : PrintedCertificateInputs) :
    PrintedSigma02 (fun P : PresentationCode => P ∈ NONMFfp) := by
  obtain ⟨R, hR, hMF⟩ := printedMFfp_printedPi02 I
  refine ⟨fun w => !R w, ?_, ?_⟩
  · refine (Computable.cond hR (Computable.const false)
      (Computable.const true)).of_eq ?_
    intro w
    cases R w <;> rfl
  · intro P
    have hcompl : P ∈ NONMFfp ↔ ¬ (P ∈ MFfp) := by
      rw [mem_NONMFfp_iff, mem_MFfp_iff]
    refine Iff.trans hcompl ?_
    constructor
    · intro hnot
      by_contra hcon
      push Not at hcon
      refine hnot ((hMF P).2 fun y => ?_)
      obtain ⟨z, hz⟩ := hcon y
      exact ⟨z, by simpa using hz⟩
    · rintro ⟨y, hy⟩ hmem
      obtain ⟨z, hz⟩ := (hMF P).1 hmem y
      have hzz := hy z
      simp [hz] at hzz

/-- `prop:mf-upper-bound`, statement sentence `8b7c6fcc3995`: "Consequently
`MF_fp ∈ Π⁰₂` and `NONMF_fp ∈ Σ⁰₂`." -/
theorem printedCertificatesUpperBound (I : PrintedCertificateInputs) :
    Pi02 (fun P : PresentationCode => P ∈ MFfp) ∧
      Sigma02 fun P : PresentationCode => P ∈ NONMFfp :=
  ⟨pi02_of_printedPi02 (printedMFfp_printedPi02 I),
    sigma02_of_printedSigma02 (printedNONMFfp_printedSigma02 I)⟩

/-- The same arithmetical conclusion from the repository's independent
rational-witness checker.  That route carries no open leaves, so the conclusion
of `prop:mf-upper-bound` does not depend on the open obligations of the printed
certificate route. -/
theorem printedCertificatesUpperBound_repository :
    Pi02 fun P : PresentationCode => P ∈ MFfp :=
  (pi02_congr (fun P => mem_MFfp_iff P)).2 MFRecognitionPi02.operatorMFCode_pi02


end

end Certificates
end MFRecognition
end Manuscript
end GroupApproximation
