import GroupApproximation.GGT.DGOLemma421MinimalGap

/-!
# The finite minimal-gap argument for DGO component ranks

The geometric interpolation lemma is symmetric in the two paths. Applied in
both directions, it turns any forward matched pair into a pair of matched
successor ranks. The proof chooses the least available source rank and uses
the reverse interpolation to exclude a gap on the target side.
-/

namespace GroupApproximation.GGT.OsinComponents

/-- Two-sided strict-interval interpolation forces matched successors as soon
as any forward match exists. No order of the original matching assignment is
assumed. -/
theorem exists_successor_match_of_rank_interpolation
    {m n : ℕ} (M : Fin m → Fin n → Prop)
    (hP : ∀ {s r t : Fin m} {a b : Fin n}, s < r → r < t → a < b →
      M s a → M t b → ∃ c : Fin n, a < c ∧ c < b ∧ M r c)
    (hQ : ∀ {a c b : Fin n} {s t : Fin m}, a < c → c < b → s < t →
      M s a → M t b → ∃ r : Fin m, s < r ∧ r < t ∧ M r c)
    {s t : Fin m} {a b : Fin n} (hst : s < t) (hab : a < b)
    (hsa : M s a) (htb : M t b) :
    ∃ r : Fin m, ∃ c : Fin n, r.val = s.val + 1 ∧ c.val = a.val + 1 ∧ M r c := by
  classical
  let Pair : ℕ → Prop := fun k => ∃ r : Fin m, ∃ c : Fin n,
    s < r ∧ a < c ∧ r.val = k ∧ M r c
  have hex : ∃ k, Pair k := ⟨t.val, t, b, hst, hab, rfl, htb⟩
  obtain ⟨r, c, hsr, hac, hrmin, hrc⟩ := Nat.find_spec hex
  have hrnext : r.val = s.val + 1 := by
    by_contra hnot
    have hxbound : s.val + 1 < m := by omega
    let x : Fin m := ⟨s.val + 1, hxbound⟩
    have hsx : s < x := by change s.val < s.val + 1; omega
    have hxr : x < r := by change s.val + 1 < r.val; omega
    obtain ⟨y, hay, hyc, hxy⟩ := hP hsx hxr hac hsa hrc
    have hminimal := Nat.find_min' hex (show Pair x.val from ⟨x, y, hsx, hay, rfl, hxy⟩)
    change Nat.find hex ≤ s.val + 1 at hminimal
    omega
  have hcnext : c.val = a.val + 1 := by
    by_contra hnot
    have hybound : a.val + 1 < n := by omega
    let y : Fin n := ⟨a.val + 1, hybound⟩
    have hay : a < y := by change a.val < a.val + 1; omega
    have hyc : y < c := by change a.val + 1 < c.val; omega
    obtain ⟨x, hsx, hxr, _⟩ := hQ hay hyc hsr hsa hrc
    have : s.val < x.val := hsx
    have : x.val < r.val := hxr
    omega
  exact ⟨r, c, hrnext, hcnext, hrc⟩



/-- For a partial bijection of ranks, the matched-successor rule fills the
whole interval between any two forward matches and makes their gaps equal. -/
theorem rank_matches_on_interval_of_successors
    {m n : ℕ} (M : Fin m → Fin n → Prop)
    (hsource : ∀ {r t : Fin m} {c : Fin n}, M r c → M t c → r = t)
    (htarget : ∀ {r : Fin m} {c d : Fin n}, M r c → M r d → c = d)
    (hnext : ∀ {s t : Fin m} {a b : Fin n}, s < t → a < b → M s a → M t b →
      ∃ r : Fin m, ∃ c : Fin n, r.val = s.val + 1 ∧ c.val = a.val + 1 ∧ M r c)
    {s t : Fin m} {a b : Fin n} (hst : s < t) (hab : a < b)
    (hsa : M s a) (htb : M t b) :
    t.val - s.val = b.val - a.val ∧
      ∀ k : ℕ, k ≤ t.val - s.val → ∃ r : Fin m, ∃ c : Fin n,
        r.val = s.val + k ∧ c.val = a.val + k ∧ M r c := by
  let L := min (t.val - s.val) (b.val - a.val)
  have hrun : ∀ k : ℕ, k ≤ L → ∃ r : Fin m, ∃ c : Fin n,
      r.val = s.val + k ∧ c.val = a.val + k ∧ M r c := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨s, a, by omega, by omega, hsa⟩
    | succ k ih =>
      intro hk
      obtain ⟨r, c, hr, hc, hrc⟩ := ih (by omega)
      have hkP : k < t.val - s.val := lt_of_lt_of_le
        (show k < L by omega) (Nat.min_le_left _ _)
      have hkQ : k < b.val - a.val := lt_of_lt_of_le
        (show k < L by omega) (Nat.min_le_right _ _)
      obtain ⟨r', c', hr', hc', hrc'⟩ := hnext
        (show r < t by change r.val < t.val; omega)
        (show c < b by change c.val < b.val; omega) hrc htb
      exact ⟨r', c', by omega, by omega, hrc'⟩
  obtain ⟨r, c, hr, hc, hrc⟩ := hrun L le_rfl
  have hgap : t.val - s.val = b.val - a.val := by
    rcases le_total (t.val - s.val) (b.val - a.val) with hle | hle
    · have hL : L = t.val - s.val := Nat.min_eq_left hle
      have hrt : r = t := by apply Fin.ext; omega
      subst r
      have hcb := htarget hrc htb
      have := congrArg Fin.val hcb
      omega
    · have hL : L = b.val - a.val := Nat.min_eq_right hle
      have hcb : c = b := by apply Fin.ext; omega
      subst c
      have hrt := hsource hrc htb
      have := congrArg Fin.val hrt
      omega
  refine ⟨hgap, ?_⟩
  intro k hk
  apply hrun k
  dsimp [L]
  rw [hgap, Nat.min_self]
  omega

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A forward pair of matches between deep W-words forces a match of the
immediate successor components on both paths. This discharges both geometric
interpolation premises of the finite minimal-gap argument. -/
theorem exists_successor_rank_match_of_uniformBounds
    {D : RelGenSet G Lambda} {C11 C414 : ℕ} (hC11 : 0 < C11)
    (hbound : DGOUniformSumBound D 1 1 C11)
    (hproj : ∀ (n : ℕ) (v : G) (word : List (RelLetter G Lambda)),
      IsQuasiGeodesicPolygon D 4 1 n v word →
      ∀ (nu : Lambda) (i k : ℕ), IsComp nu word i k → IsIsolated D.fam nu v word i →
        (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall nu (C414 * n))
    (hbase : DGO421BaseSymmetric D)
    {P Q : List (RelLetter G Lambda)} {vp vq : G}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW1P : WWord.IsWOne P) (hW1Q : WWord.IsWOne Q)
    (hW2P : WWord.IsWTwo D (max (50 * C11) (C414 * 4)) P)
    (hW2Q : WWord.IsWTwo D (max (50 * C11) (C414 * 4)) Q)
    (hW3P : WWord.IsWThree D P) (hW3Q : WWord.IsWThree D Q)
    (hqgP : ∀ i j : ℕ, i ≤ j → j ≤ P.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vp P i) (vertex vp P j) : ℝ))
    (hqgQ : ∀ i j : ℕ, i ≤ j → j ≤ Q.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q i) (vertex vq Q j) : ℝ))
    {s t : Fin (peripheralPositions P).card}
    {a b : Fin (peripheralPositions Q).card}
    (hst : s < t) (hab : a < b)
    (hlabelA : (peripheralOccurrence Q a).label = (peripheralOccurrence P s).label)
    (hlabelB : (peripheralOccurrence Q b).label = (peripheralOccurrence P t).label)
    (hmatchA : (vertex vp P (peripheralOccurrence P s).pos)⁻¹ *
      vertex vq Q (peripheralOccurrence Q a).pos ∈ D.fam (peripheralOccurrence P s).label)
    (hmatchB : (vertex vp P (peripheralOccurrence P t).pos)⁻¹ *
      vertex vq Q (peripheralOccurrence Q b).pos ∈ D.fam (peripheralOccurrence P t).label) :
    ∃ r : Fin (peripheralPositions P).card, ∃ c : Fin (peripheralPositions Q).card,
      r.val = s.val + 1 ∧ c.val = a.val + 1 ∧
      (peripheralOccurrence Q c).label = (peripheralOccurrence P r).label ∧
      (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q c).pos ∈ D.fam (peripheralOccurrence P r).label := by
  let M : Fin (peripheralPositions P).card → Fin (peripheralPositions Q).card → Prop :=
    fun r c => (peripheralOccurrence Q c).label = (peripheralOccurrence P r).label ∧
      (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q c).pos ∈ D.fam (peripheralOccurrence P r).label
  apply exists_successor_match_of_rank_interpolation M ?_ ?_ hst hab
    ⟨hlabelA, hmatchA⟩ ⟨hlabelB, hmatchB⟩
  · intro s r t a b hsr hrt hab hsa htb
    exact exists_intermediate_rank_match_of_uniformBounds hC11 hbound hproj hbase
      hletP hletQ hW1P hW2P hW3P hW3Q hqgP hqgQ hsr hrt hab hsa.1 htb.1 hsa.2 htb.2
  · intro a c b s t hac hcb hst hsa htb
    have hrevA : (vertex vq Q (peripheralOccurrence Q a).pos)⁻¹ *
        vertex vp P (peripheralOccurrence P s).pos ∈ D.fam (peripheralOccurrence Q a).label := by
      rw [hsa.1]
      simpa only [mul_inv_rev, inv_inv] using
        (D.fam (peripheralOccurrence P s).label).inv_mem hsa.2
    have hrevB : (vertex vq Q (peripheralOccurrence Q b).pos)⁻¹ *
        vertex vp P (peripheralOccurrence P t).pos ∈ D.fam (peripheralOccurrence Q b).label := by
      rw [htb.1]
      simpa only [mul_inv_rev, inv_inv] using
        (D.fam (peripheralOccurrence P t).label).inv_mem htb.2
    obtain ⟨r, hsr, hrt, hlabel, hmatch⟩ :=
      exists_intermediate_rank_match_of_uniformBounds hC11 hbound hproj hbase
        hletQ hletP hW1Q hW2Q hW3Q hW3P hqgQ hqgP hac hcb hst
        hsa.1.symm htb.1.symm hrevA hrevB
    refine ⟨r, hsr, hrt, hlabel.symm, ?_⟩
    rw [hlabel]
    simpa only [mul_inv_rev, inv_inv] using
      (D.fam (peripheralOccurrence Q c).label).inv_mem hmatch

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.exists_successor_match_of_rank_interpolation

#audit_axioms GroupApproximation.GGT.OsinComponents.exists_successor_rank_match_of_uniformBounds

#audit_axioms GroupApproximation.GGT.OsinComponents.rank_matches_on_interval_of_successors
