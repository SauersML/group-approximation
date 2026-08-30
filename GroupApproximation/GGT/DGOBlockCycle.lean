import GroupApproximation.GGT.DGOBlockWord
import GroupApproximation.GGT.DGOAlternatingCycle

/-!
# The two cycles, over a block word

`GGT/DGOAlternatingCycle.lean` runs Dahmani--Guirardel--Osin's Lemma 4.6 over the
two-letter block `base a, comp () h` and gets `n - 1 ≤ |(a h)^n|` on a window
whose length the depth of `h` fixes.  This module is the same argument over the
block `w ++ [comp lam h]` of `GGT/DGOBlockWord.lean`, for an arbitrary
admissible word `w` no letter of which is a `lam`-letter, and over an arbitrary
index set `Λ`.

Nothing in the mathematics changes.  The vertex at the `h`-letter of block `t` is
`(a h)^t · a` with `a = listVal w`, which is the same group element the
two-letter case produces, so `connected_blockWordAppend_iff` is
`connected_altWordAppend_iff` with `a` reinterpreted, and
`conj_inv_eq_conj_of_commute` is reused verbatim.  What changes is the index
arithmetic: positions `2t+1` become `t * (r+1) + r` with `r = w.length`, cycle
lengths `2m+1` and `2n+L` become `m(r+1)+1` and `n(r+1)+L`, and the window
hypothesis `3n ≤ R+1` becomes `n(r+2) ≤ R+1`.

## Why `n (r+2) ≤ R + 1` is the right window

The dichotomy is unchanged: either the cycle `(w h)^n · u` is no longer than `R`,
and then no `h`-letter of it can be isolated, so each is connected to a distinct
component of the geodesic side and `L ≥ n - 1`; or the cycle is longer than `R`,
and then `L > R - n(r+1)`.  For the second branch to give `n - 1` as well one
needs `R - n(r+1) ≥ n - 1`, which is `n(r+2) ≤ R + 1`.  At `r = 1` this is the
`3n ≤ R + 1` of the two-letter case.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Connectedness along the block word -/

/-- **Two `h`-letters of the block word are connected exactly when the power of
`w h` between them lies in `H lam`.**  The two initial vertices are `(a h)^t a`
and `(a h)^s a` with `a = listVal w`, whose ratio is
`a⁻¹ (a h)^{s-t} a = h (a h)^{s-t} h⁻¹`. -/
theorem connected_blockWordAppend_iff (D : RelGenSet G Λ) (lam : Λ)
    {pre : List (RelLetter G Λ)} {h : G} (hh : h ∈ D.fam lam)
    (u : List (RelLetter G Λ)) {n t s : ℕ} (ht : t < n) (hs : s < n)
    (hts : t ≤ s) :
    Connected D.fam lam 1 (blockWord lam pre h n ++ u)
        (t * (pre.length + 1) + pre.length) (s * (pre.length + 1) + pre.length)
      ↔ (RelLetter.listVal pre * h) ^ (s - t) ∈ D.fam lam := by
  have hv1 : vertex (1 : G) (blockWord lam pre h n ++ u)
      (t * (pre.length + 1) + pre.length)
      = (RelLetter.listVal pre * h) ^ t * RelLetter.listVal pre := by
    rw [vertex_blockWordAppend_comp lam pre h 1 u ht, one_mul]
  have hv2 : vertex (1 : G) (blockWord lam pre h n ++ u)
      (s * (pre.length + 1) + pre.length)
      = (RelLetter.listVal pre * h) ^ s * RelLetter.listVal pre := by
    rw [vertex_blockWordAppend_comp lam pre h 1 u hs, one_mul]
  show (vertex (1 : G) (blockWord lam pre h n ++ u)
      (t * (pre.length + 1) + pre.length))⁻¹ *
      vertex (1 : G) (blockWord lam pre h n ++ u)
        (s * (pre.length + 1) + pre.length) ∈ D.fam lam ↔ _
  rw [hv1, hv2]
  have hcancel : ∀ X Y cc : G, (X * cc)⁻¹ * (X * Y * cc) = cc⁻¹ * Y * cc := by
    intro X Y cc
    group
  have hpow : (RelLetter.listVal pre * h) ^ s
      = (RelLetter.listVal pre * h) ^ t * (RelLetter.listVal pre * h) ^ (s - t) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, hcancel]
  have hconj : (RelLetter.listVal pre)⁻¹ * (RelLetter.listVal pre * h) ^ (s - t)
        * RelLetter.listVal pre
      = h * (RelLetter.listVal pre * h) ^ (s - t) * h⁻¹ :=
    conj_inv_eq_conj_of_commute (RelLetter.listVal pre) h _
      ((Commute.refl (RelLetter.listVal pre * h)).pow_left (s - t)).eq
  rw [hconj]
  constructor
  · intro hm
    have haux : ∀ Y : G, h⁻¹ * (h * Y * h⁻¹) * h = Y := by
      intro Y
      group
    have hmem := mul_mem (mul_mem (inv_mem hh) hm) hh
    rwa [haux] at hmem
  · intro hm
    exact mul_mem (mul_mem hh hm) (inv_mem hh)

/-! ## The first cycle: a returning power is a late one -/

/-- **The least returning power puts `h⁻¹` in a ball of radius `m(r+1)+1`.**  The
word `(w h)^m` closed up by the single `H lam`-letter `((a h)^m)⁻¹` is a cycle in
which the first `h`-letter is isolated: another `h`-letter of the block part
would force `(a h)^s ∈ H lam` for some `0 < s < m`, against minimality, and the
closing letter does not start a component, the letter before it being the last
`h`.  `a ∉ H lam` is what makes `m ≥ 2`. -/
theorem inv_mem_relBall_of_minimal_pow_mem_fam_block (D : RelGenSet G Λ)
    (lam : Λ) {pre : List (RelLetter G Λ)} (hpre : ∀ c ∈ pre, D.IsLetter c)
    (hno : ∀ c ∈ pre, ¬ c.IsCompOf lam) (hr : 0 < pre.length)
    (hgH : RelLetter.listVal pre ∉ D.fam lam) {h : G} (hh : h ∈ D.fam lam)
    {m : ℕ} (hmem : (RelLetter.listVal pre * h) ^ m ∈ D.fam lam)
    (hmin : ∀ d : ℕ, 1 ≤ d → d < m →
      (RelLetter.listVal pre * h) ^ d ∉ D.fam lam) (hm1 : 1 ≤ m) :
    h⁻¹ ∈ D.relBall lam (m * (pre.length + 1) + 1) := by
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have hm : m = 1 := by omega
    subst hm
    rw [pow_one] at hmem
    have hin : RelLetter.listVal pre * h * h⁻¹ ∈ D.fam lam :=
      mul_mem hmem (inv_mem hh)
    rw [mul_inv_cancel_right] at hin
    exact hgH hin
  set uu : List (RelLetter G Λ) :=
    [RelLetter.comp lam (((RelLetter.listVal pre * h) ^ m)⁻¹)] with huu
  set c : List (RelLetter G Λ) := blockWord lam pre h m ++ uu with hcdef
  have hlen : c.length = m * (pre.length + 1) + 1 := by
    rw [hcdef, List.length_append, length_blockWord, huu]
    simp
  have hlet : ∀ x ∈ c, D.IsLetter x := by
    intro x hx
    rw [hcdef] at hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact isLetter_of_mem_blockWord D lam hpre hh m x hx'
    · rw [huu] at hx'
      rw [List.eq_of_mem_singleton hx']
      exact inv_mem hmem
  have hcl : RelLetter.listVal c = 1 := by
    rw [hcdef, listVal_append, listVal_blockWord, huu]
    simp [RelLetter.listVal, RelLetter.val]
  have hcomp : IsComp lam c (0 * (pre.length + 1) + pre.length)
      (0 * (pre.length + 1) + pre.length + 1) := by
    rw [hcdef]
    exact isComp_blockWordAppend lam pre h uu hno hr (by omega)
  have hv1 : vertex (1 : G) c (0 * (pre.length + 1) + pre.length)
      = RelLetter.listVal pre := by
    rw [hcdef, vertex_blockWordAppend_comp lam pre h 1 uu (by omega), pow_zero,
      one_mul, one_mul]
  have hv2 : vertex (1 : G) c (0 * (pre.length + 1) + pre.length + 1)
      = RelLetter.listVal pre * h := by
    have hidx : 0 * (pre.length + 1) + pre.length + 1 = 1 * (pre.length + 1) := by
      ring
    rw [hcdef, hidx, vertex_blockWordAppend_block lam pre h 1 uu (by omega),
      pow_one, one_mul]
  have hiso : IsIsolated D.fam lam 1 c (0 * (pre.length + 1) + pre.length) := by
    refine ⟨⟨_, hcomp⟩, ?_⟩
    intro j hj hstart hconn
    have hjlen : j < c.length := by
      obtain ⟨k, hk⟩ := hstart
      have h1 := hk.1
      have h2 := hk.2.1
      omega
    rcases Nat.lt_or_ge j (m * (pre.length + 1)) with hlt | hge
    · rw [hcdef] at hstart
      obtain ⟨t, htm, hjt⟩ :=
        exists_of_isCompStart_lt lam pre h uu hno hlt hstart
      have ht1 : 1 ≤ t := by
        by_contra hc
        have ht0 : t = 0 := by omega
        subst ht0
        exact hj hjt
      have hconn' : Connected D.fam lam 1 (blockWord lam pre h m ++ uu)
          (0 * (pre.length + 1) + pre.length)
          (t * (pre.length + 1) + pre.length) := by
        rw [hcdef] at hconn
        rw [← hjt]
        exact hconn
      have hpow := (connected_blockWordAppend_iff D lam hh uu (n := m) (t := 0)
        (s := t) (by omega) htm (by omega)).mp hconn'
      rw [Nat.sub_zero] at hpow
      exact hmin t ht1 htm hpow
    · have hj2m : j = m * (pre.length + 1) := by omega
      subst hj2m
      rw [hcdef] at hstart
      exact not_isCompStart_boundary lam pre h uu (n := m) (by omega) hstart
  have hball := relBall_inv_of_isolated_of_closed D lam (1 : G) hlet hcl hcomp hiso
  rw [hv1, hv2, hlen] at hball
  have hspan : (RelLetter.listVal pre)⁻¹ * (RelLetter.listVal pre * h) = h := by
    group
  rwa [hspan] at hball

/-- **If `h⁻¹` is far, every returning power is late.** -/
theorem lt_of_pow_mem_fam_block (D : RelGenSet G Λ) (lam : Λ)
    {pre : List (RelLetter G Λ)} (hpre : ∀ c ∈ pre, D.IsLetter c)
    (hno : ∀ c ∈ pre, ¬ c.IsCompOf lam) (hr : 0 < pre.length)
    (hgH : RelLetter.listVal pre ∉ D.fam lam) {h : G} (hh : h ∈ D.fam lam)
    {R : ℕ} (hnb : h⁻¹ ∉ D.relBall lam R) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : (RelLetter.listVal pre * h) ^ d ∈ D.fam lam) :
    R < d * (pre.length + 1) + 1 := by
  classical
  have hex : ∃ m : ℕ, 1 ≤ m ∧ (RelLetter.listVal pre * h) ^ m ∈ D.fam lam :=
    ⟨d, hd1, hd⟩
  have hspec := Nat.find_spec hex
  have hmd : Nat.find hex ≤ d := Nat.find_le ⟨hd1, hd⟩
  have hmin : ∀ k : ℕ, 1 ≤ k → k < Nat.find hex →
      (RelLetter.listVal pre * h) ^ k ∉ D.fam lam := by
    intro k hk1 hk2 hkm
    exact Nat.find_min hex hk2 ⟨hk1, hkm⟩
  have hball := inv_mem_relBall_of_minimal_pow_mem_fam_block D lam hpre hno hr
    hgH hh hspec.2 hmin hspec.1
  by_contra hcon
  have hmono : Nat.find hex * (pre.length + 1) ≤ d * (pre.length + 1) :=
    Nat.mul_le_mul_right _ hmd
  have hle : Nat.find hex * (pre.length + 1) + 1 ≤ R := by omega
  exact hnb (relBall_mono_radius D lam hle hball)

/-! ## The second cycle: `(w h)^n` is long -/

/-- **The block word is long, on the window `h⁻¹` is far enough to cover.** -/
theorem sub_one_le_wordDist_block (D : RelGenSet G Λ) (lam : Λ)
    {pre : List (RelLetter G Λ)} (hpre : ∀ c ∈ pre, D.IsLetter c)
    (hno : ∀ c ∈ pre, ¬ c.IsCompOf lam) (hr : 0 < pre.length)
    (hgH : RelLetter.listVal pre ∉ D.fam lam) {h : G} (hh : h ∈ D.fam lam)
    {R : ℕ} (hnb : h⁻¹ ∉ D.relBall lam R) {n : ℕ}
    (hn : n * (pre.length + 2) ≤ R + 1) :
    n - 1 ≤ wordDist D.alphabet.carrier 1 ((RelLetter.listVal pre * h) ^ n) := by
  set L : ℕ := wordDist D.alphabet.carrier 1 ((RelLetter.listVal pre * h) ^ n)
    with hL
  have hsplit : n * (pre.length + 2) = n * (pre.length + 1) + n := by ring
  rcases Nat.lt_or_ge R (n * (pre.length + 1) + L) with hbig | hle
  · omega
  obtain ⟨l, hl, hllen⟩ :=
    exists_isWord_length_eq D.alphabet.symmetricGenerating
      (((RelLetter.listVal pre * h) ^ n)⁻¹)
  obtain ⟨u, hulet, huval, hulen⟩ := exists_relWord D l hl.letters
  have hlL : l.length = L := by
    rw [hllen, wordNorm_inv D.alphabet.symmetricGenerating, hL, wordDist_one_left]
  have huL : u.length = L := by rw [hulen, hlL]
  have huprod : RelLetter.listVal u = ((RelLetter.listVal pre * h) ^ n)⁻¹ := by
    rw [huval, hl.prod_eq]
  set c : List (RelLetter G Λ) := blockWord lam pre h n ++ u with hcdef
  have hclen : c.length = n * (pre.length + 1) + L := by
    rw [hcdef, List.length_append, length_blockWord, huL]
  have hlet : ∀ x ∈ c, D.IsLetter x := by
    intro x hx
    rw [hcdef] at hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact isLetter_of_mem_blockWord D lam hpre hh n x hx'
    · exact hulet x hx'
  have hcl : RelLetter.listVal c = 1 := by
    rw [hcdef, listVal_append, listVal_blockWord, huprod, mul_inv_cancel]
  have hnotconn : ∀ t s : ℕ, t < n → s < n → t ≠ s →
      ¬ Connected D.fam lam 1 c (t * (pre.length + 1) + pre.length)
          (s * (pre.length + 1) + pre.length) := by
    have hkey : ∀ t s : ℕ, t < n → s < n → t < s →
        ¬ Connected D.fam lam 1 c (t * (pre.length + 1) + pre.length)
            (s * (pre.length + 1) + pre.length) := by
      intro t s ht hs hts hconn
      rw [hcdef] at hconn
      have hpow : (RelLetter.listVal pre * h) ^ (s - t) ∈ D.fam lam :=
        (connected_blockWordAppend_iff D lam hh u (n := n) (t := t) (s := s) ht hs
          (by omega)).mp hconn
      have hlt := lt_of_pow_mem_fam_block D lam hpre hno hr hgH hh hnb
        (d := s - t) (by omega) hpow
      have hmono : (s - t) * (pre.length + 1) ≤ (n - 1) * (pre.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hstep : (n - 1) * (pre.length + 1) + (pre.length + 1)
          = n * (pre.length + 1) := by
        have hn1 : n = (n - 1) + 1 := by omega
        calc (n - 1) * (pre.length + 1) + (pre.length + 1)
            = ((n - 1) + 1) * (pre.length + 1) := by ring
          _ = n * (pre.length + 1) := by rw [← hn1]
      omega
    intro t s ht hs hne hconn
    rcases Nat.lt_or_ge t s with hts | hst
    · exact hkey t s ht hs hts hconn
    · exact hkey s t hs ht (by omega) (connected_symm hconn)
  have hall : ∀ t : ℕ, ∃ j : ℕ, t + 1 < n →
      (n * (pre.length + 1) ≤ j ∧ j < n * (pre.length + 1) + L) ∧
        Connected D.fam lam 1 c (t * (pre.length + 1) + pre.length) j := by
    intro t
    by_cases htn : t + 1 < n
    · have hcomp : IsComp lam c (t * (pre.length + 1) + pre.length)
          (t * (pre.length + 1) + pre.length + 1) := by
        rw [hcdef]
        exact isComp_blockWordAppend lam pre h u hno hr htn
      have hnotiso : ¬ IsIsolated D.fam lam 1 c
          (t * (pre.length + 1) + pre.length) := by
        intro hiso
        have hball := relBall_inv_of_isolated_of_closed D lam (1 : G) hlet hcl
          hcomp hiso
        have hv1 : vertex (1 : G) c (t * (pre.length + 1) + pre.length)
            = (RelLetter.listVal pre * h) ^ t * RelLetter.listVal pre := by
          rw [hcdef, vertex_blockWordAppend_comp lam pre h 1 u (by omega), one_mul]
        have hv2 : vertex (1 : G) c (t * (pre.length + 1) + pre.length + 1)
            = (RelLetter.listVal pre * h) ^ (t + 1) := by
          have hidx : t * (pre.length + 1) + pre.length + 1
              = (t + 1) * (pre.length + 1) := by ring
          rw [hcdef, hidx,
            vertex_blockWordAppend_block lam pre h 1 u (by omega), one_mul]
        have hspan : ((RelLetter.listVal pre * h) ^ t * RelLetter.listVal pre)⁻¹
            * (RelLetter.listVal pre * h) ^ (t + 1) = h := by
          have haux : ∀ Y : G, (Y * RelLetter.listVal pre)⁻¹
              * (Y * (RelLetter.listVal pre * h)) = h := by
            intro Y
            group
          rw [pow_succ]
          exact haux _
        rw [hv1, hv2, hspan, hclen] at hball
        exact hnb (relBall_mono_radius D lam hle hball)
      have hex : ∃ j : ℕ, j ≠ t * (pre.length + 1) + pre.length ∧
          IsCompStart lam c j ∧
          Connected D.fam lam 1 c (t * (pre.length + 1) + pre.length) j := by
        by_contra hno'
        push Not at hno'
        exact hnotiso ⟨⟨_, hcomp⟩, fun j hj hjst => hno' j hj hjst⟩
      obtain ⟨j, hjne, hjstart, hjconn⟩ := hex
      refine ⟨j, fun _ => ⟨⟨?_, ?_⟩, hjconn⟩⟩
      · by_contra hjlt
        rw [hcdef] at hjstart
        obtain ⟨s, hsn, hjs⟩ :=
          exists_of_isCompStart_lt lam pre h u hno (by omega) hjstart
        refine hnotconn t s (by omega) hsn ?_ ?_
        · intro hts
          exact hjne (by rw [hjs, hts])
        · rw [← hjs]
          exact hjconn
      · obtain ⟨kk, hk⟩ := hjstart
        have h1 := hk.1
        have h2 := hk.2.1
        omega
    · exact ⟨0, fun hc => absurd hc htn⟩
  choose F hF using hall
  have hcard : (Finset.range (n - 1)).card
      ≤ (Finset.Ico (n * (pre.length + 1)) (n * (pre.length + 1) + L)).card := by
    refine Finset.card_le_card_of_injOn F ?_ ?_
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio] at ht
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact (hF t (by omega)).1
    · intro t ht t' ht' heq
      simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
      by_contra hne
      refine hnotconn t t' (by omega) (by omega) hne ?_
      have h1 := (hF t (by omega)).2
      have h2 := (hF t' (by omega)).2
      rw [heq] at h1
      exact connected_trans h1 (connected_symm h2)
  rw [Finset.card_range, Nat.card_Ico] at hcard
  omega

end OsinComponents
end GGT
end GroupApproximation
