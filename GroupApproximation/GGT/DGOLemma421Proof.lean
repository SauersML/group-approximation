import GroupApproximation.GGT.DGOLemma421Statement
import GroupApproximation.GGT.DGOPolygonCutFamily
import GroupApproximation.GGT.DGOLemma421Components
import GroupApproximation.GGT.DGOIsolatedComponentCut
import GroupApproximation.GGT.DGOAssemblyCuts
import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex
import GroupApproximation.GGT.HullSCRelatorSeparation2RelativeSides

/-!
# DGO Lemma 4.21 from the uniform isolated-component bound

Dahmani--Guirardel--Osin Proposition 4.14 states that, in a weakly relatively
hyperbolic group, the total relative length of distinguished isolated
components in an `n`-gon is bounded by `C(μ,c) n` when all other sides are
`(μ,c)`-quasi-geodesic.  `DGOUniformSumBound` is that conclusion in the
radius-witness form used by `DGOPolygonCut.SumBound`, and
`DGOProposition414Uniform` keeps the source's quantifier order while retaining
the pointwise isolated-component projection used by Lemma 4.21.

The rest of this module proves DGO Lemma 4.21(b) from that uniform bound.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric
open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The conclusion of DGO Proposition 4.14 at fixed parameters.**

This is Definition 4.13 and Proposition 4.14 written with a radius witness.
The distinguished sides are isolated components and every other side is
`(μ,c)`-quasi-geodesic.  One radius function bounds all distinguished spans,
and its total is at most `C n`. -/
def DGOUniformSumBound (D : RelGenSet G Λ) (mu c : ℝ) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (v : G) (word : List (RelLetter G Λ))
      (cut : ℕ → ℕ) (I : Finset ℕ) (lam : ℕ → Λ),
    (∀ a ∈ word, D.IsLetter a) →
    RelLetter.listVal word = 1 →
    IsPolygonCut n word cut →
    (∀ s ∈ I, s < n) →
    (∀ s ∈ I, cut (s + 1) = cut s + 1) →
    (∀ s ∈ I, IsComp (lam s) word (cut s) (cut (s + 1))) →
    (∀ s ∈ I, IsIsolated D.fam (lam s) v word (cut s)) →
    (∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
      cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ)) →
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I,
        (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
          ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ C * n

/-- **Dahmani--Guirardel--Osin Proposition 4.14, with uniformity in `n`.**

The quantifier order is the one printed in Proposition 4.14: after the group,
relative structure, and weak-hyperbolicity hypothesis are fixed, arbitrary
`μ ≥ 1` and `c ≥ 0` determine one positive constant `C(μ,c)` which works for
every `n`-gon. -/
def DGOProposition414Uniform : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    (∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet)) →
      ∀ mu c : ℝ, 1 ≤ mu → 0 ≤ c →
      ∃ C : ℕ, 0 < C ∧
        DGOUniformSumBound D mu c C ∧
        ∀ (n : ℕ) (v : G) (word : List (RelLetter G Λ)),
          IsQuasiGeodesicPolygon D mu c n v word →
          ∀ (lam : Λ) (i k : ℕ), IsComp lam word i k →
            IsIsolated D.fam lam v word i →
              (vertex v word i)⁻¹ * vertex v word k ∈
                D.relBall lam (C * n)

/-! ## The singleton-cut projection used by the earlier counting paragraphs -/

theorem dgoUniformSumBound_of_uniform414
    (h : DGOProposition414Uniform.{u, w}) (D : RelGenSet G Λ)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet))
    (mu c : ℝ) (hmu : 1 ≤ mu) (hc : 0 ≤ c) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D mu c C := by
  obtain ⟨C, hC, hsum, hbound⟩ := h G Λ D hhyp mu c hmu hc
  refine ⟨C, hC, ?_⟩
  exact hsum

/-! ## Model test for the uniform-bound payload -/

/-- The relative structure on the trivial group with one trivial peripheral
member.  Keeping a genuine peripheral index makes the model test non-vacuous. -/
private def trivialUniformRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

/-- In the one-point model every distinguished span is the identity, so the
uniform component bound holds with radius zero for every parameter and polygon. -/
theorem dgoProposition414Uniform_trivialModel (mu c : ℝ)
    (_hmu : 1 ≤ mu) (_hc : 0 ≤ c) :
    ∃ C : ℕ, 0 < C ∧
      DGOUniformSumBound trivialUniformRelGenSet mu c C ∧
      ∀ (n : ℕ) (v : PUnit) (word : List (RelLetter PUnit Unit)),
        IsQuasiGeodesicPolygon trivialUniformRelGenSet mu c n v word →
        ∀ (lam : Unit) (i k : ℕ), IsComp lam word i k →
          IsIsolated trivialUniformRelGenSet.fam lam v word i →
            (vertex v word i)⁻¹ * vertex v word k ∈
              trivialUniformRelGenSet.relBall lam (C * n) := by
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
    refine ⟨fun _ => 0, ?_, by simp⟩
    intro s hs
    have hspan :
        (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) = 1 :=
      Subsingleton.elim _ _
    rw [hspan]
    exact one_mem_relBall trivialUniformRelGenSet (lam s) 0
  · intro n v word hpoly lam i k hcomp hiso
    have hspan : (vertex v word i)⁻¹ * vertex v word k = 1 :=
      Subsingleton.elim _ _
    rw [hspan]
    exact one_mem_relBall trivialUniformRelGenSet lam (1 * n)

/-! ## Counting deep isolated singleton sides -/

/-- **The counting consequence of Proposition 4.14 at an arbitrary cut.**

If the distinguished singleton sides all lie outside the relative ball of
radius `B`, every radius witness supplied by Proposition 4.14 is at least
`B+1`.  Summing gives `(B+1)|I| ≤ Cn`. -/
theorem deepIsolated_card_bound
    {D : RelGenSet G Λ} {mu c : ℝ} {C B n : ℕ}
    (hbound : DGOUniformSumBound D mu c C)
    {v : G} {word : List (RelLetter G Λ)} {cut : ℕ → ℕ}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hclosed : RelLetter.listVal word = 1)
    (hcut : IsPolygonCut n word cut)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (hI : ∀ s ∈ I, s < n)
    (hedge : ∀ s ∈ I, cut (s + 1) = cut s + 1)
    (hcomp : ∀ s ∈ I, IsComp (lam s) word (cut s) (cut (s + 1)))
    (hiso : ∀ s ∈ I, IsIsolated D.fam (lam s) v word (cut s))
    (hquasi : ∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
      cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ))
    (hdeep : ∀ s ∈ I,
      (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
        ∉ D.relBall (lam s) B) :
    (B + 1) * I.card ≤ C * n := by
  obtain ⟨r, hrmem, hrsum⟩ :=
    hbound n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  have hrLarge : ∀ s ∈ I, B + 1 ≤ r s := by
    intro s hs
    by_contra hnot
    have hrle : r s ≤ B := by omega
    have hmono : D.relBall (lam s) (r s) ⊆ D.relBall (lam s) B :=
      relBall_mono_radius D (lam s) hrle
    exact hdeep s hs (hmono (hrmem s hs))
  calc
    (B + 1) * I.card = ∑ _s ∈ I, (B + 1) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ s ∈ I, r s := by
      exact Finset.sum_le_sum fun s hs => hrLarge s hs
    _ ≤ C * n := hrsum

/-- A deep singleton side of an `n`-gon cannot be isolated once its depth
threshold is at least the Proposition 4.14 bound `C n`. -/
theorem not_isolated_singleton_of_uniformBound
    {D : RelGenSet G Λ} {mu c : ℝ} {C n : ℕ}
    (hbound : DGOUniformSumBound D mu c C)
    {v : G} {word : List (RelLetter G Λ)} {cut : ℕ → ℕ}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hclosed : RelLetter.listVal word = 1)
    (hcut : IsPolygonCut n word cut)
    {s : ℕ} (hs : s < n) {lam : Λ}
    (hedge : cut (s + 1) = cut s + 1)
    (hcomp : IsComp lam word (cut s) (cut (s + 1)))
    (hquasi : ∀ t : ℕ, t < n → t ≠ s → ∀ p q : ℕ,
      cut t ≤ p → p ≤ q → q ≤ cut (t + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ))
    (hdeep : (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
      ∉ D.relBall lam (C * n)) :
    ¬ IsIsolated D.fam lam v word (cut s) := by
  intro hiso
  have hcount := deepIsolated_card_bound hbound hlet hclosed hcut
    {s} (fun _ => lam)
    (by simp [hs]) (by simp [hedge]) (by simpa [hedge] using hcomp)
    (by simpa using hiso)
    (by
      intro t ht htn
      exact hquasi t ht (by simpa using htn))
    (by simpa using hdeep)
  simp only [Finset.card_singleton] at hcount
  omega

/-! ## The every-edge specialization -/

/-- **The counting consequence of Proposition 4.14 used in Lemma 4.21.**

Cut a closed word at every letter.  Every non-distinguished side is
`(1,1)`-quasi-geodesic, including a possible identity-labelled edge.  If every
distinguished singleton component lies outside the relative ball of radius
`B`, the radius witnesses supplied by Proposition 4.14 are all larger than
`B`, so `(B+1)|I| ≤ C · length`. -/
theorem deepIsolated_card_bound_everyEdge
    {D : RelGenSet G Λ} {C B : ℕ}
    (hbound : DGOUniformSumBound D 1 1 C)
    {v : G} {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hclosed : RelLetter.listVal word = 1)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (hI : ∀ s ∈ I, s < word.length)
    (hcomp : ∀ s ∈ I, IsComp (lam s) word s (s + 1))
    (hiso : ∀ s ∈ I, IsIsolated D.fam (lam s) v word s)
    (hdeep : ∀ s ∈ I,
      (vertex v word s)⁻¹ * vertex v word (s + 1)
        ∉ D.relBall (lam s) B) :
    (B + 1) * I.card ≤ C * word.length := by
  have hcut : IsPolygonCut word.length word (fun s => s) :=
    ⟨rfl, rfl, fun s => Nat.le_succ s⟩
  apply deepIsolated_card_bound hbound hlet hclosed hcut I lam hI
    (fun _ _ => rfl) hcomp hiso (by
        intro s hs hsI p q hp hpq hq
        have hpqOne : q - p ≤ 1 := by omega
        have hnonneg : (0 : ℝ) ≤
            ((wordDist D.alphabet.carrier
              (vertex v word p) (vertex v word q) : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        have hpqReal : ((q - p : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast hpqOne
        norm_num only [div_one]
        linarith) hdeep

/-! ## The minimal connected-pair cut -/

omit [Group G] in
/-- An internal singleton component remains maximal after cutting the segment
and appending one closing peripheral edge.  At the far boundary, the closing
family index is required to differ from the internal component's index. -/
theorem isComp_cutWord_of_singleton
    {word : List (RelLetter G Λ)} {lam closeLam : Λ}
    {start m i : ℕ} {z : G}
    (hm : start + m ≤ word.length)
    (hcomp : IsComp lam word i (i + 1))
    (hstart : start ≤ i) (hend : i + 1 ≤ start + m)
    (hboundary : i + 1 = start + m → closeLam ≠ lam) :
    IsComp lam (cutWord word closeLam start m z)
      (i - start) (i - start + 1) := by
  have hlen : (cutWord word closeLam start m z).length = m + 1 :=
    length_cutWord word closeLam start m z hm
  have hpos : start + (i - start) = i := by omega
  have hside : i - start < m := by omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj0 hj1 hj
    have hjEq : j = i - start := by omega
    subst j
    rw [getElem_cutWord_lt word closeLam start m z hm (i - start)
      (by omega) (by omega) hside]
    simpa only [hpos] using
      hcomp.2.2.1 i le_rfl (by omega) (by omega)
  · intro j hji hj hc
    have hjm : j < m := by omega
    have hjw : start + j < word.length := by omega
    rw [getElem_cutWord_lt word closeLam start m z hm j hj hjw hjm] at hc
    exact hcomp.2.2.2.1 (start + j) (by omega) hjw hc
  · intro hk hc
    by_cases hendEq : i - start + 1 = m
    · rw [getElem_cutWord_last word closeLam start m z hm
        (i - start + 1) hendEq hk] at hc
      have hne : closeLam ≠ lam := hboundary (by omega)
      exact hne hc
    · have hltm : i - start + 1 < m := by omega
      have hword : start + (i - start + 1) < word.length := by omega
      rw [getElem_cutWord_lt word closeLam start m z hm
        (i - start + 1) hk hword hltm] at hc
      have hidx : start + (i - start + 1) = i + 1 := by omega
      exact hcomp.2.2.2.2 (by omega) (by simpa only [hidx] using hc)

/-- Connectedness between vertices before the closing edge is unchanged by
the cut-cycle coordinate shift. -/
theorem connected_cutWord_iff (H : Λ → Subgroup G) (lam closeLam : Λ)
    (v : G) (word : List (RelLetter G Λ)) {start m : ℕ} (z : G)
    (hm : start + m ≤ word.length) {p q : ℕ}
    (hp : p ≤ m) (hq : q ≤ m) :
    Connected H lam (vertex v word start) (cutWord word closeLam start m z) p q
      ↔ Connected H lam v word (start + p) (start + q) := by
  show (vertex (vertex v word start) (cutWord word closeLam start m z) p)⁻¹ *
      vertex (vertex v word start) (cutWord word closeLam start m z) q ∈ H lam ↔
    (vertex v word (start + p))⁻¹ * vertex v word (start + q) ∈ H lam
  rw [vertex_cutWord v word closeLam start m z hm p hp,
    vertex_cutWord v word closeLam start m z hm q hq]

/-- A component start before the cut's closing edge is an original ordered W
occurrence.  The only remaining start position is the closing edge itself. -/
theorem cutWord_isCompStart_cases
    {D : RelGenSet G Λ} {word : List (RelLetter G Λ)}
    (hW3 : WWord.IsWThree D word) {closeLam : Λ}
    {start m j : ℕ} {z : G} (hm : start + m ≤ word.length)
    {lam : Λ}
    (hj : IsCompStart lam (cutWord word closeLam start m z) j) :
    (j = m ∧ closeLam = lam) ∨
      ∃ t : Fin (peripheralPositions word).card,
      j < m ∧ (peripheralOccurrence word t).pos = start + j ∧
        (peripheralOccurrence word t).label = lam := by
  obtain ⟨k, hcomp⟩ := hj
  have hlen : (cutWord word closeLam start m z).length = m + 1 :=
    length_cutWord word closeLam start m z hm
  have hjCycle : j < (cutWord word closeLam start m z).length :=
    hcomp.1.trans_le hcomp.2.1
  have hjle : j ≤ m := by
    rw [hlen] at hjCycle
    omega
  rcases eq_or_lt_of_le hjle with hjEq | hjlt
  · apply Or.inl
    refine ⟨hjEq, ?_⟩
    have hmCycle : j < (cutWord word closeLam start m z).length := by omega
    have hcompOf :
        ((cutWord word closeLam start m z)[j]'hmCycle).IsCompOf lam :=
      hcomp.2.2.1 j le_rfl hcomp.1 hmCycle
    rw [getElem_cutWord_last word closeLam start m z hm j hjEq hmCycle]
      at hcompOf
    exact hcompOf
  · apply Or.inr
    have hcompOf :
        ((cutWord word closeLam start m z)[j]'hjCycle).IsCompOf lam :=
      hcomp.2.2.1 j le_rfl hcomp.1 hjCycle
    have hword : start + j < word.length := by omega
    rw [getElem_cutWord_lt word closeLam start m z hm j hjCycle hword hjlt]
      at hcompOf
    cases hread : word[start + j]'hword with
    | base x =>
        rw [hread] at hcompOf
        exact False.elim hcompOf
    | comp mu x =>
        rw [hread] at hcompOf
        have hmulam : mu = lam := hcompOf
        have hreadOpt : word[start + j]? = some (RelLetter.comp lam x) := by
          rw [← hmulam]
          simpa [List.getElem?_eq_getElem hword] using hread
        have hstartOriginal : IsCompStart lam word (start + j) :=
          ⟨start + j + 1,
            isComp_singleton_of_isWThree_read hW3 hreadOpt⟩
        obtain ⟨t, hpos, hlabel⟩ :=
          exists_peripheralOccurrence_eq_of_isCompStart hstartOriginal
        exact ⟨t, hjlt, hpos, hlabel⟩

/-! ## Components of one W-word are isolated -/

/-- **The first paragraph of DGO Lemma 4.21.**

For a W-word whose peripheral letters lie outside the radius `50C` balls, no
two distinct components are connected.  If a connected pair existed, choose
one of minimal rank gap.  The components strictly between it are isolated in
the cut cycle closed by one peripheral edge.  Proposition 4.14 bounds their
total depth by `C` times at most twice the rank gap, contradicting (W2). -/
theorem peripheralOccurrence_not_connected_of_uniformBound
    {D : RelGenSet G Λ} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hW1 : WWord.IsWOne word)
    (hW2 : WWord.IsWTwo D (50 * C) word)
    (hW3 : WWord.IsWThree D word) (v : G)
    {a b : Fin (peripheralPositions word).card} (hab : a ≠ b)
    (hlabel : (peripheralOccurrence word b).label =
      (peripheralOccurrence word a).label) :
    ¬ Connected D.fam (peripheralOccurrence word a).label v word
      (peripheralOccurrence word a).pos
      (peripheralOccurrence word b).pos := by
  classical
  intro habConn
  let Pair : ℕ → Prop := fun gap =>
    ∃ s r : Fin (peripheralPositions word).card,
      s < r ∧ r.val - s.val = gap ∧
      (peripheralOccurrence word r).label =
        (peripheralOccurrence word s).label ∧
      Connected D.fam (peripheralOccurrence word s).label v word
        (peripheralOccurrence word s).pos
        (peripheralOccurrence word r).pos
  have hPair : ∃ gap : ℕ, Pair gap := by
    rcases lt_or_gt_of_ne hab with habLt | hbaLt
    · exact ⟨b.val - a.val, a, b, habLt, rfl, hlabel, habConn⟩
    · refine ⟨a.val - b.val, b, a, hbaLt, rfl, hlabel.symm, ?_⟩
      have hsymm := connected_symm habConn
      simpa only [hlabel] using hsymm
  let gap : ℕ := Nat.find hPair
  obtain ⟨s, r, hsr, hgap, hsrLabel, hsrConn⟩ := Nat.find_spec hPair
  have hminimal : ∀ {x y : Fin (peripheralPositions word).card},
      x < y →
      (peripheralOccurrence word y).label =
        (peripheralOccurrence word x).label →
      Connected D.fam (peripheralOccurrence word x).label v word
        (peripheralOccurrence word x).pos
        (peripheralOccurrence word y).pos →
      gap ≤ y.val - x.val := by
    intro x y hxy hxyLabel hxyConn
    exact Nat.find_min' hPair ⟨x, y, hxy, rfl, hxyLabel, hxyConn⟩
  have hgapTwo : 2 ≤ gap := by
    have hgapPos : 0 < gap := by omega
    by_contra hnot
    have hgapOne : gap = 1 := by omega
    have hrVal : r.val = s.val + 1 := by omega
    have hsucc : s.val + 1 < (peripheralPositions word).card := by omega
    let r' : Fin (peripheralPositions word).card := ⟨s.val + 1, hsucc⟩
    have hrr' : r = r' := Fin.ext hrVal
    rw [hrr'] at hsrLabel hsrConn
    exact not_connected_peripheralOccurrence_succ hlet hW1 hW3 v s hsucc
      hsrLabel hsrConn
  let A := peripheralOccurrence word s
  let B := peripheralOccurrence word r
  let start := A.pos + 1
  let width := B.pos - start
  have hABpos : A.pos < B.pos := peripheralOccurrence_pos_lt word hsr
  have hstartB : start ≤ B.pos := by
    dsimp [start]
    omega
  have hwidthEnd : start + width = B.pos := by
    dsimp [width]
    omega
  have hBword : B.pos < word.length :=
    (List.getElem?_eq_some_iff.mp B.read).1
  have hwidthWord : start + width ≤ word.length := by omega
  let z : G := (vertex v word B.pos)⁻¹ * vertex v word start
  have hAcomp : IsComp A.label word A.pos (A.pos + 1) :=
    PeripheralOccurrence.isComp hW3 s
  have hAspan : (vertex v word A.pos)⁻¹ * vertex v word start
      ∈ D.fam A.label := by
    simpa [start] using span_mem_fam_of_isComp D v hlet hAcomp
  have hzFam : z ∈ D.fam A.label := by
    have hzEq : z =
        ((vertex v word A.pos)⁻¹ * vertex v word B.pos)⁻¹ *
          ((vertex v word A.pos)⁻¹ * vertex v word start) := by
      dsimp [z]
      group
    rw [hzEq]
    exact mul_mem (inv_mem hsrConn) hAspan
  let cycle := cutWord word A.label start width z
  have hcycleLen : cycle.length = width + 1 := by
    exact length_cutWord word A.label start width z hwidthWord
  have hcycleLet : ∀ c ∈ cycle, D.IsLetter c := by
    exact letters_cutWord D hlet A.label start width hzFam
  have hcycleClosed : RelLetter.listVal cycle = 1 := by
    have hclosed := listVal_cutWord v word A.label start width
    have hzEq : z =
        (vertex v word (start + width))⁻¹ * vertex v word start := by
      dsimp [z]
      rw [hwidthEnd]
    simpa [cycle, hzEq] using hclosed
  let J : Finset (Fin (peripheralPositions word).card) := Finset.Ioo s r
  let side : Fin (peripheralPositions word).card → ℕ := fun t =>
    (peripheralOccurrence word t).pos - start
  let I : Finset ℕ := J.image side
  have hsideInj : Set.InjOn side (↑J : Set (Fin (peripheralPositions word).card)) := by
    intro x hx y hy hxy
    have hxJ : s < x ∧ x < r := Finset.mem_Ioo.mp hx
    have hyJ : s < y ∧ y < r := Finset.mem_Ioo.mp hy
    have hAx : A.pos < (peripheralOccurrence word x).pos := by
      exact peripheralOccurrence_pos_lt word hxJ.1
    have hAy : A.pos < (peripheralOccurrence word y).pos := by
      exact peripheralOccurrence_pos_lt word hyJ.1
    have hposEq : (peripheralOccurrence word x).pos =
        (peripheralOccurrence word y).pos := by
      dsimp [side, start] at hxy
      omega
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact False.elim ((peripheralOccurrence_pos_lt word hlt).ne hposEq)
    · exact heq
    · exact False.elim ((peripheralOccurrence_pos_lt word hgt).ne hposEq.symm)
  have hcardI : I.card = gap - 1 := by
    calc
      I.card = J.card := Finset.card_image_iff.mpr hsideInj
      _ = gap - 1 := by
        simp only [J, Fin.card_Ioo]
        omega
  have hpack : ∀ q ∈ I, ∃ lam : Λ,
      IsComp lam cycle q (q + 1) ∧
      IsIsolated D.fam lam (vertex v word start) cycle q ∧
      (vertex (vertex v word start) cycle q)⁻¹ *
        vertex (vertex v word start) cycle (q + 1)
          ∉ D.relBall lam (50 * C) := by
    intro q hq
    obtain ⟨t, htJ, htSide⟩ := Finset.mem_image.mp hq
    have htBounds : s < t ∧ t < r := Finset.mem_Ioo.mp htJ
    have hAt : A.pos < (peripheralOccurrence word t).pos :=
      peripheralOccurrence_pos_lt word htBounds.1
    have htB : (peripheralOccurrence word t).pos < B.pos :=
      peripheralOccurrence_pos_lt word htBounds.2
    have hstartT : start ≤ (peripheralOccurrence word t).pos := by
      dsimp [start]
      omega
    have hendT : (peripheralOccurrence word t).pos + 1 ≤ start + width := by
      rw [hwidthEnd]
      omega
    have hsideCoord : start + side t = (peripheralOccurrence word t).pos := by
      dsimp [side]
      omega
    have hsideLt : side t < width := by
      dsimp [side, width, start]
      omega
    have hboundary : (peripheralOccurrence word t).pos + 1 = start + width →
        A.label ≠ (peripheralOccurrence word t).label := by
      intro hnext
      have hBnext : word[(peripheralOccurrence word t).pos + 1]? =
          some (RelLetter.comp B.label B.value) := by
        rw [hnext, hwidthEnd]
        exact B.read
      have hne := hW3.1 (peripheralOccurrence word t).pos
        (peripheralOccurrence word t).label B.label
        (peripheralOccurrence word t).value B.value
        (peripheralOccurrence word t).read hBnext
      intro hEq
      apply hne
      exact hEq.symm.trans hsrLabel.symm
    have htComp : IsComp (peripheralOccurrence word t).label word
        (peripheralOccurrence word t).pos
        ((peripheralOccurrence word t).pos + 1) :=
      PeripheralOccurrence.isComp hW3 t
    have htCycleComp : IsComp (peripheralOccurrence word t).label cycle
        (side t) (side t + 1) := by
      dsimp [cycle]
      exact isComp_cutWord_of_singleton hwidthWord htComp hstartT hendT hboundary
    have htIsolated : IsIsolated D.fam (peripheralOccurrence word t).label
        (vertex v word start) cycle (side t) := by
      refine ⟨⟨side t + 1, htCycleComp⟩, ?_⟩
      intro j hjne hjStart hjConn
      rcases cutWord_isCompStart_cases hW3 hwidthWord hjStart with
        ⟨hjWidth, hcloseLabel⟩ | ⟨u, hjWidth, huPos, huLabel⟩
      · have hjle : j ≤ width := by omega
        have htle : side t ≤ width := by omega
        have hconnOriginal :=
          (connected_cutWord_iff D.fam (peripheralOccurrence word t).label
            A.label v word z hwidthWord htle hjle).mp hjConn
        have hconnTR : Connected D.fam (peripheralOccurrence word t).label v word
            (peripheralOccurrence word t).pos B.pos := by
          simpa only [hsideCoord, hjWidth, hwidthEnd] using hconnOriginal
        have hlabelTR : B.label = (peripheralOccurrence word t).label :=
          hsrLabel.trans hcloseLabel
        have hmin := hminimal htBounds.2 hlabelTR hconnTR
        omega
      · have hjle : j ≤ width := by omega
        have htle : side t ≤ width := by omega
        have hconnOriginal :=
          (connected_cutWord_iff D.fam (peripheralOccurrence word t).label
            A.label v word z hwidthWord htle hjle).mp hjConn
        have hconnTU : Connected D.fam (peripheralOccurrence word t).label v word
            (peripheralOccurrence word t).pos
            (peripheralOccurrence word u).pos := by
          rw [hsideCoord, ← huPos] at hconnOriginal
          exact hconnOriginal
        have hsu : s < u := by
          have hAu : A.pos < (peripheralOccurrence word u).pos := by
            rw [huPos]
            dsimp [start]
            omega
          rcases lt_trichotomy s u with hlt | heq | hgt
          · exact hlt
          · subst u
            exact False.elim (hAu.ne rfl)
          · have hus := peripheralOccurrence_pos_lt word hgt
            have hAu' : (peripheralOccurrence word s).pos <
                (peripheralOccurrence word u).pos := by
              simpa only [A] using hAu
            exact False.elim (Nat.lt_asymm hus hAu')
        have hur : u < r := by
          have huB : (peripheralOccurrence word u).pos < B.pos := by
            rw [huPos, ← hwidthEnd]
            omega
          rcases lt_trichotomy u r with hlt | heq | hgt
          · exact hlt
          · subst u
            exact False.elim (huB.ne rfl)
          · have hru := peripheralOccurrence_pos_lt word hgt
            have huB' : (peripheralOccurrence word u).pos <
                (peripheralOccurrence word r).pos := by
              simpa only [B] using huB
            exact False.elim (Nat.lt_asymm hru huB')
        by_cases hut : u = t
        · subst u
          apply hjne
          dsimp [side]
          rw [huPos]
          omega
        · rcases lt_or_gt_of_ne hut with hutLt | htuLt
          · have hconnUT := connected_symm hconnTU
            have hconnUT' : Connected D.fam (peripheralOccurrence word u).label
                v word (peripheralOccurrence word u).pos
                (peripheralOccurrence word t).pos := by
              rwa [huLabel]
            have hmin := hminimal hutLt huLabel.symm hconnUT'
            omega
          · have hmin := hminimal htuLt huLabel hconnTU
            omega
    have htDeep :
        (vertex (vertex v word start) cycle (side t))⁻¹ *
          vertex (vertex v word start) cycle (side t + 1)
            ∉ D.relBall (peripheralOccurrence word t).label (50 * C) := by
      have hsideSucc : start + (side t + 1) =
          (peripheralOccurrence word t).pos + 1 := by omega
      rw [show cycle = cutWord word A.label start width z from rfl,
        vertex_cutWord v word A.label start width z hwidthWord
          (side t) (by omega),
        vertex_cutWord v word A.label start width z hwidthWord
          (side t + 1) (by omega), hsideCoord, hsideSucc,
        vertex_succ word v (peripheralOccurrence word t).pos
          (List.getElem?_eq_some_iff.mp (peripheralOccurrence word t).read).1,
        inv_mul_cancel_left]
      rw [(List.getElem?_eq_some_iff.mp
        (peripheralOccurrence word t).read).2]
      exact hW2 (peripheralOccurrence word t).pos
        (peripheralOccurrence word t).label
        (peripheralOccurrence word t).value
        (peripheralOccurrence word t).read
    rw [← htSide]
    exact ⟨(peripheralOccurrence word t).label, htCycleComp,
      htIsolated, htDeep⟩
  let lamSide : ℕ → Λ := fun q =>
    if hq : q ∈ I then Classical.choose (hpack q hq) else A.label
  have hlamSpec : ∀ q ∈ I,
      IsComp (lamSide q) cycle q (q + 1) ∧
      IsIsolated D.fam (lamSide q) (vertex v word start) cycle q ∧
      (vertex (vertex v word start) cycle q)⁻¹ *
        vertex (vertex v word start) cycle (q + 1)
          ∉ D.relBall (lamSide q) (50 * C) := by
    intro q hq
    dsimp [lamSide]
    rw [dif_pos hq]
    exact Classical.choose_spec (hpack q hq)
  have hIrange : ∀ q ∈ I, q < cycle.length := by
    intro q hq
    obtain ⟨t, htJ, rfl⟩ := Finset.mem_image.mp hq
    have htBounds : s < t ∧ t < r := Finset.mem_Ioo.mp htJ
    have hAt : A.pos < (peripheralOccurrence word t).pos :=
      peripheralOccurrence_pos_lt word htBounds.1
    have htB : (peripheralOccurrence word t).pos < B.pos :=
      peripheralOccurrence_pos_lt word htBounds.2
    dsimp [side, start]
    rw [hcycleLen]
    dsimp [width]
    omega
  have hcount := deepIsolated_card_bound_everyEdge hbound hcycleLet hcycleClosed
    I lamSide hIrange (fun q hq => (hlamSpec q hq).1)
    (fun q hq => (hlamSpec q hq).2.1)
    (fun q hq => (hlamSpec q hq).2.2)
  have hwalk : ∀ d : ℕ, s.val + d < (peripheralPositions word).card →
      peripheralPos word (s.val + d) ≤ peripheralPos word s.val + 2 * d := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
        have hprev := ih (by omega)
        have hstep := peripheralPos_succ_le_add_two hW1
          (t := s.val + d)
          (by omega : s.val + d + 1 < (peripheralPositions word).card)
        rw [show s.val + (d + 1) = s.val + d + 1 from by omega]
        calc
          peripheralPos word (s.val + d + 1) ≤
              peripheralPos word (s.val + d) + 2 := hstep
          _ ≤ peripheralPos word s.val + 2 * (d + 1) := by omega
  have hspacing := hwalk (r.val - s.val) (by
    convert r.isLt using 1
    omega)
  have hspacing' : peripheralPos word r.val ≤
      peripheralPos word s.val + 2 * (r.val - s.val) := by
    have hidx : s.val + (r.val - s.val) = r.val := by omega
    rw [hidx] at hspacing
    exact hspacing
  have hgapEq : gap = r.val - s.val := by
    dsimp [gap]
    omega
  have hwidthBound : width + 1 ≤ 2 * gap := by
    rw [hgapEq]
    dsimp [width, start, A, B]
    rw [peripheralOccurrence_pos, peripheralOccurrence_pos]
    omega
  rw [hcardI, hcycleLen] at hcount
  have hstrict : C * (width + 1) < (50 * C + 1) * (gap - 1) := by
    have hgapLe : gap ≤ 2 * (gap - 1) := by omega
    have hcoeff : 4 * C < 50 * C + 1 := by omega
    calc
      C * (width + 1) ≤ C * (2 * gap) :=
        Nat.mul_le_mul_left C hwidthBound
      _ = (2 * C) * gap := by ring
      _ ≤ (2 * C) * (2 * (gap - 1)) :=
        Nat.mul_le_mul_left (2 * C) hgapLe
      _ = (4 * C) * (gap - 1) := by ring
      _ < (50 * C + 1) * (gap - 1) :=
        Nat.mul_lt_mul_of_pos_right hcoeff (by omega)
  omega

/-- Every canonical peripheral occurrence of a W-word is an isolated
component of that path. -/
theorem peripheralOccurrence_isIsolated_of_uniformBound
    {D : RelGenSet G Λ} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hW1 : WWord.IsWOne word)
    (hW2 : WWord.IsWTwo D (50 * C) word)
    (hW3 : WWord.IsWThree D word) (v : G)
    (t : Fin (peripheralPositions word).card) :
    IsIsolated D.fam (peripheralOccurrence word t).label v word
      (peripheralOccurrence word t).pos := by
  refine ⟨⟨(peripheralOccurrence word t).pos + 1,
    PeripheralOccurrence.isComp hW3 t⟩, ?_⟩
  intro j hjne hjStart hjConn
  obtain ⟨u, huPos, huLabel⟩ :=
    exists_peripheralOccurrence_eq_of_isCompStart hjStart
  have hut : t ≠ u := by
    intro htu
    subst u
    exact hjne huPos.symm
  have hnot := peripheralOccurrence_not_connected_of_uniformBound
    hC hbound hlet hW1 hW2 hW3 v hut huLabel
  apply hnot
  rwa [huPos]

/-! ## Appending the geodesic closing side -/

omit [Group G] in
/-- A component ending strictly inside the first word stays maximal after an
arbitrary closing word is appended. -/
theorem isComp_append_of_lt_421
    {word tail : List (RelLetter G Λ)} {lam : Λ} {i k : ℕ}
    (hcomp : IsComp lam word i k) (hk : k < word.length) :
    IsComp lam (word ++ tail) i k := by
  obtain ⟨hik, hkw, hrange, hprev, hnext⟩ := hcomp
  refine ⟨hik, by simp; omega, ?_, ?_, ?_⟩
  · intro j hij hjk hjall
    have hjword : j < word.length := by omega
    rw [List.getElem_append_left hjword]
    exact hrange j hij hjk hjword
  · intro j hij hjall
    have hjword : j < word.length := by omega
    rw [List.getElem_append_left hjword]
    exact hprev j hij hjword
  · intro hkall
    rw [List.getElem_append_left hk]
    exact hnext hk

/-- Connectedness between two vertices of the first word is unchanged after a
closing word is appended. -/
theorem connected_append_left_iff_421 (H : Λ → Subgroup G) (lam : Λ)
    (v : G) (word tail : List (RelLetter G Λ)) {i j : ℕ}
    (hi : i ≤ word.length) (hj : j ≤ word.length) :
    Connected H lam v (word ++ tail) i j ↔ Connected H lam v word i j := by
  show (vertex v (word ++ tail) i)⁻¹ * vertex v (word ++ tail) j ∈ H lam ↔
    (vertex v word i)⁻¹ * vertex v word j ∈ H lam
  rw [vertex_append_of_le word tail v i hi,
    vertex_append_of_le word tail v j hj]

/-- A component start lying in the first block of an appended W-word is one of
the original word's canonical peripheral occurrences. -/
theorem append_isCompStart_left_occurrence
    {D : RelGenSet G Λ} {word tail : List (RelLetter G Λ)}
    (hW3 : WWord.IsWThree D word) {lam : Λ} {j : ℕ}
    (hjWord : j < word.length)
    (hj : IsCompStart lam (word ++ tail) j) :
    ∃ t : Fin (peripheralPositions word).card,
      (peripheralOccurrence word t).pos = j ∧
        (peripheralOccurrence word t).label = lam := by
  obtain ⟨k, hcomp⟩ := hj
  have hjAll : j < (word ++ tail).length := by simp; omega
  have hcompOf : ((word ++ tail)[j]'hjAll).IsCompOf lam :=
    hcomp.2.2.1 j le_rfl hcomp.1 hjAll
  rw [List.getElem_append_left hjWord] at hcompOf
  cases hread : word[j]'hjWord with
  | base x =>
      rw [hread] at hcompOf
      exact False.elim hcompOf
  | comp mu x =>
      rw [hread] at hcompOf
      have hmulam : mu = lam := hcompOf
      have hreadOpt : word[j]? = some (RelLetter.comp lam x) := by
        rw [← hmulam]
        simpa [List.getElem?_eq_getElem hjWord] using hread
      have hstartOriginal : IsCompStart lam word j :=
        ⟨j + 1, isComp_singleton_of_isWThree_read hW3 hreadOpt⟩
      exact exists_peripheralOccurrence_eq_of_isCompStart hstartOriginal

/-- The cut with one side containing an entire word. -/
def oneSideCut (word : List (RelLetter G Λ)) : ℕ → ℕ := fun s =>
  if s = 0 then 0 else word.length

omit [Group G] in
/-- `oneSideCut` cuts a word as a one-gon. -/
theorem isPolygonCut_oneSide (word : List (RelLetter G Λ)) :
    IsPolygonCut 1 word (oneSideCut word) := by
  refine ⟨rfl, by simp [oneSideCut], ?_⟩
  intro s
  cases s with
  | zero => simp [oneSideCut]
  | succ s => simp [oneSideCut]

omit [Group G] in
/-- Before the final side, the appended cut agrees with the identity cut on
the first word. -/
theorem appendCut_oneSide_left (word tail : List (RelLetter G Λ))
    {s : ℕ} (hs : s ≤ word.length) :
    appendCut (fun t => t) word.length (oneSideCut tail) s = s := by
  simp [appendCut, hs]

omit [Group G] in
/-- The last corner of the appended cut is the end of the concatenation. -/
theorem appendCut_oneSide_last (word tail : List (RelLetter G Λ)) :
    appendCut (fun t => t) word.length (oneSideCut tail)
      (word.length + 1) = word.length + tail.length := by
  simp [appendCut, oneSideCut]

/-! ## The internal peripheral occurrences -/

/-- Peripheral occurrences whose singleton components end strictly before the
end of the W-word.  These components stay maximal after a closing word is
appended. -/
noncomputable def internalPeripheralOccurrences (word : List (RelLetter G Λ)) :
    Finset (Fin (peripheralPositions word).card) :=
  Finset.univ.filter fun t =>
    (peripheralOccurrence word t).pos + 1 < word.length

omit [Group G] in
@[simp] theorem mem_internalPeripheralOccurrences
    {word : List (RelLetter G Λ)}
    {t : Fin (peripheralPositions word).card} :
    t ∈ internalPeripheralOccurrences word ↔
      (peripheralOccurrence word t).pos + 1 < word.length := by
  simp [internalPeripheralOccurrences]

omit [Group G] in
/-- At most the final peripheral occurrence is lost by requiring its component
to end strictly inside the word. -/
theorem peripheralCount_le_internal_card_add_one
    (word : List (RelLetter G Λ)) :
    peripheralCount word ≤ (internalPeripheralOccurrences word).card + 1 := by
  classical
  let E : Finset (Fin (peripheralPositions word).card) :=
    Finset.univ.filter fun t =>
      ¬ ((peripheralOccurrence word t).pos + 1 < word.length)
  have hE : E.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' : ¬ ((peripheralOccurrence word a).pos + 1 < word.length) := by
      simpa [E] using ha
    have hb' : ¬ ((peripheralOccurrence word b).pos + 1 < word.length) := by
      simpa [E] using hb
    have haPos : (peripheralOccurrence word a).pos + 1 = word.length := by
      have hlt := (List.getElem?_eq_some_iff.mp
        (peripheralOccurrence word a).read).1
      omega
    have hbPos : (peripheralOccurrence word b).pos + 1 = word.length := by
      have hlt := (List.getElem?_eq_some_iff.mp
        (peripheralOccurrence word b).read).1
      omega
    rcases lt_trichotomy a b with hab | hab | hba
    · have hpos := peripheralOccurrence_pos_lt word hab
      omega
    · exact hab
    · have hpos := peripheralOccurrence_pos_lt word hba
      omega
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (peripheralPositions word).card)))
    (p := fun t => (peripheralOccurrence word t).pos + 1 < word.length)
  have huniv :
      (Finset.univ : Finset (Fin (peripheralPositions word).card)).card =
        peripheralCount word := by
    calc
      (Finset.univ : Finset (Fin (peripheralPositions word).card)).card =
          Fintype.card (Fin (peripheralPositions word).card) :=
        Finset.card_univ
      _ = (peripheralPositions word).card := Fintype.card_fin _
      _ = peripheralCount word := card_peripheralPositions word
  have htotal :
      (Finset.univ.filter fun t : Fin (peripheralPositions word).card =>
        (peripheralOccurrence word t).pos + 1 < word.length).card +
      (Finset.univ.filter fun t : Fin (peripheralPositions word).card =>
        ¬ ((peripheralOccurrence word t).pos + 1 < word.length)).card =
        peripheralCount word :=
    hpartition.trans huniv
  have hEeq :
      (Finset.univ.filter fun t : Fin (peripheralPositions word).card =>
        ¬ ((peripheralOccurrence word t).pos + 1 < word.length)).card = E.card :=
    rfl
  rw [hEeq] at htotal
  change peripheralCount word ≤
    (Finset.univ.filter fun t : Fin (peripheralPositions word).card =>
      (peripheralOccurrence word t).pos + 1 < word.length).card + 1
  omega

omit [Group G] in
/-- Distinct canonical peripheral occurrences have distinct word positions. -/
theorem peripheralOccurrence_pos_injective
    (word : List (RelLetter G Λ)) :
    Function.Injective fun t : Fin (peripheralPositions word).card =>
      (peripheralOccurrence word t).pos := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact False.elim ((peripheralOccurrence_pos_lt word hlt).ne hab)
  · exact heq
  · exact False.elim ((peripheralOccurrence_pos_lt word hgt).ne hab.symm)

omit [Group G] in
/-- A component start has only one peripheral family index. -/
theorem isCompStart_label_unique_421 {lam mu : Λ}
    {word : List (RelLetter G Λ)} {i : ℕ}
    (hlam : IsCompStart lam word i) (hmu : IsCompStart mu word i) :
    lam = mu := by
  by_contra hne
  obtain ⟨k, hk⟩ := hlam
  obtain ⟨m, hm⟩ := hmu
  have hi : i < word.length := hk.1.trans_le hk.2.1
  have hli : (word[i]'hi).IsCompOf lam :=
    hk.2.2.1 i le_rfl hk.1 hi
  have hmi : (word[i]'hi).IsCompOf mu :=
    hm.2.2.1 i le_rfl hm.1 hi
  cases hletter : word[i]'hi with
  | base x =>
      rw [hletter] at hli
      exact hli
  | comp nu x =>
      rw [hletter] at hli hmi
      exact hne (hli.symm.trans hmi)

/-! ## The W-word quasi-geodesic estimate -/

/-- **The counting paragraph of DGO Lemma 4.21(a), for a whole W-word.**

Close the word by a geodesic.  Proposition 4.14 bounds the number of internal
W-components which remain isolated in the resulting polygon.  Every other
internal component connects injectively to a component of the closing
geodesic, because distinct W-components do not connect to each other.  The
alternation estimate from (W1) then gives the printed `(4,1)` bound. -/
theorem wWord_length_le_four_wordDist_add_four_of_uniformBound
    {D : RelGenSet G Λ} [Nonempty Λ] {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hW1 : WWord.IsWOne word)
    (hW2 : WWord.IsWTwo D (50 * C) word)
    (hW3 : WWord.IsWThree D word) (v : G) :
    word.length ≤ 4 * wordDist D.alphabet.carrier v
      (vertex v word word.length) + 4 := by
  classical
  obtain ⟨close, hclose⟩ :=
    existsGeodesicWord D (vertex v word word.length) v
  let cycle := word ++ close
  have hcycleLet : ∀ a ∈ cycle, D.IsLetter a := by
    intro a ha
    rw [show cycle = word ++ close from rfl, List.mem_append] at ha
    exact ha.elim (hlet a) (hclose.1 a)
  have hcycleClosed : RelLetter.listVal cycle = 1 := by
    have hend : v * RelLetter.listVal word = vertex v word word.length := by
      exact (vertex_length v word).symm
    apply mul_left_cancel (a := v)
    rw [show cycle = word ++ close from rfl, listVal_append, mul_one,
      ← mul_assoc, hend, hclose.2.1]
  let cut := appendCut (fun s => s) word.length (oneSideCut close)
  have hcut : IsPolygonCut (word.length + 1) cycle cut := by
    exact isPolygonCut_append (isPolygonCut_id word)
      (isPolygonCut_oneSide close)
  let Internal := internalPeripheralOccurrences word
  let Iso : Finset (Fin (peripheralPositions word).card) :=
    Internal.filter fun t =>
      IsIsolated D.fam (peripheralOccurrence word t).label v cycle
        (peripheralOccurrence word t).pos
  let Noniso : Finset (Fin (peripheralPositions word).card) :=
    Internal.filter fun t =>
      ¬ IsIsolated D.fam (peripheralOccurrence word t).label v cycle
        (peripheralOccurrence word t).pos
  have hpartition : Iso.card + Noniso.card = Internal.card := by
    dsimp [Iso, Noniso]
    exact Finset.card_filter_add_card_filter_not
      (s := Internal)
      (p := fun t => IsIsolated D.fam
        (peripheralOccurrence word t).label v cycle
        (peripheralOccurrence word t).pos)
  let pos : Fin (peripheralPositions word).card → ℕ := fun t =>
    (peripheralOccurrence word t).pos
  let I : Finset ℕ := Iso.image pos
  have hposInj : Function.Injective pos := by
    exact peripheralOccurrence_pos_injective word
  have hcardI : I.card = Iso.card := by
    exact Finset.card_image_iff.mpr hposInj.injOn
  have howner : ∀ s : ℕ, s ∈ I →
      ∃ t ∈ Iso, pos t = s := by
    intro s hs
    simpa [I] using Finset.mem_image.mp hs
  let owner : ∀ s : ℕ, s ∈ I → Fin (peripheralPositions word).card :=
    fun s hs => Classical.choose (howner s hs)
  have hownerMem : ∀ s : ℕ, ∀ hs : s ∈ I, owner s hs ∈ Iso := by
    intro s hs
    exact (Classical.choose_spec (howner s hs)).1
  have hownerPos : ∀ s : ℕ, ∀ hs : s ∈ I, pos (owner s hs) = s := by
    intro s hs
    exact (Classical.choose_spec (howner s hs)).2
  let lamSide : ℕ → Λ := fun s =>
    if hs : s ∈ I then (peripheralOccurrence word (owner s hs)).label
    else Classical.choice inferInstance
  have hIrange : ∀ s ∈ I, s < word.length + 1 := by
    intro s hs
    have hposEq := hownerPos s hs
    have hread := (peripheralOccurrence word (owner s hs)).read
    have hlt := (List.getElem?_eq_some_iff.mp hread).1
    dsimp [pos] at hposEq
    omega
  have hedge : ∀ s ∈ I, cut (s + 1) = cut s + 1 := by
    intro s hs
    have hposEq := hownerPos s hs
    have htIso := hownerMem s hs
    have htInternal : owner s hs ∈ Internal := by
      exact (Finset.mem_filter.mp htIso).1
    have hend :
        (peripheralOccurrence word (owner s hs)).pos + 1 < word.length := by
      simpa [Internal] using htInternal
    dsimp [pos] at hposEq
    rw [show cut = appendCut (fun s => s) word.length (oneSideCut close) from rfl,
      appendCut_oneSide_left word close (by omega),
      appendCut_oneSide_left word close (by omega)]
  have hcomp : ∀ s ∈ I, IsComp (lamSide s) cycle (cut s) (cut (s + 1)) := by
    intro s hs
    have hposEq := hownerPos s hs
    have htIso := hownerMem s hs
    have htInternal : owner s hs ∈ Internal :=
      (Finset.mem_filter.mp htIso).1
    have hend :
        (peripheralOccurrence word (owner s hs)).pos + 1 < word.length := by
      simpa [Internal] using htInternal
    have horiginal := PeripheralOccurrence.isComp hW3 (owner s hs)
    have happended := isComp_append_of_lt_421 (tail := close) horiginal hend
    dsimp [pos] at hposEq
    dsimp [lamSide]
    rw [dif_pos hs, show cycle = word ++ close from rfl]
    have hcutS : cut s = s := by
      rw [show cut = appendCut (fun s => s) word.length (oneSideCut close) from rfl]
      exact appendCut_oneSide_left word close (by omega)
    have hcutSucc : cut (s + 1) = s + 1 := by
      rw [show cut = appendCut (fun s => s) word.length (oneSideCut close) from rfl]
      exact appendCut_oneSide_left word close (by omega)
    rw [hcutS, hcutSucc]
    simpa only [hposEq] using happended
  have hiso : ∀ s ∈ I,
      IsIsolated D.fam (lamSide s) v cycle (cut s) := by
    intro s hs
    have hposEq := hownerPos s hs
    have htIso := hownerMem s hs
    have htIsolation :
        IsIsolated D.fam (peripheralOccurrence word (owner s hs)).label v cycle
          (peripheralOccurrence word (owner s hs)).pos :=
      Finset.mem_filter.mp htIso |>.2
    have htInternal : owner s hs ∈ Internal :=
      (Finset.mem_filter.mp htIso).1
    have hend :
        (peripheralOccurrence word (owner s hs)).pos + 1 < word.length := by
      simpa [Internal] using htInternal
    dsimp [pos] at hposEq
    dsimp [lamSide]
    rw [dif_pos hs]
    have hcutS : cut s = s := by
      rw [show cut = appendCut (fun s => s) word.length (oneSideCut close) from rfl]
      exact appendCut_oneSide_left word close (by omega)
    rw [hcutS]
    simpa only [hposEq] using htIsolation
  have hquasi : ∀ s : ℕ, s < word.length + 1 → s ∉ I → ∀ p q : ℕ,
      cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
      ((q - p : ℕ) : ℝ) / (1 : ℝ) - 1 ≤
        ((wordDist D.alphabet.carrier
          (vertex v cycle p) (vertex v cycle q) : ℕ) : ℝ) := by
    intro s hs hsI p q hp hpq hq
    by_cases hsWord : s < word.length
    · have hcutS : cut s = s := by
        exact appendCut_oneSide_left word close (by omega)
      have hcutSucc : cut (s + 1) = s + 1 := by
        exact appendCut_oneSide_left word close (by omega)
      rw [hcutS] at hp
      rw [hcutSucc] at hq
      have hgap : q - p ≤ 1 := by omega
      have hgapReal : ((q - p : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast hgap
      have hnonneg : (0 : ℝ) ≤
          ((wordDist D.alphabet.carrier
            (vertex v cycle p) (vertex v cycle q) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      norm_num only [div_one]
      linarith
    · have hsLast : s = word.length := by omega
      subst s
      have hcutStart : cut word.length = word.length :=
        appendCut_oneSide_left word close le_rfl
      have hcutEnd : cut (word.length + 1) = word.length + close.length :=
        appendCut_oneSide_last word close
      rw [hcutStart] at hp
      rw [hcutEnd] at hq
      let p' := p - word.length
      let q' := q - word.length
      have hpEq : p = word.length + p' := by
        dsimp [p']
        omega
      have hqEq : q = word.length + q' := by
        dsimp [q']
        omega
      have hpq' : p' ≤ q' := by
        dsimp [p', q']
        omega
      have hq' : q' ≤ close.length := by
        dsimp [q']
        omega
      have hgeo := sub_le_wordDist_vertex D hclose p' q' hpq' hq'
      rw [vertex_length] at hgeo
      have hgapShift : word.length + q' - (word.length + p') = q' - p' := by
        omega
      rw [show cycle = word ++ close from rfl, hpEq, hqEq,
        vertex_append_add word close v p', vertex_append_add word close v q',
        hgapShift]
      norm_num only [div_one]
      have hgeoReal : ((q' - p' : ℕ) : ℝ) ≤
          ((wordDist D.alphabet.carrier
            (vertex (v * RelLetter.listVal word) close p')
            (vertex (v * RelLetter.listVal word) close q') : ℕ) : ℝ) := by
        exact_mod_cast hgeo
      linarith
  have hdeep : ∀ s ∈ I,
      (vertex v cycle (cut s))⁻¹ * vertex v cycle (cut (s + 1))
        ∉ D.relBall (lamSide s) (50 * C) := by
    intro s hs
    have hposEq := hownerPos s hs
    have htIso := hownerMem s hs
    have htInternal : owner s hs ∈ Internal :=
      (Finset.mem_filter.mp htIso).1
    have hend :
        (peripheralOccurrence word (owner s hs)).pos + 1 < word.length := by
      simpa [Internal] using htInternal
    have hread := (peripheralOccurrence word (owner s hs)).read
    have hreadLt := (List.getElem?_eq_some_iff.mp hread).1
    dsimp [pos] at hposEq
    dsimp [lamSide]
    rw [dif_pos hs]
    have hcutS : cut s = s := by
      rw [show cut = appendCut (fun s => s) word.length (oneSideCut close) from rfl]
      exact appendCut_oneSide_left word close (by omega)
    have hcutSucc : cut (s + 1) = s + 1 := by
      rw [show cut = appendCut (fun s => s) word.length (oneSideCut close) from rfl]
      exact appendCut_oneSide_left word close (by omega)
    rw [hcutS, hcutSucc]
    have hdeepOccurrence :
        (vertex v cycle (peripheralOccurrence word (owner s hs)).pos)⁻¹ *
          vertex v cycle ((peripheralOccurrence word (owner s hs)).pos + 1)
            ∉ D.relBall (peripheralOccurrence word (owner s hs)).label
              (50 * C) := by
      rw [show cycle = word ++ close from rfl,
        vertex_append_of_le word close v _ (by omega),
        vertex_append_of_le word close v _ (by omega),
        vertex_succ word v _ hreadLt, inv_mul_cancel_left,
        (List.getElem?_eq_some_iff.mp hread).2]
      exact hW2 _ _ _ hread
    simpa only [hposEq] using hdeepOccurrence
  have hcount := deepIsolated_card_bound hbound hcycleLet hcycleClosed hcut
    I lamSide hIrange hedge hcomp hiso hquasi hdeep
  rw [hcardI] at hcount
  have hscaled : C * (50 * Iso.card) ≤ C * (word.length + 1) := by
    calc
      C * (50 * Iso.card) = (50 * C) * Iso.card := by ring
      _ ≤ (50 * C + 1) * Iso.card :=
        Nat.mul_le_mul_right Iso.card (Nat.le_succ (50 * C))
      _ ≤ C * (word.length + 1) := hcount
  have hIsoBound : 50 * Iso.card ≤ word.length + 1 :=
    Nat.le_of_mul_le_mul_left hscaled hC
  have hother : ∀ t : ↑Noniso, ∃ j : ℕ,
      j ≠ (peripheralOccurrence word t.1).pos ∧
      IsCompStart (peripheralOccurrence word t.1).label cycle j ∧
      Connected D.fam (peripheralOccurrence word t.1).label v cycle
        (peripheralOccurrence word t.1).pos j := by
    intro t
    have htNoniso := Finset.mem_filter.mp t.2
    have htInternal : t.1 ∈ Internal := htNoniso.1
    have htEnd : (peripheralOccurrence word t.1).pos + 1 < word.length := by
      simpa [Internal] using htInternal
    have htStart : IsCompStart (peripheralOccurrence word t.1).label cycle
        (peripheralOccurrence word t.1).pos :=
      ⟨(peripheralOccurrence word t.1).pos + 1,
        isComp_append_of_lt_421 (tail := close)
          (PeripheralOccurrence.isComp hW3 t.1) htEnd⟩
    have hnotAll : ¬ ∀ j : ℕ,
        j ≠ (peripheralOccurrence word t.1).pos →
        IsCompStart (peripheralOccurrence word t.1).label cycle j →
        ¬ Connected D.fam (peripheralOccurrence word t.1).label v cycle
          (peripheralOccurrence word t.1).pos j := by
      intro hall
      exact htNoniso.2 ⟨htStart, hall⟩
    push Not at hnotAll
    exact hnotAll
  let other : ∀ t : ↑Noniso, ℕ := fun t => Classical.choose (hother t)
  have hotherSpec : ∀ t : ↑Noniso,
      other t ≠ (peripheralOccurrence word t.1).pos ∧
      IsCompStart (peripheralOccurrence word t.1).label cycle (other t) ∧
      Connected D.fam (peripheralOccurrence word t.1).label v cycle
        (peripheralOccurrence word t.1).pos (other t) := by
    intro t
    exact Classical.choose_spec (hother t)
  have hotherFar : ∀ t : ↑Noniso, word.length ≤ other t := by
    intro t
    by_contra hlt
    have hjWord : other t < word.length := by omega
    have htPos : (peripheralOccurrence word t.1).pos < word.length :=
      (List.getElem?_eq_some_iff.mp (peripheralOccurrence word t.1).read).1
    obtain ⟨a, haPos, haLabel⟩ :=
      append_isCompStart_left_occurrence hW3 hjWord (hotherSpec t).2.1
    have hta : t.1 ≠ a := by
      intro hEq
      subst a
      exact (hotherSpec t).1 haPos.symm
    have hconnWord : Connected D.fam (peripheralOccurrence word t.1).label v word
        (peripheralOccurrence word t.1).pos
        (peripheralOccurrence word a).pos := by
      have hconn := (connected_append_left_iff_421 D.fam
        (peripheralOccurrence word t.1).label v word close
        (by omega) (by omega)).mp (hotherSpec t).2.2
      rwa [← haPos] at hconn
    exact peripheralOccurrence_not_connected_of_uniformBound hC hbound hlet
      hW1 hW2 hW3 v hta haLabel hconnWord
  have hotherLt : ∀ t : ↑Noniso, other t < cycle.length := by
    intro t
    obtain ⟨k, hk⟩ := (hotherSpec t).2.1
    exact hk.1.trans_le hk.2.1
  let matchFin : ↑Noniso → Fin close.length := fun t =>
    ⟨other t - word.length, by
      have hlt := hotherLt t
      have hfar := hotherFar t
      rw [show cycle = word ++ close from rfl, List.length_append] at hlt
      omega⟩
  have hmatchInj : Function.Injective matchFin := by
    intro a b hab
    have hotherEq : other a = other b := by
      have hval := congrArg Fin.val hab
      dsimp [matchFin] at hval
      have haFar := hotherFar a
      have hbFar := hotherFar b
      omega
    have hlabelEq : (peripheralOccurrence word a.1).label =
        (peripheralOccurrence word b.1).label := by
      exact isCompStart_label_unique_421 (hotherSpec a).2.1
        (by rw [hotherEq]; exact (hotherSpec b).2.1)
    apply Subtype.ext
    by_contra habUnderlying
    have hconnB : Connected D.fam (peripheralOccurrence word a.1).label v cycle
        (peripheralOccurrence word b.1).pos (other a) := by
      rw [hlabelEq, hotherEq]
      exact (hotherSpec b).2.2
    have hconnCycle : Connected D.fam (peripheralOccurrence word a.1).label v cycle
        (peripheralOccurrence word a.1).pos
        (peripheralOccurrence word b.1).pos :=
      connected_trans (hotherSpec a).2.2 (connected_symm hconnB)
    have haPos : (peripheralOccurrence word a.1).pos < word.length :=
      (List.getElem?_eq_some_iff.mp (peripheralOccurrence word a.1).read).1
    have hbPos : (peripheralOccurrence word b.1).pos < word.length :=
      (List.getElem?_eq_some_iff.mp (peripheralOccurrence word b.1).read).1
    have hconnWord := (connected_append_left_iff_421 D.fam
      (peripheralOccurrence word a.1).label v word close
      (by omega) (by omega)).mp hconnCycle
    exact peripheralOccurrence_not_connected_of_uniformBound hC hbound hlet
      hW1 hW2 hW3 v habUnderlying hlabelEq.symm hconnWord
  have hNonisoBound : Noniso.card ≤ close.length := by
    have hcard := Fintype.card_le_of_injective matchFin hmatchInj
    simpa using hcard
  have hperipheral := peripheralCount_le_internal_card_add_one word
  have hlength := length_le_two_mul_peripheralCount_add_one hW1
  have hcloseLength : close.length =
      wordDist D.alphabet.carrier v (vertex v word word.length) := by
    rw [hclose.2.2, wordDist_comm D.alphabet.symmetricGenerating]
  rw [← hpartition] at hperipheral
  rw [hcloseLength] at hNonisoBound
  omega

omit [Group G] in
/-- A bounded segment reads the original word at the shifted position. -/
theorem getElem?_drop_take_of_lt_421 (word : List (RelLetter G Λ))
    {start width t : ℕ} (ht : t < width) :
    ((word.drop start).take width)[t]? = word[start + t]? := by
  simp only [List.getElem?_take, List.getElem?_drop, if_pos ht]

omit [Group G] in
/-- Condition (W1) passes to a contiguous segment. -/
theorem isWOne_drop_take_421 {word : List (RelLetter G Λ)}
    (hW1 : WWord.IsWOne word) (start width : ℕ) :
    WWord.IsWOne ((word.drop start).take width) := by
  intro i x y hx hy
  have hi : i < width := by
    have hlt := (List.getElem?_eq_some_iff.mp hx).1
    simp only [List.length_take, List.length_drop] at hlt
    omega
  have hi1 : i + 1 < width := by
    have hlt := (List.getElem?_eq_some_iff.mp hy).1
    simp only [List.length_take, List.length_drop] at hlt
    omega
  have hx' : word[start + i]? = some (RelLetter.base x) := by
    rw [← getElem?_drop_take_of_lt_421 word hi]
    exact hx
  have hy' : word[(start + i) + 1]? = some (RelLetter.base y) := by
    rw [show (start + i) + 1 = start + (i + 1) from by omega,
      ← getElem?_drop_take_of_lt_421 word hi1]
    exact hy
  exact hW1 (start + i) x y hx' hy'

/-- Condition (W2) passes to a contiguous segment. -/
theorem isWTwo_drop_take_421 {D : RelGenSet G Λ} {R : ℕ}
    {word : List (RelLetter G Λ)} (hW2 : WWord.IsWTwo D R word)
    (start width : ℕ) :
    WWord.IsWTwo D R ((word.drop start).take width) := by
  intro i lam x hx
  have hi : i < width := by
    have hlt := (List.getElem?_eq_some_iff.mp hx).1
    simp only [List.length_take, List.length_drop] at hlt
    omega
  apply hW2 (start + i) lam x
  rw [← getElem?_drop_take_of_lt_421 word hi]
  exact hx

/-- Condition (W3) passes to a contiguous segment. -/
theorem isWThree_drop_take_421 {D : RelGenSet G Λ}
    {word : List (RelLetter G Λ)} (hW3 : WWord.IsWThree D word)
    (start width : ℕ) :
    WWord.IsWThree D ((word.drop start).take width) := by
  constructor
  · intro i lam mu x y hx hy
    have hi : i < width := by
      have hlt := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_take, List.length_drop] at hlt
      omega
    have hi1 : i + 1 < width := by
      have hlt := (List.getElem?_eq_some_iff.mp hy).1
      simp only [List.length_take, List.length_drop] at hlt
      omega
    apply hW3.1 (start + i) lam mu x y
    · rw [← getElem?_drop_take_of_lt_421 word hi]
      exact hx
    · rw [show (start + i) + 1 = start + (i + 1) from by omega,
        ← getElem?_drop_take_of_lt_421 word hi1]
      exact hy
  · intro i lam mu x y z hx hz hy
    have hi : i < width := by
      have hlt := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_take, List.length_drop] at hlt
      omega
    have hi1 : i + 1 < width := by
      have hlt := (List.getElem?_eq_some_iff.mp hz).1
      simp only [List.length_take, List.length_drop] at hlt
      omega
    have hi2 : i + 2 < width := by
      have hlt := (List.getElem?_eq_some_iff.mp hy).1
      simp only [List.length_take, List.length_drop] at hlt
      omega
    apply hW3.2 (start + i) lam mu x y z
    · rw [← getElem?_drop_take_of_lt_421 word hi]
      exact hx
    · rw [show (start + i) + 1 = start + (i + 1) from by omega,
        ← getElem?_drop_take_of_lt_421 word hi1]
      exact hz
    · rw [show (start + i) + 2 = start + (i + 2) from by omega,
        ← getElem?_drop_take_of_lt_421 word hi2]
      exact hy

omit [Group G] in
/-- If there are no peripheral indices, (W1) bounds a word by one letter. -/
theorem length_le_one_of_isEmpty_of_isWOne [IsEmpty Λ]
    {word : List (RelLetter G Λ)} (hW1 : WWord.IsWOne word) :
    word.length ≤ 1 := by
  by_contra hlen
  have hzero : 0 < word.length := by omega
  have hone : 1 < word.length := by omega
  cases hzeroLetter : word[0]'hzero with
  | comp lam x => exact isEmptyElim lam
  | base x =>
      cases honeLetter : word[1]'hone with
      | comp lam y => exact isEmptyElim lam
      | base y =>
          apply hW1 0 x y
          · simpa [List.getElem?_eq_getElem hzero] using hzeroLetter
          · simpa [List.getElem?_eq_getElem hone] using honeLetter

/-- DGO Lemma 4.21(a) follows from the uniform Proposition 4.14 bound. -/
theorem dgoLemma421a_of_uniform414
    (h : DGOProposition414Uniform.{u, w}) : DGOLemma421a.{u, w} := by
  intro G _ Λ D hhyp
  obtain ⟨C, hC, hbound⟩ := dgoUniformSumBound_of_uniform414 h D hhyp 1 1
    le_rfl (by norm_num)
  refine ⟨50 * C, ?_⟩
  intro v word hlet hW1 hW2 hW3 i j hij hj
  let segment := (word.drop i).take (j - i)
  have hsegmentLength : segment.length = j - i := by
    exact length_segment word i (j - i) (by omega)
  cases isEmpty_or_nonempty Λ with
  | inl hEmpty =>
      letI : IsEmpty Λ := hEmpty
      have hwordLength := length_le_one_of_isEmpty_of_isWOne hW1
      have hdistNonneg : 0 ≤ wordDist D.alphabet.carrier
          (vertex v word i) (vertex v word j) := Nat.zero_le _
      omega
  | inr hNonempty =>
      letI : Nonempty Λ := hNonempty
      have hsegmentLet : ∀ a ∈ segment, D.IsLetter a := by
        intro a ha
        exact hlet a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
      have hsegmentW1 : WWord.IsWOne segment :=
        isWOne_drop_take_421 hW1 i (j - i)
      have hsegmentW2 : WWord.IsWTwo D (50 * C) segment :=
        isWTwo_drop_take_421 hW2 i (j - i)
      have hsegmentW3 : WWord.IsWThree D segment :=
        isWThree_drop_take_421 hW3 i (j - i)
      have hwhole := wWord_length_le_four_wordDist_add_four_of_uniformBound
        hC hbound hsegmentLet hsegmentW1 hsegmentW2 hsegmentW3
        (vertex v word i)
      have hend : vertex (vertex v word i) segment segment.length =
          vertex v word j := by
        rw [hsegmentLength]
        calc
          vertex (vertex v word i) segment (j - i) =
              vertex v word (i + (j - i)) := by
            simpa [segment] using
              (vertex_segment word v i (j - i) (j - i) le_rfl)
          _ = vertex v word j := by rw [show i + (j - i) = j by omega]
      rw [hend] at hwhole
      omega

/-! ## One opposite-side match from a deep run -/

/-- A run of more deep singleton components than the two short connector
words can absorb contains a component matched on the opposite long side.
This is the finite-absorption paragraph of Dahmani--Guirardel--Osin's proof of
Lemma 4.21(b), with arbitrary quasi-geodesic constants and arbitrary relative
connector words. -/
theorem exists_opposite_match_of_deep_run_of_uniformBound
    (D : RelGenSet G Λ) (lam : Λ) {mu b : ℝ}
    (hbnd : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k →
          IsIsolated D.fam nu v u i →
            (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (rho : ℕ) (p q r s : List (RelLetter G Λ)),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q *
          RelLetter.listVal r →
        IsQuasiGeodesicPolygon D mu b 4 1
          (p ++ q ++ r ++ revWord s) →
        ∀ (source : Fin (p.length + r.length + 1) → ℕ),
          (∀ i, 0 < source i) →
          (∀ i, source i + 1 < q.length) →
          (∀ i, IsComp lam q (source i) (source i + 1)) →
          Function.Injective source →
          (∀ i, (vertex (1 : G) q (source i))⁻¹ *
              vertex (1 : G) q (source i + 1) ∉ D.relBall lam rho) →
          C * 4 ≤ rho →
          (∀ i i', i' ≤ q.length → i' ≠ source i →
            IsCompStart lam (p ++ q ++ r ++ revWord s)
              (p.length + i') →
            ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
              (p.length + source i) (p.length + i')) →
          ∃ i : Fin (p.length + r.length + 1), ∃ j : ℕ,
            j ≤ s.length ∧
            IsCompStart lam (p ++ q ++ r ++ revWord s)
              (p.length + q.length + r.length + (s.length - j)) ∧
              ∃ h : G, h ∈ D.fam lam ∧
                RelLetter.listVal p * vertex (1 : G) q (source i) * h =
                  vertex (1 : G) s j := by
  obtain ⟨C, hC, hdeepBound⟩ := hbnd
  have hdeepTarget : ∀ (n : ℕ) (rho : ℕ), n ≤ 6 →
      ∀ (p q r s : List (RelLetter G Λ)),
      RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q *
        RelLetter.listVal r →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ (i k : ℕ), 0 < i → IsComp lam q i k → k < q.length →
        C * n ≤ rho →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
        ∃ n' : ℕ, n' ≠ p.length + i ∧
          IsCompStart lam (p ++ q ++ r ++ revWord s) n' ∧
          (n' < p.length ∨
            (∃ i' : ℕ, i' ≤ q.length ∧ n' = p.length + i') ∨
            (∃ m : ℕ, m < r.length ∧
              n' = p.length + q.length + m) ∨
            (∃ j : ℕ, j ≤ s.length ∧
              n' = p.length + q.length + r.length + (s.length - j))) ∧
          ∃ h : G, h ∈ D.fam lam ∧
            RelLetter.listVal p * vertex (1 : G) q i * h =
              vertex (1 : G) (p ++ q ++ r ++ revWord s) n' := by
    intro n rho hn p q r s hclose hpoly i k hi hcomp hk hrho hdeep
    have hbridge := isComp_fourGon_of_isComp_side_of_interior
      p q r s lam hi hk hcomp
    have hiq : i ≤ q.length := le_trans (Nat.le_of_lt hcomp.1) hcomp.2.1
    have hstart : IsCompStart lam (p ++ q ++ r ++ revWord s)
        (p.length + i) := ⟨p.length + k, hbridge⟩
    apply exists_other_component_fourGon_general D lam p q r s hiq hstart
    intro hisolated
    have hspan := hdeepBound n hn 1 (p ++ q ++ r ++ revWord s) hpoly
      lam (p.length + i) (p.length + k) hbridge hisolated
    rw [span_fourGon_side p q r s (by omega) (by omega)] at hspan
    exact hdeep (relBall_mono_radius D lam hrho hspan)
  refine ⟨C, hC, ?_⟩
  intro rho p q r s hclose hpoly source hsource_pos hsource_end
    hsource_comp hsource_inj hsource_deep hrho hnotSame
  have hraw : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) ∧
      ∃ h : G, h ∈ D.fam lam ∧
        RelLetter.listVal p * vertex (1 : G) q (source i) * h =
          vertex (1 : G) (p ++ q ++ r ++ revWord s) n := by
    intro i
    obtain ⟨n, hn, hnstart, hnloc, h, hh, heq⟩ :=
      hdeepTarget 4 rho (by omega) p q r s hclose hpoly
        (source i) (source i + 1) (hsource_pos i) (hsource_comp i)
        (hsource_end i) (by simpa using hrho) (hsource_deep i)
    refine ⟨n, hn, hnstart, hnloc, h, hh, heq⟩
  have htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
      Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) := by
    intro i
    obtain ⟨n, hn, hnstart, hnloc, h, hh, heq⟩ := hraw i
    refine ⟨n, hn, hnstart, ?_, hnloc⟩
    show (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + source i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s) n ∈ D.fam lam
    rw [vertex_fourGon_side p q r s 1 (by
      exact le_trans (Nat.le_of_lt (hsource_comp i).1)
        (hsource_comp i).2.1), ← heq]
    have hcancel :
        (RelLetter.listVal p * vertex (1 : G) q (source i))⁻¹ *
          (RelLetter.listVal p * vertex (1 : G) q (source i) * h) = h := by
      group
    simp only [one_mul]
    rw [hcancel]
    exact hh
  have hpairwise : ∀ i j, i ≠ j →
      ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j) := by
    intro i j hij
    apply hnotSame i (source j)
    · exact le_trans (Nat.le_of_lt (hsource_comp j).1)
        (hsource_comp j).2.1
    · exact fun heq => hij (hsource_inj heq.symm)
    · exact ⟨p.length + source j + 1,
        isComp_fourGon_of_isComp_side_of_interior p q r s lam
          (hsource_pos j) (hsource_end j) (hsource_comp j)⟩
  obtain ⟨i, n, j, hnstart, hnconn, hj, hn⟩ :=
    exists_opposite_component_of_finite_absorption D.fam lam p q r s source
      hpairwise htarget hnotSame
  refine ⟨i, j, hj, ?_, ?_⟩
  · rw [← hn]
    exact hnstart
  exact exists_connector_fourGon D lam p q r s hclose
    (by
      exact le_trans (Nat.le_of_lt (hsource_comp i).1)
        (hsource_comp i).2.1) (hn ▸ hnconn)

/-! ## Per-source targets for the consecutive-run count -/

/-- A deep interior component has a distinct connected target in the
quadrilateral.  The target is either on a short side, on the opposite long
side, or at another start on the same long side.  The pointwise projection in
the uniform Proposition 4.14 payload is used only to exclude isolation. -/
theorem exists_target_of_deep_component_of_uniformBound
    (D : RelGenSet G Λ) (lam : Λ) {mu b : ℝ}
    (hbnd : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k →
          IsIsolated D.fam nu v u i →
            (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ) (rho : ℕ) (p q r s : List (RelLetter G Λ)),
        n ≤ 6 →
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q *
          RelLetter.listVal r →
        IsQuasiGeodesicPolygon D mu b n 1
          (p ++ q ++ r ++ revWord s) →
        ∀ (i k : ℕ), 0 < i → k < q.length → IsComp lam q i k →
          C * n ≤ rho →
          (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉
            D.relBall lam rho →
          ∃ n' : ℕ, n' ≠ p.length + i ∧
            IsCompStart lam (p ++ q ++ r ++ revWord s) n' ∧
            (n' < p.length ∨
              (∃ i' : ℕ, i' ≤ q.length ∧ n' = p.length + i') ∨
              (∃ m : ℕ, m < r.length ∧
                n' = p.length + q.length + m) ∨
              (∃ j : ℕ, j ≤ s.length ∧
                n' = p.length + q.length + r.length + (s.length - j))) ∧
            ∃ h : G, h ∈ D.fam lam ∧
              RelLetter.listVal p * vertex (1 : G) q i * h =
                vertex (1 : G) (p ++ q ++ r ++ revWord s) n' := by
  obtain ⟨C, hC, hdeepBound⟩ := hbnd
  refine ⟨C, hC, ?_⟩
  intro n rho p q r s hn hclose hpoly i k hi hk hcomp hrho hdeep
  have hbridge := isComp_fourGon_of_isComp_side_of_interior
    p q r s lam hi hk hcomp
  have hiq : i ≤ q.length :=
    le_trans (Nat.le_of_lt hcomp.1) hcomp.2.1
  have hstart : IsCompStart lam (p ++ q ++ r ++ revWord s)
      (p.length + i) := ⟨p.length + k, hbridge⟩
  apply exists_other_component_fourGon_general D lam p q r s hiq hstart
  intro hisolated
  have hspan := hdeepBound n hn 1 (p ++ q ++ r ++ revWord s) hpoly
    lam (p.length + i) (p.length + k) hbridge hisolated
  rw [span_fourGon_side p q r s hiq (by omega)] at hspan
  exact hdeep (relBall_mono_radius D lam hrho hspan)

omit [Group G] in
/-! ## The finite consecutive-run extraction -/

/-- If every source in a finite run either has an opposite-side match or is
assigned to one of `M` short-side slots, then `M + 1` consecutive blocks of
length `K` contain one whole block of opposite matches.  Distinct unmatched
sources must have distinct short slots. -/
theorem exists_consecutive_block_of_short_absorption
    {K M : ℕ} (hK : 0 < K)
    (Matched : Fin (K * (M + 1)) → Prop)
    (short : Fin (K * (M + 1)) → Fin M)
    (hclass : ∀ i, Matched i ∨ ∃ z : Fin M, ¬ Matched i ∧ short i = z)
    (hinj : ∀ i j, ¬ Matched i → ¬ Matched j → short i = short j → i = j) :
    ∃ b : Fin (M + 1),
      ∀ j : Fin K,
        Matched ⟨b.val * K + j.val, by
          have hb := b.isLt
          have hj := j.isLt
          omega⟩ := by
  classical
  by_contra hnone
  push Not at hnone
  have hbad : ∀ b : Fin (M + 1),
      ∃ j : Fin K,
        ¬ Matched ⟨b.val * K + j.val, by
          have hb := b.isLt
          have hj := j.isLt
          omega⟩ := by
    intro b
    by_contra hall
    push Not at hall
    exact hnone b hall
  let chosen : Fin (M + 1) → Fin (K * (M + 1)) := fun b =>
    let j := Classical.choose (hbad b)
    ⟨b.val * K + j.val, by
      have hb := b.isLt
      have hj := j.isLt
      omega⟩
  have hchosenBad : ∀ b : Fin (M + 1), ¬ Matched (chosen b) := by
    intro b
    dsimp [chosen]
    exact (Classical.choose_spec (hbad b))
  have hsourceInj : Function.Injective chosen := by
    intro a b hab
    have hv := congrArg Fin.val hab
    have ha := (Classical.choose (hbad a)).isLt
    have hb := (Classical.choose (hbad b)).isLt
    apply Fin.ext
    omega
  let owner : Fin (M + 1) → Fin M := fun b =>
    Classical.choose (hclass (chosen b) |>.resolve_left (hchosenBad b))
  have hownerSpec : ∀ b : Fin (M + 1),
      ¬ Matched (chosen b) ∧ short (chosen b) = owner b := by
    intro b
    dsimp [owner]
    exact Classical.choose_spec
      (hclass (chosen b) |>.resolve_left (hchosenBad b))
  have hownerInj : Function.Injective owner := by
    intro a b hab
    have hshortEq : short (chosen a) = short (chosen b) := by
      rw [hownerSpec a |>.2, hownerSpec b |>.2, hab]
    have hchosenEq := hinj (chosen a) (chosen b)
      (hownerSpec a).1 (hownerSpec b).1 hshortEq
    exact hsourceInj hchosenEq
  have hcard := Fintype.card_le_of_injective owner hownerInj
  simp only [Fintype.card_fin] at hcard
  omega

end OsinComponents
end GGT
end GroupApproximation
