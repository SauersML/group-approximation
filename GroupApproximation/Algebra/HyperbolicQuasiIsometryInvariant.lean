import GroupApproximation.Algebra.HyperbolicQuasiIsometry
import GroupApproximation.GGT.GeodesicChainThrough
import GroupApproximation.GGT.HullSCConeOffHeavyChordChain

/-!
# Hyperbolicity is a quasi-isometry invariant

`Algebra/HyperbolicQuasiIsometry.lean` leaves
`Hyperbolic.QuasiIsometryInvariant` as the Morse-lemma boundary.  The Morse
lemma is now an unconditional theorem of the repository, at every universe
(`Hyperbolic.morseLemma_univ`), so the boundary can be assembled.

Choose a coarse inverse `g` to a quasi-isometry `f`.  Pulling a target geodesic
chain back along `g` gives a source quasi-geodesic, with constants depending
only on the constants of `f`.  The Morse lemma moves that chain to a source
geodesic.  Source slimness then moves it to one of the other two source sides,
and a first-crossing argument moves that source side back to a target geodesic.
Thus target triangles are uniformly slim; the already proved
slim-triangles-to-four-point implication finishes the proof.
-/

namespace GroupApproximation
namespace Hyperbolic

open GroupApproximation.WordMetric
open GroupApproximation.GGT

universe u v

/-- **Hyperbolicity is invariant under quasi-isometry.**

This discharges `QuasiIsometryInvariant` from the proved Morse lemma.  The
constants are intentionally generous: only their uniformity matters. -/
theorem quasiIsometryInvariant : QuasiIsometryInvariant := by
  intro G H instG instH S T f K C hS hT hqi hsource
  letI : Group G := instG
  letI : Group H := instH
  obtain ⟨delta, hdelta⟩ := hsource

  -- Normalise the multiplicative constant so that it is at least one.
  let k : ℕ := max 1 K
  have hk : K ≤ k := le_max_right 1 K
  have hk1 : 1 ≤ k := le_max_left 1 K
  have hfwd : ∀ a b : G,
      wordDist T (f a) (f b) ≤ k * wordDist S a b + C := by
    intro a b
    exact (hqi.1 a b).1.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right (wordDist S a b) hk) C)
  have hback : ∀ a b : G,
      wordDist S a b ≤ k * wordDist T (f a) (f b) + C := by
    intro a b
    exact (hqi.1 a b).2.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right (wordDist T (f a) (f b)) hk) C)

  -- A chosen coarse inverse.  No algebraic compatibility is required.
  choose g hg using hqi.2

  have hgdist : ∀ a b : H,
      wordDist S (g a) (g b) ≤
        k * wordDist T a b + (2 * k * C + C) := by
    intro a b
    have hab : wordDist T (f (g a)) (f (g b)) ≤ C + wordDist T a b + C := by
      have h1 := wordDist_triangle hT (f (g a)) a (f (g b))
      have h2 := wordDist_triangle hT a b (f (g b))
      have hcomm : wordDist T b (f (g b)) = wordDist T (f (g b)) b :=
        wordDist_comm hT b (f (g b))
      have hb : wordDist T b (f (g b)) ≤ C := by rw [hcomm]; exact hg b
      calc
        wordDist T (f (g a)) (f (g b))
            ≤ wordDist T (f (g a)) a + wordDist T a (f (g b)) := h1
        _ ≤ C + wordDist T a (f (g b)) := Nat.add_le_add_right (hg a) _
        _ ≤ C + (wordDist T a b + wordDist T b (f (g b))) :=
          Nat.add_le_add_left h2 _
        _ ≤ C + (wordDist T a b + C) :=
          Nat.add_le_add_left (Nat.add_le_add_left hb _) _
        _ = C + wordDist T a b + C := by ring
    calc
      wordDist S (g a) (g b) ≤ k * wordDist T (f (g a)) (f (g b)) + C :=
        hback (g a) (g b)
      _ ≤ k * (C + wordDist T a b + C) + C :=
        Nat.add_le_add_right (Nat.mul_le_mul_left k hab) C
      _ = k * wordDist T a b + (2 * k * C + C) := by ring

  -- One additive constant works in both directions for pulled-back chains.
  let B : ℕ := 2 * k * C + C + 3 * C
  have hthreeC : 3 * C ≤ k * B := by
    have hCB : 3 * C ≤ B := by
      dsimp [B]
      omega
    exact hCB.trans (by
      simpa using Nat.mul_le_mul_right B hk1)

  have pullback_quasi : ∀ (n : ℕ) (c : ℕ → H), IsGeodesicChain T c n →
      IsQuasiGeodesic S k B n (fun i => g (c i)) := by
    intro n c hc i hi j hj hij
    have hcij : wordDist T (c i) (c j) = j - i := hc i j hij hj
    constructor
    · calc
        wordDist S (g (c i)) (g (c j))
            ≤ k * wordDist T (c i) (c j) + (2 * k * C + C) := hgdist _ _
        _ ≤ k * (j - i) + B := by rw [hcij]; dsimp [B]; omega
    · have htarget : wordDist T (c i) (c j)
          ≤ k * wordDist S (g (c i)) (g (c j)) + 3 * C := by
        have h1 := wordDist_triangle hT (c i) (f (g (c i))) (c j)
        have h2 := wordDist_triangle hT (f (g (c i))) (f (g (c j))) (c j)
        have hcomm : wordDist T (c i) (f (g (c i))) =
            wordDist T (f (g (c i))) (c i) := wordDist_comm hT _ _
        have hfg := hfwd (g (c i)) (g (c j))
        have hleft : wordDist T (c i) (f (g (c i))) ≤ C := by
          rw [hcomm]
          exact hg (c i)
        have hright : wordDist T (f (g (c j))) (c j) ≤ C := hg (c j)
        calc
          wordDist T (c i) (c j)
              ≤ wordDist T (c i) (f (g (c i))) +
                  wordDist T (f (g (c i))) (c j) := h1
          _ ≤ wordDist T (c i) (f (g (c i))) +
                (wordDist T (f (g (c i))) (f (g (c j))) +
                  wordDist T (f (g (c j))) (c j)) :=
            Nat.add_le_add_left h2 _
          _ ≤ C + ((k * wordDist S (g (c i)) (g (c j)) + C) + C) :=
            Nat.add_le_add hleft (Nat.add_le_add hfg hright)
          _ = k * wordDist S (g (c i)) (g (c j)) + 3 * C := by ring
      rw [hcij] at htarget
      calc
        j - i ≤ k * wordDist S (g (c i)) (g (c j)) + 3 * C := htarget
        _ ≤ k * (wordDist S (g (c i)) (g (c j)) + B) := by
          rw [Nat.mul_add]
          exact Nat.add_le_add_left hthreeC _

  obtain ⟨R, hRall⟩ := morseLemma_univ k B delta
  have hMorse : ∀ (n : ℕ) (p : ℕ → G), IsQuasiGeodesic S k B n p →
      ∀ i ≤ n, ∃ q : G, IsBetween S (p 0) q (p n) ∧
        wordDist S (p i) q ≤ R :=
    hRall G instG S hS hdelta
  have hslimS : IsSlimTriangles S (4 * delta) :=
    isSlimTriangles_of_isFourPointHyperbolic hS hdelta

  -- A source chord with coarse-inverse endpoints lies uniformly near a target
  -- chord.  The first-crossing argument is the discrete inverse-Morse step.
  let M : ℕ := k * (k + B + 2 * R + 2 * delta) + 2 * C
  have source_between_to_target : ∀ {x z : H} {r : G},
      IsBetween S (g x) r (g z) →
        ∃ s : H, IsBetween T x s z ∧ wordDist T (f r) s ≤ M := by
    intro x z r hr
    obtain ⟨c, hc0, hcn, hc⟩ := exists_isGeodesicChain hT x z
    let n : ℕ := wordDist T x z
    have hcqg : IsQuasiGeodesic S k B n (fun i => g (c i)) :=
      pullback_quasi n c hc
    have hproject : ∀ i ≤ n, ∃ q : G,
        IsBetween S (g x) q (g z) ∧ wordDist S (g (c i)) q ≤ R := by
      intro i hi
      obtain ⟨q, hq, hd⟩ := hMorse n (fun j => g (c j)) hcqg i hi
      rw [hc0, hcn] at hq
      exact ⟨q, hq, hd⟩
    let a : ℕ := wordDist S (g x) r
    by_cases haR : a ≤ R
    · refine ⟨x, isBetween_left T x z, ?_⟩
      have hfrgx := hfwd r (g x)
      have hcommS : wordDist S r (g x) = wordDist S (g x) r :=
        wordDist_comm hS r (g x)
      have hcommT : wordDist T (f r) x ≤ wordDist T (f r) (f (g x)) + C := by
        have htri := wordDist_triangle hT (f r) (f (g x)) x
        exact htri.trans (Nat.add_le_add_left (hg x) _)
      dsimp [a] at haR
      rw [hcommS] at hfrgx
      have hfrx : wordDist T (f r) x ≤ k * R + 2 * C := by
        calc
          wordDist T (f r) x ≤ wordDist T (f r) (f (g x)) + C := hcommT
          _ ≤ (k * wordDist S (g x) r + C) + C :=
            Nat.add_le_add_right hfrgx C
          _ ≤ (k * R + C) + C :=
            Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.mul_le_mul_left k haR) C) C
          _ = k * R + 2 * C := by ring
      have hRinner : R ≤ k + B + 2 * R + 2 * delta := by omega
      calc
        wordDist T (f r) x ≤ k * R + 2 * C := hfrx
        _ ≤ k * (k + B + 2 * R + 2 * delta) + 2 * C :=
          Nat.add_le_add_right (Nat.mul_le_mul_left k hRinner) (2 * C)
        _ = M := by rfl
    · have hex : ∃ i : ℕ, i ≤ n ∧ a ≤ wordDist S (g x) (g (c i)) := by
        refine ⟨n, le_rfl, ?_⟩
        rw [hcn]
        have hr' : wordDist S (g x) r + wordDist S r (g z) =
            wordDist S (g x) (g z) := hr
        dsimp [a]
        omega
      let i : ℕ := Nat.find hex
      have hi : i ≤ n ∧ a ≤ wordDist S (g x) (g (c i)) := by
        dsimp [i]
        exact Nat.find_spec hex
      have hi0 : 0 < i := by
        by_contra hnot
        have hieq : i = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hieq, hc0, wordDist_self] at hi
        omega
      have hprevN : i - 1 ≤ n := by omega
      have hprev : wordDist S (g x) (g (c (i - 1))) < a := by
        have hminimal : ¬ (i - 1 ≤ n ∧
            a ≤ wordDist S (g x) (g (c (i - 1)))) :=
          Nat.find_min hex (by omega)
        omega
      have hstepT : wordDist T (c (i - 1)) (c i) = 1 := by
        have hchain := hc (i - 1) i (by omega) hi.1
        calc
          wordDist T (c (i - 1)) (c i) = i - (i - 1) := hchain
          _ = 1 := by omega
      have hstepS : wordDist S (g (c (i - 1))) (g (c i)) ≤ k + B := by
        have h := hgdist (c (i - 1)) (c i)
        rw [hstepT] at h
        dsimp [B]
        omega
      have hci : wordDist S (g x) (g (c i)) ≤ a + (k + B) := by
        have htri := wordDist_triangle hS (g x) (g (c (i - 1))) (g (c i))
        omega
      obtain ⟨q, hq, hciq⟩ := hproject i hi.1
      have hpar1 : wordDist S (g x) r ≤
          wordDist S (g x) q + (k + B + R) := by
        have htri := wordDist_triangle hS (g x) q (g (c i))
        have hcomm : wordDist S q (g (c i)) = wordDist S (g (c i)) q :=
          wordDist_comm hS _ _
        dsimp [a] at hi ⊢
        omega
      have hpar2 : wordDist S (g x) q ≤
          wordDist S (g x) r + (k + B + R) := by
        have htri := wordDist_triangle hS (g x) (g (c i)) q
        dsimp [a] at hci ⊢
        omega
      have hrq : wordDist S r q ≤ k + B + R + 2 * delta :=
        HullSC.wordDist_le_of_isBetween_of_param_le hS hdelta hr hq hpar1 hpar2
      have hrci : wordDist S r (g (c i)) ≤ k + B + 2 * R + 2 * delta := by
        have htri := wordDist_triangle hS r q (g (c i))
        have hcomm : wordDist S q (g (c i)) = wordDist S (g (c i)) q :=
          wordDist_comm hS _ _
        omega
      refine ⟨c i, ?_, ?_⟩
      · have hbet := hc.isBetween hi.1
        rwa [hc0, hcn] at hbet
      · have h1 := hfwd r (g (c i))
        have htri := wordDist_triangle hT (f r) (f (g (c i))) (c i)
        have hfrci : wordDist T (f r) (c i) ≤
            k * wordDist S r (g (c i)) + 2 * C := by
          calc
            wordDist T (f r) (c i)
                ≤ wordDist T (f r) (f (g (c i))) +
                    wordDist T (f (g (c i))) (c i) := htri
            _ ≤ (k * wordDist S r (g (c i)) + C) + C :=
              Nat.add_le_add h1 (hg (c i))
            _ = k * wordDist S r (g (c i)) + 2 * C := by ring
        calc
          wordDist T (f r) (c i)
              ≤ k * wordDist S r (g (c i)) + 2 * C := hfrci
          _ ≤ k * (k + B + 2 * R + 2 * delta) + 2 * C :=
            Nat.add_le_add_right (Nat.mul_le_mul_left k hrci) (2 * C)
          _ = M := by rfl

  let D : ℕ := k * R + 4 * k * delta + M + 3 * C
  have hslimT : IsSlimTriangles T D := by
    intro x y z p hp
    obtain ⟨c, hc0, hcn, hc, hcp⟩ := exists_isGeodesicChain_through hT hp
    let n : ℕ := wordDist T x y
    have hcqg : IsQuasiGeodesic S k B n (fun i => g (c i)) :=
      pullback_quasi n c hc
    have hip : wordDist T x p ≤ n := by
      have hp' : wordDist T x p + wordDist T p y = wordDist T x y := hp
      dsimp [n]
      omega
    obtain ⟨q, hq, hpq⟩ :=
      hMorse n (fun i => g (c i)) hcqg (wordDist T x p) hip
    rw [hc0, hcn] at hq
    rw [hcp] at hpq
    rcases hslimS (g x) (g y) (g z) q hq with
      ⟨r, hr, hqr⟩ | ⟨r, hr, hqr⟩
    · obtain ⟨s, hs, hrs⟩ := source_between_to_target hr
      refine Or.inl ⟨s, hs, ?_⟩
      have hpg : wordDist T p (f (g p)) ≤ C := by
        rw [wordDist_comm hT]
        exact hg p
      have hpqT := hfwd (g p) q
      have hqrT := hfwd q r
      have htri1 := wordDist_triangle hT p (f (g p)) (f q)
      have htri2 := wordDist_triangle hT p (f q) (f r)
      have htri3 := wordDist_triangle hT p (f r) s
      have hpqT' : wordDist T (f (g p)) (f q) ≤ k * R + C :=
        hpqT.trans (Nat.add_le_add_right (Nat.mul_le_mul_left k hpq) C)
      have hqrT' : wordDist T (f q) (f r) ≤ 4 * k * delta + C := by
        calc
          wordDist T (f q) (f r) ≤ k * wordDist S q r + C := hqrT
          _ ≤ k * (4 * delta) + C :=
            Nat.add_le_add_right (Nat.mul_le_mul_left k hqr) C
          _ = 4 * k * delta + C := by ring
      have hpath : wordDist T p s ≤
          wordDist T p (f (g p)) +
            (wordDist T (f (g p)) (f q) +
              (wordDist T (f q) (f r) + wordDist T (f r) s)) := by
        omega
      calc
        wordDist T p s ≤ wordDist T p (f (g p)) +
            (wordDist T (f (g p)) (f q) +
              (wordDist T (f q) (f r) + wordDist T (f r) s)) := hpath
        _ ≤ C + ((k * R + C) + ((4 * k * delta + C) + M)) :=
          Nat.add_le_add hpg
            (Nat.add_le_add hpqT' (Nat.add_le_add hqrT' hrs))
        _ = D := by dsimp [D]; ring
    · obtain ⟨s, hs, hrs⟩ := source_between_to_target hr
      refine Or.inr ⟨s, hs, ?_⟩
      have hpg : wordDist T p (f (g p)) ≤ C := by
        rw [wordDist_comm hT]
        exact hg p
      have hpqT := hfwd (g p) q
      have hqrT := hfwd q r
      have htri1 := wordDist_triangle hT p (f (g p)) (f q)
      have htri2 := wordDist_triangle hT p (f q) (f r)
      have htri3 := wordDist_triangle hT p (f r) s
      have hpqT' : wordDist T (f (g p)) (f q) ≤ k * R + C :=
        hpqT.trans (Nat.add_le_add_right (Nat.mul_le_mul_left k hpq) C)
      have hqrT' : wordDist T (f q) (f r) ≤ 4 * k * delta + C := by
        calc
          wordDist T (f q) (f r) ≤ k * wordDist S q r + C := hqrT
          _ ≤ k * (4 * delta) + C :=
            Nat.add_le_add_right (Nat.mul_le_mul_left k hqr) C
          _ = 4 * k * delta + C := by ring
      have hpath : wordDist T p s ≤
          wordDist T p (f (g p)) +
            (wordDist T (f (g p)) (f q) +
              (wordDist T (f q) (f r) + wordDist T (f r) s)) := by
        omega
      calc
        wordDist T p s ≤ wordDist T p (f (g p)) +
            (wordDist T (f (g p)) (f q) +
              (wordDist T (f q) (f r) + wordDist T (f r) s)) := hpath
        _ ≤ C + ((k * R + C) + ((4 * k * delta + C) + M)) :=
          Nat.add_le_add hpg
            (Nat.add_le_add hpqT' (Nat.add_le_add hqrT' hrs))
        _ = D := by dsimp [D]; ring

  exact ⟨3 * D + 1, isFourPointHyperbolic_of_isSlimTriangles hT hslimT⟩

end Hyperbolic
end GroupApproximation
