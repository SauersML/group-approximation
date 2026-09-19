import GroupApproximation.ClassTransposition.Presentation.Local

/-!
# Canonical split words

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
step O1, in `H P`).

For a list of primes `qs`, `D o qs` splits the cell `o` by the first prime and then every child,
from the left, by `D _ qs.tail`; `Ch o c qs` does this to the `c` cells starting at `o`. Its leaves
are all the classes of modulus `qs.prod` times the cell's modulus.

`regroup`: in `H P`, the words `Ch o p (q :: qs)` (every child split by `q`, then its subtree) and
`layer o p q ++ Ch o (p * q) qs` (all `q`-splits first) are equal, by far commutation.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- The canonical split word on the cell `o` for the primes `qs`. -/
def D : ℕ → List ℕ → List Move
  | _, [] => []
  | o, q :: qs => .split o q :: (List.range q).flatMap fun e => D (o + e * qs.prod) qs

/-- The canonical split words on the `c` cells starting at `o`. -/
def Ch (o c : ℕ) (qs : List ℕ) : List Move := (List.range c).flatMap fun e => D (o + e * qs.prod) qs

theorem D_nil (o : ℕ) : D o [] = [] := by simp [D]

theorem D_cons (o q : ℕ) (qs : List ℕ) : D o (q :: qs) = .split o q :: Ch o q qs := by
  simp only [D, Ch]

theorem Ch_zero (o : ℕ) (qs : List ℕ) : Ch o 0 qs = [] := by simp [Ch]

theorem Ch_succ (o c : ℕ) (qs : List ℕ) : Ch o (c + 1) qs = Ch o c qs ++ D (o + c * qs.prod) qs := by
  rw [Ch, Ch, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem Ch_add (o a : ℕ) (qs : List ℕ) : ∀ b, Ch o (a + b) qs = Ch o a qs ++ Ch (o + a * qs.prod) b qs
  | 0 => by rw [add_zero, Ch_zero, List.append_nil]
  | b + 1 => by
    rw [← add_assoc, Ch_succ o (a + b) qs, Ch_add o a qs b, Ch_succ (o + a * qs.prod) b qs,
      List.append_assoc,
      show o + (a + b) * qs.prod = o + a * qs.prod + b * qs.prod by ring]

theorem mul_sub_one_add {p q : ℕ} (hq : 1 ≤ q) : p * (q - 1) + p = p * q := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, mul_add_one]

/-! ### Growth, locality and primes -/

theorem growth_Ch_of {qs : List ℕ} (hg : ∀ o, growth (D o qs) + 1 = qs.prod) (o : ℕ) :
    ∀ c, growth (Ch o c qs) + c = c * qs.prod
  | 0 => by rw [Ch_zero, zero_mul]; rfl
  | c + 1 => by
    have ih := growth_Ch_of hg o c
    have h1 := hg (o + c * qs.prod)
    rw [Ch_succ, growth_append, add_one_mul]
    omega

theorem growth_D : ∀ (qs : List ℕ), (∀ q ∈ qs, 1 ≤ q) → ∀ o, growth (D o qs) + 1 = qs.prod
  | [], _, o => by rw [D_nil, List.prod_nil]; rfl
  | q :: qs, h, o => by
    have hq := h q List.mem_cons_self
    have hc := growth_Ch_of (growth_D qs fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) o q
    rw [D_cons, List.prod_cons]
    show q - 1 + growth (Ch o q qs) + 1 = q * qs.prod
    omega

theorem locS_mono {lo : ℕ} : ∀ {hi hi' : ℕ} {w : List Move}, LocS lo hi w → hi ≤ hi' →
    LocS lo hi' w
  | _, _, [], _, _ => trivial
  | _, _, .split _ _ :: _, ⟨h1, h2, h3⟩, h => ⟨h1, by omega, locS_mono h3 (by omega)⟩
  | _, _, .swap _ :: _, hw, _ => hw

theorem locS_mono_lo {lo lo' : ℕ} (hl : lo' ≤ lo) : ∀ {hi : ℕ} {w : List Move}, LocS lo hi w →
    LocS lo' hi w
  | _, [], _ => trivial
  | _, .split _ _ :: _, ⟨h1, h2, h3⟩ => ⟨by omega, h2, locS_mono_lo hl h3⟩
  | _, .swap _ :: _, hw => hw

theorem locS_Ch_of {qs : List ℕ} (hg : ∀ o, growth (D o qs) + 1 = qs.prod)
    (hl : ∀ o, LocS o (o + 1) (D o qs)) (o : ℕ) : ∀ c, LocS o (o + c) (Ch o c qs)
  | 0 => by rw [Ch_zero]; trivial
  | c + 1 => by
    rw [Ch_succ, locS_append]
    have e := growth_Ch_of hg o c
    refine ⟨locS_mono (locS_Ch_of hg hl o c) (by omega), ?_⟩
    rw [show o + (c + 1) + growth (Ch o c qs) = o + c * qs.prod + 1 by omega]
    exact locS_mono_lo (by omega) (hl (o + c * qs.prod))

theorem locS_D : ∀ (qs : List ℕ), (∀ q ∈ qs, 1 ≤ q) → ∀ o, LocS o (o + 1) (D o qs)
  | [], _, o => by rw [D_nil]; trivial
  | q :: qs, h, o => by
    have hq := h q List.mem_cons_self
    have h' : ∀ q' ∈ qs, 1 ≤ q' := fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    rw [D_cons]
    refine ⟨le_refl o, Nat.lt_succ_self o, ?_⟩
    rw [show o + 1 + (q - 1) = o + q by omega]
    exact locS_Ch_of (growth_D qs h') (locS_D qs h') o q

theorem primesIn_flatMap {f : ℕ → List Move} : ∀ l : List ℕ, (∀ e ∈ l, PrimesIn P (f e)) →
    PrimesIn P (l.flatMap f)
  | [], _ => by rw [List.flatMap_nil]; trivial
  | e :: l, h => by
    rw [List.flatMap_cons]
    exact (primesIn_append _ _).2 ⟨h e List.mem_cons_self,
      primesIn_flatMap l fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

theorem primesIn_D : ∀ (qs : List ℕ), (∀ q ∈ qs, q ∈ P' P) → ∀ o, PrimesIn P (D o qs)
  | [], _, o => by rw [D_nil]; trivial
  | q :: qs, h, o => by
    rw [D_cons]
    exact ⟨h q List.mem_cons_self, primesIn_flatMap _ fun e _ =>
      primesIn_D qs (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) _⟩

theorem primesIn_Ch (qs : List ℕ) (h : ∀ q ∈ qs, q ∈ P' P) (o c : ℕ) : PrimesIn P (Ch o c qs) :=
  primesIn_flatMap _ fun _ _ => primesIn_D qs h _

/-! ### Layers and swap words -/

theorem layer_snoc (i p q : ℕ) : layer i (p + 1) q = layer i p q ++ [.split (i + p * q) q] := by
  rw [layer, layer, List.range_succ, List.map_append, List.map_singleton]

theorem locS_layer {q : ℕ} (hq : 1 ≤ q) : ∀ (c i : ℕ), LocS i (i + c) (layer i c q)
  | 0, _ => trivial
  | c + 1, i => by
    rw [layer_succ]
    refine ⟨le_refl i, by omega, ?_⟩
    rw [show i + (c + 1) + (q - 1) = i + q + c by omega]
    exact locS_mono_lo (by omega) (locS_layer hq c (i + q))

theorem growth_layer (q : ℕ) : ∀ (c i : ℕ), growth (layer i c q) = c * (q - 1)
  | 0, _ => by rw [zero_mul]; rfl
  | c + 1, i => by
    rw [layer_succ, add_one_mul]
    show q - 1 + growth (layer (i + q) c q) = _
    rw [growth_layer q c (i + q)]
    omega

theorem primesIn_layer {q : ℕ} (hq : q ∈ P' P) : ∀ (c i : ℕ), PrimesIn P (layer i c q)
  | 0, _ => trivial
  | c + 1, i => by
    rw [layer_succ]
    exact ⟨hq, primesIn_layer hq c (i + q)⟩

theorem locB_swaps_at (o c : ℕ) : ∀ w : List ℕ, (∀ k ∈ w, k + 1 < c) → LocB o (o + c) (swaps o w)
  | [], _ => trivial
  | k :: w, h => by
    have := h k List.mem_cons_self
    show o ≤ o + k ∧ o + k + 1 < o + c ∧ LocB o (o + c) (swaps o w)
    exact ⟨by omega, by omega, locB_swaps_at o c w fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

theorem growth_swaps_at (o : ℕ) : ∀ w : List ℕ, growth (swaps o w) = 0
  | [] => rfl
  | _ :: w => growth_swaps_at o w

theorem primesIn_swaps_at (o : ℕ) : ∀ w : List ℕ, PrimesIn P (swaps o w)
  | [] => trivial
  | _ :: w => primesIn_swaps_at (P := P) o w

/-! ### Regrouping the first splits -/

section Regroup

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

/-- A split moves right past a split word acting to its left, as `Eqv`. -/
theorem push_eqv {q : ℕ} (hq : q ∈ P' P) (A : List Move) (n j lo f : ℕ) (hA : LocS lo f A)
    (hpA : PrimesIn P A) (hfj : f ≤ j) (hj : j < n) :
    Eqv P n (.split j q :: A) (A ++ [.split (j + growth A) q]) := by
  have hq1 := hpos q hq
  refine ⟨?_, ?_⟩
  · have h := push_split hB hP2 hpos hq A n j hj (leftOf_of_locS hpos hA hpA hfj) hpA
    rwa [shiftPos_eq hpos j A hpA (split_of_locS hA)] at h
  · rw [levW_cons, lev_split q hj, levW_append,
      levW_locB hpos lo A (n + q - 1) f (by omega) (locB_of_locS hA) hpA,
      levW_locB hpos lo A n f (by omega) (locB_of_locS hA) hpA, levW_cons, levW_nil,
      lev_split q (by omega)]
    omega

/-- All first-level splits of the children come first. -/
theorem regroup {q : ℕ} (hq : q ∈ P' P) (qs : List ℕ) (hqs : ∀ q' ∈ qs, q' ∈ P' P) (o : ℕ) :
    ∀ (p N : ℕ), o + p ≤ N → Eqv P N (Ch o p (q :: qs)) (layer o p q ++ Ch o (p * q) qs)
  | 0, N, _ => by
    rw [Ch_zero, zero_mul, Ch_zero, List.append_nil]
    exact Eqv.refl N _
  | p + 1, N, hN => by
    have hq1 := hpos q hq
    have hqs1 : ∀ q' ∈ qs, 1 ≤ q' := fun q' h => by have := hpos q' (hqs q' h); omega
    have hA := locS_Ch_of (growth_D qs hqs1) (locS_D qs hqs1) o (p * q)
    have hgA := growth_Ch_of (growth_D qs hqs1) o (p * q)
    have hpA : PrimesIn P (Ch o (p * q) qs) := primesIn_Ch qs hqs o (p * q)
    have hlev : levW N (layer o p q) = N + p * (q - 1) := levW_layer (by omega) p o N (by omega)
    have hm := mul_sub_one_add (p := p) (q := q) (by omega)
    have e3 := push_eqv hB hP2 hpos hq (Ch o (p * q) qs) (N + p * (q - 1)) (o + p * q) o
      (o + p * q) hA hpA le_rfl (by omega)
    have hj : o + p * q + growth (Ch o (p * q) qs) = o + p * (q :: qs).prod := by
      rw [List.prod_cons, ← mul_assoc]; omega
    rw [hj, ← hlev] at e3
    have e1 := (regroup hq qs hqs o p N (by omega)).append_right
      (D (o + p * (q :: qs).prod) (q :: qs))
    have e2 := Eqv.append_left (layer o p q)
      (e3.symm.append_right (Ch (o + p * (q :: qs).prod) q qs))
    refine (Eqv.of_eq (Ch_succ o p (q :: qs))).trans (e1.trans ((Eqv.of_eq ?_).trans
      (e2.trans (Eqv.of_eq ?_))))
    · rw [D_cons]
      simp only [List.append_assoc, List.singleton_append]
    · rw [layer_snoc, add_one_mul, Ch_add o (p * q) qs q, List.prod_cons, ← mul_assoc]
      simp only [List.append_assoc, List.singleton_append, List.cons_append]

end Regroup

end GroupApproximation.ClassTransposition.Presentation
