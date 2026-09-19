import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Step
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg words over a graded ring: all degrees from degree one (lane pal-q111, H.L2)

Iterating `Graded.Rels.rels_extend`: a family satisfying the homogeneous Steinberg relations of
degree `≤ 1` extends, without changing its values in degrees `≤ 1`, to a family satisfying all
homogeneous Steinberg relations (Tulenbaev, Lemma 3.3; Lavrenov–Sinchuk, Prop 5.3).

* `iter hN Y n`: the family extended `n` times, correct in degrees `≤ 1 + n`
  (`Rels.iter`).
* `limit hN Y`: its value in degree `d` is that of `iter hN Y (d - 1).toNat`.
* `Rels.limit`: the limit satisfies the relations of every degree, and `limit_of_le_one`:
  it agrees with `Y` in degrees `≤ 1`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace Graded

variable {A : Type*} [CommRing A] {𝔄 : Ideal A} {G : Type*} [Group G] {N : ℕ}

/-- The relations of degree `≤ m` only see the values in degrees `≤ m`. -/
theorem Rels.congr {Y Y' : Fam G A N} {m : ℤ} (h : Rels 𝔄 Y m)
    (hYY : ∀ (i j : Fin N) (hij : i ≠ j) (d : ℤ) (c : A), d ≤ m → Y' i j hij d c = Y i j hij d c) :
    Rels 𝔄 Y' m where
  add i j hij d c c' hd hc hc' := by
    rw [hYY i j hij d c hd, hYY i j hij d c' hd, hYY i j hij d (c + c') hd]
    exact h.add i j hij d c c' hd hc hc'
  r2 i j k hij hjk hik d e c c' hd he hde hc hc' := by
    rw [hYY i j hij d c hd, hYY j k hjk e c' he, hYY i k hik (d + e) (c * c') hde]
    exact h.r2 i j k hij hjk hik d e c c' hd he hde hc hc'
  r3 i j k l hij hkl hjk hil d e c c' hd he hc hc' := by
    rw [hYY i j hij d c hd, hYY k l hkl e c' he]
    exact h.r3 i j k l hij hkl hjk hil d e c c' hd he hc hc'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.congr

theorem Rels.mono {Y : Fam G A N} {m m' : ℤ} (h : Rels 𝔄 Y m) (hm : m' ≤ m) : Rels 𝔄 Y m' where
  add i j hij d c c' hd hc hc' := h.add i j hij d c c' (by omega) hc hc'
  r2 i j k hij hjk hik d e c c' hd he hde hc hc' :=
    h.r2 i j k hij hjk hik d e c c' (by omega) (by omega) (by omega) hc hc'
  r3 i j k l hij hkl hjk hil d e c c' hd he hc hc' :=
    h.r3 i j k l hij hkl hjk hil d e c c' (by omega) (by omega) hc hc'

/-- The family extended `n` times. -/
noncomputable def iter (hN : 3 ≤ N) (Y : Fam G A N) : ℕ → Fam G A N
  | 0 => Y
  | n + 1 => extend hN (iter hN Y n) (1 + (n : ℤ))

theorem Rels.iter {Y : Fam G A N} (h : Rels 𝔄 Y 1) (hN : 3 ≤ N) (hN5 : 5 ≤ N) (n : ℕ) :
    Rels 𝔄 (iter hN Y n) (1 + (n : ℤ)) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have h' := ih.rels_extend (by omega) hN hN5
    rw [show 1 + ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) + 1 by push_cast; ring]
    exact h'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.iter

/-- `iter (n + k)` agrees with `iter n` in degrees `≤ 1 + n`. -/
theorem iter_add_of_le (hN : 3 ≤ N) (Y : Fam G A N) (n k : ℕ) {i j : Fin N} (hij : i ≠ j)
    {d : ℤ} (hd : d ≤ 1 + (n : ℤ)) (c : A) :
    iter hN Y (n + k) i j hij d c = iter hN Y n i j hij d c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih, ← Nat.add_assoc, iter]
    exact extend_of_le (m := 1 + ((n + k : ℕ) : ℤ)) hN hij (d := d) (by push_cast; omega) c

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.iter_add_of_le

theorem iter_eq_of_le (hN : 3 ≤ N) (Y : Fam G A N) {n n' : ℕ} (hnn : n ≤ n') {i j : Fin N}
    (hij : i ≠ j) {d : ℤ} (hd : d ≤ 1 + (n : ℤ)) (c : A) :
    iter hN Y n' i j hij d c = iter hN Y n i j hij d c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnn
  exact iter_add_of_le hN Y n k hij hd c

/-- **The limit family**: in degree `d` it is `iter (d - 1).toNat`. -/
noncomputable def limit (hN : 3 ≤ N) (Y : Fam G A N) : Fam G A N :=
  fun i j hij d c => iter hN Y (d - 1).toNat i j hij d c

theorem limit_eq_iter (hN : 3 ≤ N) (Y : Fam G A N) {n : ℕ} {i j : Fin N} (hij : i ≠ j) {d : ℤ}
    (hd : d ≤ 1 + (n : ℤ)) (c : A) : limit hN Y i j hij d c = iter hN Y n i j hij d c := by
  unfold limit
  rcases le_total (d - 1).toNat n with hle | hle
  · exact (iter_eq_of_le hN Y hle hij (by omega) c).symm
  · exact iter_eq_of_le hN Y hle hij hd c

theorem limit_of_le_one (hN : 3 ≤ N) (Y : Fam G A N) {i j : Fin N} (hij : i ≠ j) {d : ℤ}
    (hd : d ≤ 1) (c : A) : limit hN Y i j hij d c = Y i j hij d c :=
  limit_eq_iter hN Y (n := 0) hij (by simpa using hd) c

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.limit_of_le_one

/-- **Tulenbaev, Lemma 3.3 (all degrees).** For `N ≥ 5`, a family satisfying the homogeneous
Steinberg relations of degree `≤ 1` has a limit satisfying those of every degree. -/
theorem Rels.limit {Y : Fam G A N} (h : Rels 𝔄 Y 1) (hN : 3 ≤ N) (hN5 : 5 ≤ N) (m : ℤ) :
    Rels 𝔄 (Graded.limit hN Y) m := by
  have hn := (h.iter hN hN5 (m - 1).toNat)
  refine (hn.mono (m' := max m 1) (by omega)).congr ?_ |>.mono (le_max_left m 1)
  intro i j hij d c hd
  exact limit_eq_iter hN Y hij (by omega) c

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.limit

end Graded
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
