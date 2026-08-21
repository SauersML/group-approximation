import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.List.Rotate
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Periodic overlap: when a self-overlap forces a word to be a proper power

The free-group `C'(1/6)` torsion theorem needs one piece of pure list
combinatorics: a criterion under which a word that agrees with a nontrivial
rotation of itself on a long prefix must be a proper power.  This file states
and proves that criterion, and — because the statement the design note
sketched is **false** — records the counterexample that fixes the threshold.

## The proper-power formalization

`IsProperPower w` is `∃ u m, 2 ≤ m ∧ w = (List.replicate m u).flatten`.  This
is Mathlib's own shape for a word power over `List (α × Bool)`
(`FreeGroup.IsCyclicallyReduced.flatten_replicate`,
`FreeGroup.reduce_flatten_replicate`), so no adapter is needed at either end,
and `mk_flatten_replicate` transports it to `FreeGroup.mk w = g ^ m` in one
step.  Everything is proved for `List β`; `β = α × Bool` is the repo's word
convention and is the instance the small-cancellation lane uses.

Note the degenerate corner: `IsProperPower []` holds, with `u = []`
(`isProperPower_nil`).  Relators are nonempty, so this never bites; the
rotation characterization below therefore carries a `w ≠ []` hypothesis.

## The correct threshold, and why "more than half" is false

Write `n = w.length` and `d = Nat.gcd k n`.  A common prefix `p` of `w` and
`w.rotate k` says exactly that the *cyclic* word `w` satisfies
`w[i] = w[i + k mod n]` for `i < p.length` — that is, all but `n - p.length`
of the `n` cyclic period-`k` constraints hold.  Those constraints split the
cyclic positions into `d` orbits, each a single `k`-cycle of length `n / d`,
and one missing constraint per orbit still leaves the orbit connected.  So the
word is forced to have cyclic period `d` exactly when at most one constraint
per orbit is missing, i.e. when

    n - p.length ≤ d,     equivalently     n ≤ p.length + gcd k n.

That is the hypothesis of `rotate_gcd_eq_self_of_prefix_rotate`, and it is the
image under `z = w ++ w.take j` of the sharp Fine–Wilf bound
`k + n - gcd k n ≤ z.length` — so the proof is Mathlib's `List.HasPeriod.gcd`
applied to one aligned window, not a fresh induction.

The design note proposed the hypothesis `n ≤ 2 * p.length` ("the arc exceeds
half").  That is **false**, and `not_isProperPower_of_two_mul_length_le` refutes
it by machine check: `w = 0 1 0 0 1 0 0 1` over `Fin 2`, `k = 3`,
`p = w.take 6`.  Here `p` is three quarters of `w`, `p` prefixes both `w` and
`w.rotate 3`, and `w` is not a proper power.  Since `gcd 3 8 = 1` the same
witness shows the true threshold is sharp: it fails `n ≤ p.length + gcd k n` by
exactly one (`overlapWitness_length_eq`).  So no constant multiple of
`p.length` can serve — with `gcd k n = 1` the hypothesis demands
`p.length ≥ n - 1`, and that is unavoidable.

## What the torsion theorem can actually consume

`n ≤ p.length + gcd k n` is a near-total overlap, and the arc a Greendlinger
count produces is nowhere near that long.  So the `C'(1/6)` torsion proof does
**not** run through Fine–Wilf.  It runs through the two-occurrence dichotomy:
an arc of `w^m` matched against a relator `r` gives two occurrences of one word
inside the cyclic word `r`, i.e. a `p` prefixing both `r.rotate a` and
`r.rotate b`, and then either

* `r.rotate a ≠ r.rotate b`, and `p` is a piece for
  `SmallCancellationRouter.IsPiece (symmetrization R)` — both rotations lie in
  the symmetrization — so `C'(1/6)` bounds `p.length` by `r.length / 6`; or
* `r.rotate a = r.rotate b`, and then `isProperPower_of_rotate_eq_rotate` says
  `r` is a proper power, contradicting the no-proper-power hypothesis.

`isProperPower_of_rotate_eq_rotate` — with no length hypothesis on the overlap
at all — is therefore the lemma the torsion theorem spends.  Fine–Wilf is kept
because it is the honest general statement and costs one window.

The arc lands in `symmetrization R` while the no-proper-power hypothesis is
stated on the base family `R`, so §9 closes that gap: rotation and formal
inversion are invertible on words, hence neither creates nor destroys a proper
power (`isProperPower_symmetrization_iff`), and `noProperPower_symmetrization`
delivers the transfer in the exact `∀ u m, 2 ≤ m → r ≠ …` shape the relator
families state it in.
-/

namespace GroupApproximation
namespace PeriodicOverlap

variable {β : Type*}

/-! ## 1.  Proper powers -/

/-- **A word is a proper power** when it is the concatenation of `m ≥ 2` copies
of a single block.  This is Mathlib's shape for word powers of free-group
words, so it needs no adapter on either side. -/
def IsProperPower (w : List β) : Prop :=
  ∃ (u : List β) (m : ℕ), 2 ≤ m ∧ w = (List.replicate m u).flatten

/-- The empty word is a proper power of the empty word.  Recorded because it is
the one place the definition is looser than the informal notion; every consumer
in the small-cancellation lane has nonempty relators. -/
theorem isProperPower_nil : IsProperPower ([] : List β) :=
  ⟨[], 2, le_refl 2, by simp⟩

/-- The length of a block power. -/
theorem length_flatten_replicate (m : ℕ) (u : List β) :
    ((List.replicate m u).flatten).length = m * u.length := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- A block power commutes with its own block: reading the block off the front
and reading it off the back give the same word. -/
theorem flatten_replicate_append_comm (m : ℕ) (u : List β) :
    (List.replicate m u).flatten ++ u = u ++ (List.replicate m u).flatten := by
  have h1 : (List.replicate (m + 1) u).flatten = u ++ (List.replicate m u).flatten := by
    rw [List.replicate_succ, List.flatten_cons]
  have h2 : (List.replicate (m + 1) u).flatten = (List.replicate m u).flatten ++ u := by
    rw [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil]
  rw [← h2, h1]

/-- Rotating a block power by one block length returns it. -/
theorem rotate_length_flatten_replicate (m : ℕ) (u : List β) :
    ((List.replicate m u).flatten).rotate u.length = (List.replicate m u).flatten := by
  cases m with
  | zero => simp
  | succ m =>
      rw [List.replicate_succ, List.flatten_cons, List.rotate_append_length_eq,
        flatten_replicate_append_comm]

/-! ## 2.  Rotations that fix a word -/

/-- Rotating by a multiple of the length does nothing. -/
theorem rotate_eq_self_of_dvd {w : List β} {j : ℕ} (h : w.length ∣ j) : w.rotate j = w := by
  obtain ⟨c, rfl⟩ := h
  exact List.rotate_length_mul w c

/-- A rotation that fixes a word fixes it after any number of repetitions. -/
theorem rotate_eq_self_mul {w : List β} {a : ℕ} (ha : w.rotate a = w) (m : ℕ) :
    w.rotate (a * m) = w := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← List.rotate_rotate, ih, ha]

/-- Two rotations that fix a word: their remainder does too.  This is the
Euclidean step. -/
theorem rotate_eq_self_mod {w : List β} {a b : ℕ} (ha : w.rotate a = w)
    (hb : w.rotate b = w) : w.rotate (b % a) = w :=
  calc w.rotate (b % a) = (w.rotate (a * (b / a))).rotate (b % a) := by
        rw [rotate_eq_self_mul ha]
    _ = w.rotate (a * (b / a) + b % a) := List.rotate_rotate _ _ _
    _ = w.rotate b := by rw [Nat.div_add_mod]
    _ = w := hb

/-- **The stabilizer of a word under rotation is closed under `gcd`.**  Proved
by the same descent that computes `gcd`. -/
theorem rotate_eq_self_gcd {w : List β} (a b : ℕ) :
    w.rotate a = w → w.rotate b = w → w.rotate (Nat.gcd a b) = w := by
  induction a, b using Nat.gcd.induction with
  | H0 b => intro _ hb; simpa using hb
  | H1 a b _ ih =>
      intro ha hb
      rw [Nat.gcd_rec]
      exact ih (rotate_eq_self_mod ha hb) ha

/-- **Two rotations that agree differ by a rotation that fixes the word.**
Rotating by `a` is invertible, so `w.rotate (a + c) = w.rotate a` cancels down
to `w.rotate c = w`. -/
theorem rotate_eq_self_of_add {w : List β} {a c : ℕ}
    (h : w.rotate (a + c) = w.rotate a) : w.rotate c = w := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  have hpos : 0 < w.length := List.length_pos_of_ne_nil hw
  obtain ⟨m, hsum⟩ : ∃ m, a + m = w.length * a :=
    ⟨w.length * a - a, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left a hpos)⟩
  have hfix : w.rotate (a + m) = w := by
    rw [hsum]; exact List.rotate_length_mul w a
  calc w.rotate c = (w.rotate (a + m)).rotate c := by rw [hfix]
    _ = w.rotate (a + m + c) := List.rotate_rotate _ _ _
    _ = w.rotate (a + c + m) := by rw [Nat.add_right_comm]
    _ = (w.rotate (a + c)).rotate m := (List.rotate_rotate _ _ _).symm
    _ = (w.rotate a).rotate m := by rw [h]
    _ = w.rotate (a + m) := List.rotate_rotate _ _ _
    _ = w := hfix

/-! ## 3.  Rotation versus period -/

/-- Mathlib's `List.HasPeriod` unfolded to the self-overlap it is defined by. -/
theorem hasPeriod_iff_drop_prefix {w : List β} {d : ℕ} :
    List.HasPeriod w d ↔ w.drop d <+: w :=
  ⟨List.HasPeriod.drop_prefix d, fun h => by
    show w <+: List.take d w ++ w
    have h2 := (List.prefix_append_right_inj (w.take d)).mpr h
    rwa [List.take_append_drop] at h2⟩

/-- A rotation that fixes a word is a period of it.  (The converse needs the
period to divide the length: see `rotate_eq_self_of_hasPeriod_of_dvd`.) -/
theorem hasPeriod_of_rotate_eq_self {w : List β} {d : ℕ} (hd : d ≤ w.length)
    (h : w.rotate d = w) : List.HasPeriod w d :=
  hasPeriod_iff_drop_prefix.mpr ⟨w.take d, by rw [← List.rotate_eq_drop_append_take hd, h]⟩

/-- **A period that divides the length cuts the word into equal blocks.**
Induction on the block count; the block itself is stable along the induction
because each tail is a prefix of the word. -/
theorem eq_flatten_replicate_aux {u : List β} :
    ∀ (m : ℕ) (w : List β), w.length = m * u.length → List.HasPeriod w u.length →
      (m = 0 ∨ u <+: w) → w = (List.replicate m u).flatten := by
  intro m
  induction m with
  | zero =>
      intro w hlen _ _
      rw [Nat.zero_mul] at hlen
      simp [List.eq_nil_of_length_eq_zero hlen]
  | succ m ih =>
      intro w hlen hper hpre
      have hu_pre : u <+: w := hpre.resolve_left (Nat.succ_ne_zero m)
      have hutake : List.take u.length w = u := (List.prefix_iff_eq_take.mp hu_pre).symm
      have hsplit : w = u ++ w.drop u.length := by
        conv_lhs => rw [← List.take_append_drop u.length w]
        rw [hutake]
      have hdlen : (w.drop u.length).length = m * u.length := by
        rw [List.length_drop, hlen, Nat.succ_mul, Nat.add_sub_cancel]
      have hper' : List.HasPeriod (w.drop u.length) u.length :=
        hper.infix (List.drop_suffix _ _).isInfix
      have hnext : m = 0 ∨ u <+: w.drop u.length := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact Or.inl rfl
        · refine Or.inr (List.prefix_of_prefix_length_le hu_pre
            (List.HasPeriod.drop_prefix _ hper) ?_)
          rw [hdlen]
          exact Nat.le_mul_of_pos_left _ hm
      have hrec := ih (w.drop u.length) hdlen hper' hnext
      rw [List.replicate_succ, List.flatten_cons, ← hrec]
      exact hsplit

/-- **A period that divides the length exhibits the word as a block power.** -/
theorem eq_flatten_replicate_of_hasPeriod {w : List β} {d : ℕ}
    (hdvd : d ∣ w.length) (hper : List.HasPeriod w d) :
    w = (List.replicate (w.length / d) (w.take d)).flatten := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  have hpos : 0 < w.length := List.length_pos_of_ne_nil hw
  have hdle : d ≤ w.length := Nat.le_of_dvd hpos hdvd
  have hulen : (w.take d).length = d := List.length_take_of_le hdle
  refine eq_flatten_replicate_aux (u := w.take d) (w.length / d) w ?_ ?_ ?_
  · rw [hulen, Nat.div_mul_cancel hdvd]
  · rwa [hulen]
  · exact Or.inr (List.take_prefix d w)

/-- A period that divides the length is a rotation fixing the word. -/
theorem rotate_eq_self_of_hasPeriod_of_dvd {w : List β} {d : ℕ}
    (hdvd : d ∣ w.length) (hper : List.HasPeriod w d) : w.rotate d = w := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  have hpos : 0 < w.length := List.length_pos_of_ne_nil hw
  have hulen : (w.take d).length = d :=
    List.length_take_of_le (Nat.le_of_dvd hpos hdvd)
  have hflat := eq_flatten_replicate_of_hasPeriod hdvd hper
  have key := rotate_length_flatten_replicate (w.length / d) (w.take d)
  rw [hulen, ← hflat] at key
  exact key

/-- **A short period makes the word a proper power.** -/
theorem isProperPower_of_hasPeriod {w : List β} {d : ℕ} (hd : 0 < d)
    (hlt : d < w.length) (hdvd : d ∣ w.length) (hper : List.HasPeriod w d) :
    IsProperPower w := by
  refine ⟨w.take d, w.length / d, ?_, eq_flatten_replicate_of_hasPeriod hdvd hper⟩
  obtain ⟨q, hq⟩ := hdvd
  have hq2 : 2 ≤ q := by
    rcases q with _ | _ | q
    · omega
    · omega
    · omega
  rw [hq, Nat.mul_div_cancel_left q hd]
  exact hq2

/-! ## 4.  The rotation criterion -/

/-- **A word fixed by a nontrivial rotation is a proper power.**  The rotation
stabilizer is closed under `gcd`, so a fixing rotation by `k` upgrades to one by
`gcd k n`, which divides `n`. -/
theorem isProperPower_of_rotate_eq_self {w : List β} {k : ℕ} (hk : 0 < k)
    (hkw : k < w.length) (h : w.rotate k = w) : IsProperPower w := by
  have hgcd : w.rotate (Nat.gcd k w.length) = w :=
    rotate_eq_self_gcd k w.length h (List.rotate_length w)
  have hle : Nat.gcd k w.length ≤ k :=
    Nat.le_of_dvd hk (Nat.gcd_dvd_left k w.length)
  have hpos : 0 < Nat.gcd k w.length := by
    refine Nat.pos_of_ne_zero fun hz => ?_
    rw [Nat.gcd_eq_zero_iff] at hz
    omega
  exact isProperPower_of_hasPeriod hpos (lt_of_le_of_lt hle hkw)
    (Nat.gcd_dvd_right k w.length)
    (hasPeriod_of_rotate_eq_self (le_trans hle hkw.le) hgcd)

/-- **The rotation characterization of a proper power.**  This is the working
form: a nonempty word is a proper power exactly when some nontrivial rotation
fixes it.  It is also what makes concrete non-examples decidable. -/
theorem isProperPower_iff_exists_rotate {w : List β} (hw : w ≠ []) :
    IsProperPower w ↔ ∃ d, 0 < d ∧ d < w.length ∧ w.rotate d = w := by
  constructor
  · rintro ⟨u, m, hm, rfl⟩
    have hune : u ≠ [] := by
      rintro rfl
      exact hw (by simp)
    have hulen : 0 < u.length := List.length_pos_of_ne_nil hune
    refine ⟨u.length, hulen, ?_, rotate_length_flatten_replicate m u⟩
    rw [length_flatten_replicate]
    calc u.length < 2 * u.length := by omega
      _ ≤ m * u.length := Nat.mul_le_mul_right u.length hm
  · rintro ⟨d, hd, hdlt, hrot⟩
    exact isProperPower_of_rotate_eq_self hd hdlt hrot

/-- **Being a proper power is a property of the cyclic word.** -/
theorem isProperPower_rotate {w : List β} (a : ℕ) :
    IsProperPower (w.rotate a) ↔ IsProperPower w := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  have hwr : w.rotate a ≠ [] := fun h => hw (List.rotate_eq_nil_iff.mp h)
  rw [isProperPower_iff_exists_rotate hw, isProperPower_iff_exists_rotate hwr,
    List.length_rotate]
  constructor
  · rintro ⟨d, hd, hdlt, hrot⟩
    rw [List.rotate_rotate] at hrot
    exact ⟨d, hd, hdlt, rotate_eq_self_of_add hrot⟩
  · rintro ⟨d, hd, hdlt, hrot⟩
    refine ⟨d, hd, hdlt, ?_⟩
    rw [List.rotate_rotate, Nat.add_comm a d, ← List.rotate_rotate, hrot]

/-- **The lemma the torsion theorem spends.**  Two rotations of a word that
coincide, with the shift a nontrivial one, make the word a proper power.  No
hypothesis on any overlap length: this is the branch of the two-occurrence
dichotomy in which the two symmetrized relators turn out to be *equal*, so the
piece bound is unavailable and the no-proper-power hypothesis is what fires. -/
theorem isProperPower_of_rotate_eq_rotate {w : List β} {a c : ℕ} (hc : 0 < c)
    (hcw : c < w.length) (h : w.rotate (a + c) = w.rotate a) : IsProperPower w :=
  isProperPower_of_rotate_eq_self hc hcw (rotate_eq_self_of_add h)

/-! ## 5.  The Fine–Wilf criterion -/

/-- **Fine–Wilf for a cyclic self-overlap.**  If `p` prefixes both `w` and
`w.rotate k` and `w.length ≤ p.length + gcd k w.length`, then `w` is fixed by
rotation through `gcd k w.length`.

The overlap hypothesis is the sharp one; see `overlapWitness_length_eq` for the
witness that fails it by one and is not a proper power.  The proof aligns the
two occurrences in the window `z = w ++ w.take j` of length `k + p.length`,
which then carries both periods `k` and `w.length`, and hands that window to
Mathlib's `List.HasPeriod.gcd`. -/
theorem rotate_gcd_eq_self_of_prefix_rotate {w p : List β} {k : ℕ}
    (hk : 0 < k) (hkw : k < w.length) (hpw : p <+: w) (hpr : p <+: w.rotate k)
    (hlen : w.length ≤ p.length + Nat.gcd k w.length) :
    w.rotate (Nat.gcd k w.length) = w := by
  have hpl : p.length ≤ w.length := hpw.length_le
  have hdk : Nat.gcd k w.length ≤ k :=
    Nat.le_of_dvd hk (Nat.gcd_dvd_left k w.length)
  have hdvd : Nat.gcd k w.length ∣ w.length := Nat.gcd_dvd_right k w.length
  obtain ⟨j, hj⟩ : ∃ j, p.length = w.length - k + j :=
    ⟨p.length - (w.length - k), by omega⟩
  have hjw : j ≤ w.length := by omega
  have hdroplen : (w.drop k).length = w.length - k := by simp
  have htakelen : (w.take j).length = j := List.length_take_of_le hjw
  set z : List β := w ++ w.take j with hz
  have hzlen : z.length = k + p.length := by
    rw [hz, List.length_append, htakelen]
    omega
  have hpz : p <+: z := hpw.trans (List.prefix_append w (w.take j))
  have hzn : List.HasPeriod z w.length := by
    refine hasPeriod_iff_drop_prefix.mpr ?_
    rw [hz, List.drop_left]
    exact (List.take_prefix j w).trans (List.prefix_append w (w.take j))
  have hpsplit : p = w.drop k ++ w.take j := by
    have h1 : p = List.take p.length (w.rotate k) := List.prefix_iff_eq_take.mp hpr
    rw [List.rotate_eq_drop_append_take hkw.le, List.take_append, hdroplen,
      (List.take_eq_self_iff (w.drop k)).mpr (by omega), List.take_take,
      Nat.min_eq_left (by omega),
      show p.length - (w.length - k) = j from by omega] at h1
    exact h1
  have hzk : List.HasPeriod z k := by
    refine hasPeriod_iff_drop_prefix.mpr ?_
    rw [hz, List.drop_append_of_le_length hkw.le, ← hpsplit]
    exact hpz
  have hfw : List.HasPeriod z (Nat.gcd k w.length) := by
    refine hzk.gcd hzn ?_
    rw [hzlen]
    omega
  have hwper : List.HasPeriod w (Nat.gcd k w.length) :=
    hfw.infix (List.prefix_append w (w.take j)).isInfix
  exact rotate_eq_self_of_hasPeriod_of_dvd hdvd hwper

/-- **The Fine–Wilf criterion, as a proper-power statement.** -/
theorem isProperPower_of_prefix_rotate {w p : List β} {k : ℕ}
    (hk : 0 < k) (hkw : k < w.length) (hpw : p <+: w) (hpr : p <+: w.rotate k)
    (hlen : w.length ≤ p.length + Nat.gcd k w.length) : IsProperPower w := by
  have hdk : Nat.gcd k w.length ≤ k :=
    Nat.le_of_dvd hk (Nat.gcd_dvd_left k w.length)
  have hpos : 0 < Nat.gcd k w.length := by
    refine Nat.pos_of_ne_zero fun hz => ?_
    rw [Nat.gcd_eq_zero_iff] at hz
    omega
  exact isProperPower_of_rotate_eq_self hpos (lt_of_le_of_lt hdk hkw)
    (rotate_gcd_eq_self_of_prefix_rotate hk hkw hpw hpr hlen)

/-- **The cyclic-word form.**  Two occurrences of `p` in the cyclic word `w`,
at cyclic distance `b - a`, with the overlap long enough. -/
theorem isProperPower_of_prefix_rotate_rotate {w p : List β} {a b : ℕ}
    (hab : a < b) (hbw : b - a < w.length) (hpa : p <+: w.rotate a)
    (hpb : p <+: w.rotate b)
    (hlen : w.length ≤ p.length + Nat.gcd (b - a) w.length) : IsProperPower w := by
  have hrot : (w.rotate a).rotate (b - a) = w.rotate b := by
    rw [List.rotate_rotate]
    congr 1
    omega
  refine (isProperPower_rotate a).mp ?_
  refine isProperPower_of_prefix_rotate (w := w.rotate a) (k := b - a) (by omega) ?_ hpa ?_ ?_
  · rwa [List.length_rotate]
  · rwa [hrot]
  · rwa [List.length_rotate]

/-! ## 6.  The counterexample that fixes the threshold -/

/-- The witness word `0 1 0 0 1 0 0 1`.  Its prefix of length six prefixes both
it and its rotation by three, so the overlap is three quarters of the word —
and it is not a proper power.  Since `gcd 3 8 = 1`, it misses the sharp
hypothesis `w.length ≤ p.length + gcd k w.length` by exactly one. -/
def overlapWitness : List (Fin 2) := [0, 1, 0, 0, 1, 0, 0, 1]

/-- The long common prefix of `overlapWitness` and its rotation by three. -/
def overlapWitnessPrefix : List (Fin 2) := [0, 1, 0, 0, 1, 0]

/-- The witness is not a proper power: no nontrivial rotation fixes it. -/
theorem not_isProperPower_overlapWitness : ¬ IsProperPower overlapWitness := by
  rw [isProperPower_iff_exists_rotate (by decide)]
  rintro ⟨d, hd0, hdlt, hrot⟩
  have h8 : d < 8 := by simpa [overlapWitness] using hdlt
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | d <;>
    first
      | omega
      | exact absurd hrot (by decide)

/-- The witness misses the sharp Fine–Wilf hypothesis by exactly one, so
`rotate_gcd_eq_self_of_prefix_rotate` cannot be weakened. -/
theorem overlapWitness_length_eq :
    overlapWitness.length
      = overlapWitnessPrefix.length + Nat.gcd 3 overlapWitness.length + 1 := by
  decide

/-- **The design note's "more than half" form is false.**  Refuted by the
witness: the overlap is three quarters of the word and the word is not a proper
power.  Any threshold phrased as a constant fraction of `w.length` fails the
same way, because with `gcd k w.length = 1` the true hypothesis forces the
overlap to be all but one letter. -/
theorem not_isProperPower_of_two_mul_length_le :
    ¬ ∀ (w p : List (Fin 2)) (k : ℕ), 0 < k → k < w.length → p <+: w →
        p <+: w.rotate k → w.length ≤ 2 * p.length → IsProperPower w := by
  intro h
  refine not_isProperPower_overlapWitness
    (h overlapWitness overlapWitnessPrefix 3 (by decide) (by decide) ?_ ?_ (by decide))
  · exact ⟨[0, 1], by decide⟩
  · exact ⟨[1, 0], by decide⟩

/-! ## 7.  Transfer to the free group -/

section FreeGroupTransfer

variable {α : Type*}

/-- A block power spells a power in the free group. -/
theorem mk_flatten_replicate (m : ℕ) (u : List (α × Bool)) :
    FreeGroup.mk ((List.replicate m u).flatten) = FreeGroup.mk u ^ m := by
  induction m with
  | zero => simp [FreeGroup.one_eq_mk]
  | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- A word that is a proper power spells a proper power in the free group.  The
converse is false — cancellation can make a reduced-word non-power spell a
power — which is why the small-cancellation hypotheses are stated on words. -/
theorem exists_pow_of_isProperPower {w : List (α × Bool)} (h : IsProperPower w) :
    ∃ (g : FreeGroup α) (m : ℕ), 2 ≤ m ∧ FreeGroup.mk w = g ^ m := by
  obtain ⟨u, m, hm, rfl⟩ := h
  exact ⟨FreeGroup.mk u, m, hm, mk_flatten_replicate m u⟩

end FreeGroupTransfer

/-! ## 8.  Closure under the operations that build a symmetrization -/

/-- Reversal preserves proper powers. -/
theorem isProperPower_reverse {w : List β} (h : IsProperPower w) :
    IsProperPower w.reverse := by
  obtain ⟨u, m, hm, rfl⟩ := h
  refine ⟨u.reverse, m, hm, ?_⟩
  rw [List.reverse_flatten, List.map_replicate, List.reverse_replicate]

/-- Relabelling letters preserves proper powers. -/
theorem isProperPower_map {γ : Type*} (f : β → γ) {w : List β} (h : IsProperPower w) :
    IsProperPower (w.map f) := by
  obtain ⟨u, m, hm, rfl⟩ := h
  refine ⟨u.map f, m, hm, ?_⟩
  rw [List.map_flatten, List.map_replicate]

/-- **Formal inversion of a block power, on the nose.**  `invRev` reverses the
word and inverts every letter, so `invRev (a ++ b) = invRev b ++ invRev a`; the
blocks of a block power are all equal, so reversing their order changes
nothing and the exponent is untouched. -/
theorem invRev_flatten_replicate {α : Type*} (m : ℕ) (u : List (α × Bool)) :
    FreeGroup.invRev ((List.replicate m u).flatten)
      = (List.replicate m (FreeGroup.invRev u)).flatten := by
  rw [FreeGroup.invRev, List.map_flatten, List.map_replicate, List.reverse_flatten,
    List.map_replicate, List.reverse_replicate]
  rfl

/-- Formal inversion preserves proper powers. -/
theorem isProperPower_invRev {α : Type*} {w : List (α × Bool)} (h : IsProperPower w) :
    IsProperPower (FreeGroup.invRev w) := by
  obtain ⟨u, m, hm, rfl⟩ := h
  exact ⟨FreeGroup.invRev u, m, hm, invRev_flatten_replicate m u⟩

/-- **Formal inversion does not create or destroy proper powers.**  `invRev` is
an involution, so the forward direction gives both. -/
theorem isProperPower_invRev_iff {α : Type*} {w : List (α × Bool)} :
    IsProperPower (FreeGroup.invRev w) ↔ IsProperPower w := by
  refine ⟨fun h => ?_, isProperPower_invRev⟩
  have h2 := isProperPower_invRev h
  rwa [FreeGroup.invRev_invRev] at h2

/-! ## 9.  Transfer from a base family to its symmetrization

The Greendlinger arc lands in `SmallCancellationRouter.symmetrization R`, while
the no-proper-power hypothesis is stated on the base family `R`.  These lemmas
are the bridge.  They are phrased on the raw existential rather than on
`symmetrization R` so that this module stays Mathlib-only: `symmetrization R` is
*defined* as `{w | ∃ r ∈ R, ∃ n, w = r.rotate n ∨ w = (invRev r).rotate n}`, so a
hypothesis `hw : w ∈ SmallCancellationRouter.symmetrization R` is definitionally
the hypothesis these lemmas take, and passes to them with no conversion. -/

/-- **The `NoProperPower` shape, negated.**  The relator families in this
development state "no relator is a proper power" as a `≠` under two universal
quantifiers; that is exactly `¬ IsProperPower`, and this is the bridge. -/
theorem not_isProperPower_iff {w : List β} :
    ¬ IsProperPower w ↔ ∀ (u : List β) (m : ℕ), 2 ≤ m → w ≠ (List.replicate m u).flatten := by
  constructor
  · intro h u m hm heq
    exact h ⟨u, m, hm, heq⟩
  · rintro h ⟨u, m, hm, heq⟩
    exact h u m hm heq

/-- **A member of the symmetrization is a proper power exactly when its base
relator is.**  Rotation and formal inversion are both invertible on words, so
neither can create or destroy a proper power. -/
theorem isProperPower_symmetrization_iff {α : Type*} (r : List (α × Bool)) (n : ℕ) :
    (IsProperPower (r.rotate n) ↔ IsProperPower r) ∧
      (IsProperPower ((FreeGroup.invRev r).rotate n) ↔ IsProperPower r) :=
  ⟨isProperPower_rotate n, (isProperPower_rotate n).trans isProperPower_invRev_iff⟩

/-- **No-proper-power transfers from a base family to its symmetrization.**
Take `hw` from `w ∈ SmallCancellationRouter.symmetrization R`, which is
definitionally this existential. -/
theorem not_isProperPower_of_mem_symmetrization {α : Type*} {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, ¬ IsProperPower r) {w : List (α × Bool)}
    (hw : ∃ r ∈ R, ∃ n : ℕ, w = r.rotate n ∨ w = (FreeGroup.invRev r).rotate n) :
    ¬ IsProperPower w := by
  obtain ⟨r, hr, n, rfl | rfl⟩ := hw
  · exact fun h => hR r hr ((isProperPower_symmetrization_iff r n).1.mp h)
  · exact fun h => hR r hr ((isProperPower_symmetrization_iff r n).2.mp h)

/-- **The same transfer, in the `NoProperPower` shape the relator families use.**
This is the drop-in: given the base-family hypothesis in its stated form, it
returns the same form for every member of the symmetrized family. -/
theorem noProperPower_symmetrization {α : Type*} {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, ∀ (u : List (α × Bool)) (m : ℕ), 2 ≤ m →
      r ≠ (List.replicate m u).flatten) :
    ∀ w : List (α × Bool),
      (∃ r ∈ R, ∃ n : ℕ, w = r.rotate n ∨ w = (FreeGroup.invRev r).rotate n) →
      ∀ (u : List (α × Bool)) (m : ℕ), 2 ≤ m → w ≠ (List.replicate m u).flatten := by
  intro w hw
  refine not_isProperPower_iff.mp
    (not_isProperPower_of_mem_symmetrization (fun r hr => ?_) hw)
  exact not_isProperPower_iff.mpr (hR r hr)

end PeriodicOverlap
end GroupApproximation
