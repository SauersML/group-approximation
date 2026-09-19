import Mathlib.Computability.TuringDegree
import Mathlib.Computability.Partrec
import Mathlib.Tactic.DeriveCountable
import GroupApproximation.Meta.AxiomGuard

/-!
# Oracle programs and the use principle

For the antichain sentence of corollary `cor:wp` in `simple_kazhdan_sofic_group.tex`: "The Turing
degrees contain an antichain of size continuum [Odifreddi, Chapter V]".

* `OCode` is the type of oracle programs: the constructors of `Nat.RecursiveIn`, with one oracle
  symbol.
* `OCode.eval g c` is the partial function computed by `c` with oracle `g`.
* `exists_eval_eq`: every function recursive in `g` is computed by an oracle program.
* `setOracle B` is the characteristic function of a set of naturals, as a total oracle.
* `mem_eval_of_agreeBelow` is **the use principle**. A computation that converges with oracle `B`
  converges to the same value with every oracle agreeing with `B` below some bound.
-/

namespace GroupApproximation
namespace OracleUse

/-- Oracle programs: the constructors of `Nat.RecursiveIn`, with one oracle symbol. -/
inductive OCode where
  | zero
  | succ
  | left
  | right
  | oracle
  | pair (c d : OCode)
  | comp (c d : OCode)
  | prec (c d : OCode)
  | rfind (c : OCode)
  deriving Countable

/-- Evaluation of an oracle program at the oracle `g`, clause by clause as in `Nat.RecursiveIn`. -/
def OCode.eval (g : ℕ →. ℕ) : OCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .oracle => g
  | .pair c d => fun n => (Nat.pair <$> c.eval g n <*> d.eval g n)
  | .comp c d => fun n => d.eval g n >>= c.eval g
  | .prec c d => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (c.eval g a) fun y IH => do
        let i ← IH
        d.eval g (Nat.pair a (Nat.pair y i))
  | .rfind c => fun a => Nat.rfind fun n => (fun m => m = 0) <$> c.eval g (Nat.pair a n)

/-- **Every function recursive in `g` is computed by an oracle program.** -/
theorem exists_eval_eq {g f : ℕ →. ℕ} (h : Nat.RecursiveIn {g} f) : ∃ c : OCode, c.eval g = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g' hg' =>
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact ⟨.oracle, rfl⟩
  | pair _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨.pair c d, rfl⟩
  | comp _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨.comp c d, rfl⟩
  | prec _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨.prec c d, rfl⟩
  | rfind _ ihf =>
    obtain ⟨c, rfl⟩ := ihf
    exact ⟨.rfind c, rfl⟩

open Classical in
/-- The characteristic function of a set of naturals, as a total oracle. -/
noncomputable def setOracle (B : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (if n ∈ B then 1 else 0)

/-- `B` and `C` agree below `N`. -/
def AgreeBelow (N : ℕ) (B C : Set ℕ) : Prop :=
  ∀ m < N, (m ∈ B ↔ m ∈ C)

theorem AgreeBelow.mono {N N' : ℕ} {B C : Set ℕ} (h : AgreeBelow N' B C) (hN : N ≤ N') :
    AgreeBelow N B C :=
  fun m hm => h m (lt_of_lt_of_le hm hN)

theorem mem_bind_iff' {p : Part ℕ} {f : ℕ → Part ℕ} {x : ℕ} :
    x ∈ (p >>= f) ↔ ∃ a ∈ p, x ∈ f a := by
  rw [Part.bind_eq_bind, Part.mem_bind_iff]

theorem mem_pair_seq_iff {p q : Part ℕ} {x : ℕ} :
    x ∈ (Nat.pair <$> p <*> q) ↔ ∃ a ∈ p, ∃ b ∈ q, x = Nat.pair a b := by
  simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, Part.map_eq_map,
    Part.mem_map_iff]
  constructor
  · rintro ⟨f, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨Nat.pair a, ⟨a, ha, rfl⟩, b, hb, rfl⟩

theorem mem_map_decide_iff {q : Part ℕ} {b : Bool} :
    b ∈ ((fun m => decide (m = 0)) <$> q) ↔ ∃ r ∈ q, decide (r = 0) = b := by
  simp only [Part.map_eq_map, Part.mem_map_iff]

/-- The use principle for the recursion clause. -/
theorem mem_rec_of_agreeBelow (c d : OCode) (B : Set ℕ)
    (ihc : ∀ n x, x ∈ c.eval (setOracle B) n →
      ∃ N, ∀ C : Set ℕ, AgreeBelow N B C → x ∈ c.eval (setOracle C) n)
    (ihd : ∀ n x, x ∈ d.eval (setOracle B) n →
      ∃ N, ∀ C : Set ℕ, AgreeBelow N B C → x ∈ d.eval (setOracle C) n)
    (a : ℕ) : ∀ (k x : ℕ), x ∈ (k.rec (motive := fun _ => Part ℕ) (c.eval (setOracle B) a)
        fun y IH => IH >>= fun i => d.eval (setOracle B) (Nat.pair a (Nat.pair y i))) →
      ∃ N, ∀ C : Set ℕ, AgreeBelow N B C →
        x ∈ (k.rec (motive := fun _ => Part ℕ) (c.eval (setOracle C) a)
          fun y IH => IH >>= fun i => d.eval (setOracle C) (Nat.pair a (Nat.pair y i))) := by
  intro k
  induction k with
  | zero => exact fun x hx => ihc a x hx
  | succ k ih =>
    intro x hx
    have hx' : x ∈ ((k.rec (motive := fun _ => Part ℕ) (c.eval (setOracle B) a)
        fun y IH => IH >>= fun i => d.eval (setOracle B) (Nat.pair a (Nat.pair y i))) >>=
          fun i => d.eval (setOracle B) (Nat.pair a (Nat.pair k i))) := hx
    obtain ⟨i, hi, hxi⟩ := mem_bind_iff'.1 hx'
    obtain ⟨N₁, h₁⟩ := ih i hi
    obtain ⟨N₂, h₂⟩ := ihd _ x hxi
    refine ⟨max N₁ N₂, fun C hC => ?_⟩
    show x ∈ ((k.rec (motive := fun _ => Part ℕ) (c.eval (setOracle C) a)
        fun y IH => IH >>= fun i => d.eval (setOracle C) (Nat.pair a (Nat.pair y i))) >>=
          fun i => d.eval (setOracle C) (Nat.pair a (Nat.pair k i)))
    exact mem_bind_iff'.2 ⟨i, h₁ C (hC.mono (le_max_left _ _)), h₂ C (hC.mono (le_max_right _ _))⟩

open Classical in
/-- **The use principle.** -/
theorem mem_eval_of_agreeBelow (c : OCode) (B : Set ℕ) :
    ∀ n x, x ∈ c.eval (setOracle B) n →
      ∃ N, ∀ C : Set ℕ, AgreeBelow N B C → x ∈ c.eval (setOracle C) n := by
  induction c with
  | zero => exact fun n x hx => ⟨0, fun C _ => hx⟩
  | succ => exact fun n x hx => ⟨0, fun C _ => hx⟩
  | left => exact fun n x hx => ⟨0, fun C _ => hx⟩
  | right => exact fun n x hx => ⟨0, fun C _ => hx⟩
  | oracle =>
    intro n x hx
    refine ⟨n + 1, fun C hC => ?_⟩
    have e : n ∈ B ↔ n ∈ C := hC n (Nat.lt_succ_self n)
    have hx' : x ∈ setOracle B n := hx
    show x ∈ setOracle C n
    simp only [setOracle, Part.mem_some_iff] at hx' ⊢
    rw [hx']
    exact if_congr e rfl rfl
  | pair c d ihc ihd =>
    intro n x hx
    have hx' : x ∈ (Nat.pair <$> c.eval (setOracle B) n <*> d.eval (setOracle B) n) := hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_pair_seq_iff.1 hx'
    obtain ⟨N₁, h₁⟩ := ihc n a ha
    obtain ⟨N₂, h₂⟩ := ihd n b hb
    refine ⟨max N₁ N₂, fun C hC => ?_⟩
    show Nat.pair a b ∈ (Nat.pair <$> c.eval (setOracle C) n <*> d.eval (setOracle C) n)
    exact mem_pair_seq_iff.2 ⟨a, h₁ C (hC.mono (le_max_left _ _)), b,
      h₂ C (hC.mono (le_max_right _ _)), rfl⟩
  | comp c d ihc ihd =>
    intro n x hx
    have hx' : x ∈ (d.eval (setOracle B) n >>= c.eval (setOracle B)) := hx
    obtain ⟨y, hy, hxy⟩ := mem_bind_iff'.1 hx'
    obtain ⟨N₁, h₁⟩ := ihd n y hy
    obtain ⟨N₂, h₂⟩ := ihc y x hxy
    refine ⟨max N₁ N₂, fun C hC => ?_⟩
    show x ∈ (d.eval (setOracle C) n >>= c.eval (setOracle C))
    exact mem_bind_iff'.2 ⟨y, h₁ C (hC.mono (le_max_left _ _)), h₂ C (hC.mono (le_max_right _ _))⟩
  | prec c d ihc ihd =>
    intro p x hx
    exact mem_rec_of_agreeBelow c d B ihc ihd (Nat.unpair p).1 (Nat.unpair p).2 x hx
  | rfind c ihc =>
    intro a x hx
    have hx' : x ∈ Nat.rfind fun n => (fun m => decide (m = 0)) <$>
        c.eval (setOracle B) (Nat.pair a n) := hx
    obtain ⟨htrue, hfalse⟩ := Nat.mem_rfind.1 hx'
    have hstep : ∀ m ≤ x, ∃ r ∈ c.eval (setOracle B) (Nat.pair a m),
        decide (r = 0) = decide (m = x) := by
      intro m hm
      rcases lt_or_eq_of_le hm with h | h
      · obtain ⟨r, hr, e⟩ := mem_map_decide_iff.1 (hfalse h)
        exact ⟨r, hr, by rw [e, decide_eq_false (Nat.ne_of_lt h)]⟩
      · subst h
        obtain ⟨r, hr, e⟩ := mem_map_decide_iff.1 htrue
        exact ⟨r, hr, by rw [e, decide_eq_true rfl]⟩
    have hcollect : ∀ k, k ≤ x + 1 → ∃ N, ∀ C : Set ℕ, AgreeBelow N B C →
        ∀ m < k, ∃ r ∈ c.eval (setOracle C) (Nat.pair a m), decide (r = 0) = decide (m = x) := by
      intro k
      induction k with
      | zero => exact fun _ => ⟨0, fun C _ m hm => absurd hm (Nat.not_lt_zero m)⟩
      | succ k ih =>
        intro hk
        obtain ⟨N₁, h₁⟩ := ih (Nat.le_of_succ_le hk)
        obtain ⟨r, hr, e⟩ := hstep k (Nat.lt_succ_iff.1 hk)
        obtain ⟨N₂, h₂⟩ := ihc (Nat.pair a k) r hr
        refine ⟨max N₁ N₂, fun C hC m hm => ?_⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hm) with h | h
        · exact h₁ C (hC.mono (le_max_left _ _)) m h
        · subst h
          exact ⟨r, h₂ C (hC.mono (le_max_right _ _)), e⟩
    obtain ⟨N, hN⟩ := hcollect (x + 1) le_rfl
    refine ⟨N, fun C hC => ?_⟩
    show x ∈ Nat.rfind fun n => (fun m => decide (m = 0)) <$> c.eval (setOracle C) (Nat.pair a n)
    refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
    · obtain ⟨r, hr, e⟩ := hN C hC x (Nat.lt_succ_self x)
      exact mem_map_decide_iff.2 ⟨r, hr, by rw [e, decide_eq_true rfl]⟩
    · obtain ⟨r, hr, e⟩ := hN C hC m (Nat.lt_succ_of_lt hm)
      exact mem_map_decide_iff.2 ⟨r, hr, by rw [e, decide_eq_false (Nat.ne_of_lt hm)]⟩

end OracleUse
end GroupApproximation

#audit_axioms GroupApproximation.OracleUse.exists_eval_eq
#audit_axioms GroupApproximation.OracleUse.mem_eval_of_agreeBelow
