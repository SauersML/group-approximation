import GroupApproximation.Computability.ArithmeticalHierarchy
import GroupApproximation.Computability.WordProblemRE
import Mathlib.Data.Set.Finite.Basic

/-!
# Canonical second-level index sets

For a partial-recursive program code, infinitude of its domain is the canonical
`Π⁰₂` question and finiteness is its `Σ⁰₂` complement.  This file starts from
the step-indexed evaluator, so every search predicate below has a concrete
computable Boolean matrix.
-/

namespace GroupApproximation
namespace SecondLevelIndexSets

open ArithmeticalHierarchy
open Nat.Partrec

/-- The domain of a partial-recursive program code. -/
def codeDomain (c : Code) : Set ℕ :=
  {n | (Code.eval c n).Dom}

/-- The canonical `Π⁰₂` index set. -/
def InfiniteDomain (c : Code) : Prop :=
  (codeDomain c).Infinite

/-- Its complementary `Σ⁰₂` index set. -/
def FiniteDomain (c : Code) : Prop :=
  (codeDomain c).Finite

/-- A bounded evaluator witness: an input strictly above the requested bound
halts by the displayed evaluation stage. -/
def aboveCheck (cn : Code × ℕ) (witness : ℕ × ℕ) : Bool :=
  decide (cn.2 < witness.1) &&
    (Code.evaln witness.2 cn.1 witness.1).isSome

theorem primrec_aboveCheck : Primrec₂ aboveCheck := by
  have hcode : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hbound : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hinput : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hstage : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have heval : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) =>
      Code.evaln z.2.2 z.1.1 z.2.1 :=
    Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hstage hcode) hinput)
  exact (Primrec.and.comp
    (Primrec.nat_lt.comp hbound hinput).decide
    (Primrec.option_isSome.comp heval)).of_eq fun _ => rfl

theorem computable_aboveCheck : Computable₂ aboveCheck :=
  primrec_aboveCheck.to_comp

/-- Halting is witnessed at some finite evaluator stage. -/
theorem eval_dom_iff_exists_evaln_isSome (c : Code) (n : ℕ) :
    (Code.eval c n).Dom ↔ ∃ stage, (Code.evaln stage c n).isSome := by
  constructor
  · intro h
    rw [Part.dom_iff_mem] at h
    obtain ⟨x, hx⟩ := h
    obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hx
    exact ⟨stage, Option.isSome_iff_exists.mpr ⟨x, hstage⟩⟩
  · rintro ⟨stage, hstage⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hstage
    rw [Part.dom_iff_mem]
    exact ⟨x, Code.evaln_sound hx⟩

/-- The Boolean search matrix says exactly that the program domain has a
member above the requested bound. -/
theorem exists_aboveCheck_iff (c : Code) (bound : ℕ) :
    (∃ witness, aboveCheck (c, bound) witness = true) ↔
      ∃ n, bound < n ∧ (Code.eval c n).Dom := by
  constructor
  · rintro ⟨⟨n, stage⟩, h⟩
    simp only [aboveCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨n, h.1, (eval_dom_iff_exists_evaln_isSome c n).2 ⟨stage, h.2⟩⟩
  · rintro ⟨n, hbn, hn⟩
    obtain ⟨stage, hstage⟩ := (eval_dom_iff_exists_evaln_isSome c n).1 hn
    exact ⟨(n, stage), by simp [aboveCheck, hbn, hstage]⟩

/-- Uniform recursive enumerability of the unbounded-domain challenge. -/
theorem rePred_hasDomainAbove :
    REPred fun cn : Code × ℕ =>
      ∃ n, cn.2 < n ∧ (Code.eval cn.1 n).Dom := by
  refine (WordProblemRE.rePred_exists_eq_true computable_aboveCheck).of_eq ?_
  intro cn
  exact exists_aboveCheck_iff cn.1 cn.2

/-- Infinitude of a program domain is a `Π⁰₂` predicate. -/
theorem infiniteDomain_pi02 : Pi02 InfiniteDomain := by
  refine pi02_of_re_family rePred_hasDomainAbove ?_
  intro c
  simpa only [InfiniteDomain, codeDomain, Set.mem_setOf_eq, and_comm] using
    (Set.infinite_iff_exists_gt (s := codeDomain c))

/-- Finiteness of a program domain is a `Σ⁰₂` predicate. -/
theorem finiteDomain_sigma02 : Sigma02 FiniteDomain := by
  refine (sigma02_congr fun c => ?_).2
    ((sigma02_compl_iff InfiniteDomain).2 infiniteDomain_pi02)
  classical
  simp only [FiniteDomain, InfiniteDomain, Set.Infinite, not_not]

/-! ## Completeness

For a uniformly r.e. relation `q (a, n)`, the program compiled below halts on
input `k` exactly when the finite prefix `q (a, 0), ..., q (a, k)` is true.
Its domain is therefore infinite exactly when every row of the `Π⁰₂` instance
is true.  The construction uses only partial-recursive finite iteration and
the `s-m-n` operator `Code.curry`.
-/

section PrefixCompiler

variable {A : Type*}

/-- Run the r.e. semidecider successively on the prefix from `0` through
`bound`.  The value is irrelevant; only the domain carries information. -/
private def prefixRun (q : A × ℕ → Prop) (a : A) (bound : ℕ) : Part Unit :=
  Nat.rec
    (Part.assert (q (a, 0)) fun _ => Part.some ())
    (fun n previous => previous.bind fun _ =>
      Part.assert (q (a, n + 1)) fun _ => Part.some ())
    bound

private theorem accept_dom_iff (r : Prop) :
    (Part.assert r fun _ => Part.some ()).Dom ↔ r := by
  change (∃ _ : r, True) ↔ r
  simp

/-- The finite-prefix runner halts exactly when every requested row holds. -/
private theorem prefixRun_dom_iff (q : A × ℕ → Prop) (a : A) (bound : ℕ) :
    (prefixRun q a bound).Dom ↔ ∀ n ≤ bound, q (a, n) := by
  induction bound with
  | zero =>
      change (Part.assert (q (a, 0)) fun _ => Part.some ()).Dom ↔ _
      rw [accept_dom_iff]
      simp
  | succ bound ih =>
      change ((prefixRun q a bound).bind fun _ =>
        Part.assert (q (a, bound + 1)) fun _ => Part.some ()).Dom ↔ _
      rw [Part.bind_dom]
      constructor
      · rintro ⟨hprevious, hnext⟩ n hn
        by_cases hnb : n ≤ bound
        · exact ih.mp hprevious n hnb
        · have hn' : n = bound + 1 := by omega
          subst n
          exact (accept_dom_iff _).mp hnext
      · intro hall
        have hprevious : (prefixRun q a bound).Dom :=
          ih.mpr fun n hn => hall n (Nat.le.step hn)
        refine ⟨hprevious, ?_⟩
        exact (accept_dom_iff _).mpr (hall (bound + 1) (by omega))

variable [Primcodable A]

/-- Finite iteration of a uniform r.e. semidecider is partial recursive. -/
private theorem prefixRun_partrec₂ {q : A × ℕ → Prop} (hq : REPred q) :
    Partrec₂ (prefixRun q) := by
  have hbase : Partrec fun x : A × ℕ =>
      Part.assert (q (x.1, 0)) fun _ => Part.some () :=
    hq.comp (Computable.fst.pair (Computable.const 0))
  have hstep : Partrec₂ fun (x : A × ℕ) (y : ℕ × Unit) =>
      Part.assert (q (x.1, y.1 + 1)) fun _ => Part.some () := by
    change Partrec fun z : (A × ℕ) × (ℕ × Unit) =>
      Part.assert (q (z.1.1, z.2.1 + 1)) fun _ => Part.some ()
    exact hq.comp
      ((Computable.fst.comp Computable.fst).pair
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
  exact (Partrec.nat_rec Computable.snd hbase hstep).of_eq fun _ => rfl

/-- The numerical partial function to which `Code.exists_code` is applied.
The input is the standard code of a pair `(a, bound)`. -/
private def encodedPrefixRun (q : A × ℕ → Prop) (input : ℕ) : Part ℕ :=
  Part.bind (↑(Encodable.decode₂ (A × ℕ) input) : Part (A × ℕ)) fun x =>
    (prefixRun q x.1 x.2).map Encodable.encode

private theorem encodedPrefixRun_partrec {q : A × ℕ → Prop} (hq : REPred q) :
    Nat.Partrec (encodedPrefixRun q) := by
  exact (Partrec.bind_decode₂_iff.mp (prefixRun_partrec₂ hq)).of_eq fun _ => rfl

/-- One fixed universal code for the prefix runner before specializing its
first argument. -/
private noncomputable def prefixRunnerCode (q : A × ℕ → Prop) (hq : REPred q) : Code :=
  (Code.exists_code.mp (encodedPrefixRun_partrec hq)).choose

private theorem eval_prefixRunnerCode (q : A × ℕ → Prop) (hq : REPred q) :
    Code.eval (prefixRunnerCode q hq) = encodedPrefixRun q :=
  (Code.exists_code.mp (encodedPrefixRun_partrec hq)).choose_spec

/-- Specialize the universal prefix runner at the instance `a`. -/
private noncomputable def prefixCode (q : A × ℕ → Prop) (hq : REPred q) (a : A) : Code :=
  Code.curry (prefixRunnerCode q hq) (Encodable.encode a)

/-- The specialization map is computable; the semidecider code is a fixed
constant and `Code.curry` is the constructive `s-m-n` operator. -/
private theorem computable_prefixCode (q : A × ℕ → Prop) (hq : REPred q) :
    Computable (prefixCode q hq) :=
  (Code.primrec₂_curry.comp (Primrec.const (prefixRunnerCode q hq))
    Primrec.encode).to_comp

/-- Exact semantics of the compiled code on one input. -/
private theorem eval_prefixCode_dom_iff (q : A × ℕ → Prop) (hq : REPred q)
    (a : A) (bound : ℕ) :
    (Code.eval (prefixCode q hq a) bound).Dom ↔
      ∀ n ≤ bound, q (a, n) := by
  rw [prefixCode, Code.eval_curry, eval_prefixRunnerCode]
  change (Part.bind
    (↑(Encodable.decode₂ (A × ℕ) (Nat.pair (Encodable.encode a) bound)) :
      Part (A × ℕ))
    fun x : A × ℕ => Part.map Encodable.encode (prefixRun q x.1 x.2)).Dom ↔ _
  have hpair : Nat.pair (Encodable.encode a) bound = Encodable.encode (a, bound) := by
    rw [Encodable.encode_prod_val, Encodable.encode_nat]
  rw [hpair, Encodable.decode₂_encode, Part.coe_some, Part.bind_some]
  change (prefixRun q a bound).Dom ↔ _
  exact prefixRun_dom_iff q a bound

/-- The compiled domain is infinite exactly when the entire r.e. row is
true. -/
private theorem infiniteDomain_prefixCode_iff (q : A × ℕ → Prop) (hq : REPred q)
    (a : A) :
    InfiniteDomain (prefixCode q hq a) ↔ ∀ n, q (a, n) := by
  constructor
  · intro hinfinite n
    have hunbounded : ∀ bound, ∃ k, bound < k ∧
        (Code.eval (prefixCode q hq a) k).Dom := by
      simpa only [InfiniteDomain, codeDomain, Set.mem_setOf_eq, and_comm] using
        (Set.infinite_iff_exists_gt.mp hinfinite)
    obtain ⟨k, hnk, hk⟩ := hunbounded n
    exact (eval_prefixCode_dom_iff q hq a k).mp hk n (Nat.le_of_lt hnk)
  · intro hall
    rw [InfiniteDomain, Set.infinite_iff_exists_gt]
    intro bound
    refine ⟨bound + 1, ?_, by omega⟩
    exact (eval_prefixCode_dom_iff q hq a (bound + 1)).mpr fun n _ => hall n

/-- Every `Π⁰₂` predicate, on any effective carrier, computably many-one
reduces to infinitude of a partial-recursive program domain. -/
theorem pi02_manyOne_infiniteDomain {p : A → Prop} (hp : Pi02 p) :
    p ≤₀ InfiniteDomain := by
  obtain ⟨q, hq, hpq⟩ := hp
  refine ⟨prefixCode q hq, computable_prefixCode q hq, fun a => ?_⟩
  exact (hpq a).trans (infiniteDomain_prefixCode_iff q hq a).symm

end PrefixCompiler

/-- Infinitude of a partial-recursive program domain is `Π⁰₂`-hard. -/
theorem infiniteDomain_pi02Hard : Pi02Hard InfiniteDomain :=
  fun _ hp => pi02_manyOne_infiniteDomain hp

/-- Infinitude of a partial-recursive program domain is `Π⁰₂`-complete. -/
theorem infiniteDomain_pi02Complete : Pi02Complete InfiniteDomain :=
  ⟨infiniteDomain_pi02, infiniteDomain_pi02Hard⟩

/-- Finiteness of a partial-recursive program domain is `Σ⁰₂`-hard. -/
theorem finiteDomain_sigma02Hard : Sigma02Hard FiniteDomain := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ :=
    pi02_manyOne_infiniteDomain (p := fun n => ¬ p n) hp
  refine ⟨f, hf, fun n => ?_⟩
  have h := not_congr (hcorrect n)
  classical
  simpa only [not_not, FiniteDomain, InfiniteDomain, Set.Infinite] using h

/-- Finiteness of a partial-recursive program domain is `Σ⁰₂`-complete. -/
theorem finiteDomain_sigma02Complete : Sigma02Complete FiniteDomain :=
  ⟨finiteDomain_sigma02, finiteDomain_sigma02Hard⟩

end SecondLevelIndexSets
end GroupApproximation
