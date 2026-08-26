import GroupApproximation.Computability.SoficMicrostateNormalForm
import GroupApproximation.Computability.SoficRecognitionSecondLevel
import GroupApproximation.Computability.WordProblemRE

/-!
# A `Π⁰₂` upper bound for recognising soficity of a finite presentation

`Computability.SoficMicrostateNormalForm` rewrites soficity of a coded group
as `∀ W k, Answers c W k`, where a challenge `(W, k)` is answered either by a
recursively enumerable search for a trivial word or by a permutation
microstate.  This file effectivises the second disjunct and reads off the
arithmetical bound.

Unlike the operator-MF analogue (`Computability.MFRecognitionPi02`), no
approximation is needed.  A permutation of `{0, …, m}` is exactly a list of
naturals; the normalized Hamming distance of a word's value from the identity
is the exact rational `movedCount / (m+1)`; and the two inequalities a
challenge asks about,

```text
  movedCount / (m + 1) ≤ 1 / (k + 1)      movedCount / (m + 1) ≥ 1 / 2
```

clear their denominators into `movedCount * (k+1) ≤ m+1` and
`m+1 ≤ 2 * movedCount`, which are decidable comparisons of naturals.  So the
microstate disjunct is an existential over a `Primcodable` type with a
primitive recursive Boolean matrix, hence `Σ⁰₁`; the void disjunct is `Σ⁰₁` by
`WordProblemRE.rePred_wordProblemPred`; and a universal quantifier over
challenges in front of a `Σ⁰₁` matrix is `Π⁰₂`.

## Totalisation

Two choices keep every syntactic operation a plain function of the raw data,
so that no partiality has to be tracked.

* A table entry is read as `min (t.getD x 0) m`, so every list of naturals
  names a function `{0, …, m} → {0, …, m}`; a genuine permutation table has
  entries `≤ m` and is unaffected.
* A certificate carries, for each generator, a forward table **and** a
  backward table, and the check verifies that the two composites are the
  identity table.  A two-sided inverse is a bijection, so the permutation is
  obtained without any decision procedure for injectivity.

## What is proved

* `passes_iff_exists_cert` --- the microstate disjunct is a certificate
  search.
* `rePred_answers` --- one challenge being answered is recursively enumerable.
* `pi02_isSofic` / `sigma02_not_isSofic` --- the arithmetical bounds.
* `sofic_fp_strict_position` --- the bound together with the unconditional
  non-enumerability of the negative side.

This file proves the upper bound only.  Hardness for *recursively enumerated*
presentations is `Computability.SoficRecognitionSecondLevel`; no completeness
claim for finite presentation codes is made here.

## Research nodes

* `research/sofic-recognition-has-a-pi2-upper-bound.md`
* `research/sofic-recognition-finite-presentations-arithmetical-position.md`

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace SoficRecognitionPi02

open ArithmeticalHierarchy
open PresentationCodes AdianRabinWordProblem RawWord
open SoficMicrostateNormalForm

/-! ## Lists indexed by a range -/

/-- Two functions agree on a list exactly when they agree after mapping. -/
theorem map_eq_map_iff {α β : Type} (l : List α) (f g : α → β) :
    l.map f = l.map g ↔ ∀ a ∈ l, f a = g a := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.cons.injEq, List.mem_cons, forall_eq_or_imp,
        ih]

/-- A range mapped to itself is exactly a pointwise fixed-point statement. -/
theorem map_range_eq_range_iff (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).map f = List.range n ↔ ∀ x, x < n → f x = x := by
  constructor
  · intro h x hx
    have h' : (List.range n).map f = (List.range n).map id := by
      rw [h, List.map_id]
    exact (map_eq_map_iff _ f id).1 h' x (List.mem_range.2 hx)
  · intro h
    have h' : (List.range n).map f = (List.range n).map id :=
      (map_eq_map_iff _ f id).2 fun a ha => h a (List.mem_range.1 ha)
    rw [h', List.map_id]

/-- Reading back an entry of a mapped range. -/
theorem getD_map_range {α : Type} (n : ℕ) (F : ℕ → α) (d : α) {x : ℕ}
    (hx : x < n) : ((List.range n).map F).getD x d = F x := by
  have hlen : x < ((List.range n).map F).length := by
    rw [List.length_map, List.length_range]; exact hx
  rw [List.getD_eq_getElem _ _ hlen]
  simp

/-! ## Summing a list of naturals

`natSum` is spelled out rather than taken from `List.sum` so that its
`Primrec` proof is a single application of `Primrec.list_foldr` against a
definitional unfolding. -/

/-- The sum of a list of naturals. -/
def natSum (l : List ℕ) : ℕ := l.foldr (· + ·) 0

@[simp] theorem natSum_nil : natSum [] = 0 := rfl

@[simp] theorem natSum_cons (a : ℕ) (l : List ℕ) :
    natSum (a :: l) = a + natSum l := rfl

theorem natSum_append : ∀ l₁ l₂ : List ℕ,
    natSum (l₁ ++ l₂) = natSum l₁ + natSum l₂
  | [], l₂ => by rw [List.nil_append, natSum_nil, Nat.zero_add]
  | a :: t, l₂ => by
      rw [List.cons_append, natSum_cons, natSum_cons, natSum_append t l₂,
        Nat.add_assoc]

theorem natSum_map_range (F : ℕ → ℕ) : ∀ n : ℕ,
    natSum ((List.range n).map F) = ∑ x ∈ Finset.range n, F x
  | 0 => by simp
  | (n + 1) => by
      rw [List.range_succ, List.map_append, natSum_append,
        natSum_map_range F n, Finset.sum_range_succ]
      simp

/-! ## Tables -/

/-- A table entry, totalised: an out-of-range index or an oversized value is
clamped into `{0, …, m}`, so every list of naturals names a function.  A
genuine permutation table has entries `≤ m` and is unaffected. -/
def act (m : ℕ) (t : List ℕ) (x : ℕ) : ℕ := min (t.getD x 0) m

theorem act_le (m : ℕ) (t : List ℕ) (x : ℕ) : act m t x ≤ m := min_le_right _ _

theorem act_lt (m : ℕ) (t : List ℕ) (x : ℕ) : act m t x < m + 1 :=
  Nat.lt_succ_of_le (act_le m t x)

/-- The identity table on `{0, …, m}`. -/
def idTable (m : ℕ) : List ℕ := List.range (m + 1)

/-- The table of the composite `t ∘ s`. -/
def compTable (m : ℕ) (t s : List ℕ) : List ℕ :=
  (List.range (m + 1)).map fun x => act m t (act m s x)

theorem act_idTable (m x : ℕ) (hx : x < m + 1) : act m (idTable m) x = x := by
  have hlen : x < (idTable m).length := by
    rw [idTable, List.length_range]; exact hx
  have hget : (idTable m).getD x 0 = x := by
    rw [List.getD_eq_getElem _ _ hlen, idTable]
    simp
  rw [act, hget]
  omega

theorem act_compTable (m : ℕ) (t s : List ℕ) {x : ℕ} (hx : x < m + 1) :
    act m (compTable m t s) x = act m t (act m s x) := by
  have hget : (compTable m t s).getD x 0 = act m t (act m s x) := by
    rw [compTable]
    exact getD_map_range (m + 1) _ 0 hx
  rw [act, hget]
  have h := act_le m t (act m s x)
  omega

/-- Two tables are mutually inverse when both composites are the identity. -/
def InverseTables (m : ℕ) (t s : List ℕ) : Prop :=
  compTable m t s = idTable m ∧ compTable m s t = idTable m

theorem act_inverse_left {m : ℕ} {t s : List ℕ} (h : InverseTables m t s)
    {x : ℕ} (hx : x < m + 1) : act m s (act m t x) = x := by
  have h2 : (List.range (m + 1)).map (fun y => act m s (act m t y))
      = List.range (m + 1) := by
    have h' := h.2
    rw [compTable, idTable] at h'
    exact h'
  exact (map_range_eq_range_iff (m + 1) _).1 h2 x hx

theorem act_inverse_right {m : ℕ} {t s : List ℕ} (h : InverseTables m t s)
    {x : ℕ} (hx : x < m + 1) : act m t (act m s x) = x := by
  have h2 : (List.range (m + 1)).map (fun y => act m t (act m s y))
      = List.range (m + 1) := by
    have h' := h.1
    rw [compTable, idTable] at h'
    exact h'
  exact (map_range_eq_range_iff (m + 1) _).1 h2 x hx

/-! ## The model on `{0, …, m}` -/

/-- The finite model on `{0, …, m}`.  Reducible, so that every statement about
`Fin (m + 1)` is a statement about it. -/
abbrev natModel (m : ℕ) : FiniteModel := ⟨Fin (m + 1), inferInstance, inferInstance⟩

theorem card_natModel (m : ℕ) : Fintype.card (natModel m) = m + 1 := by
  show Fintype.card (Fin (m + 1)) = m + 1
  exact Fintype.card_fin _

/-- The permutation named by a mutually inverse pair of tables. -/
def toPerm (m : ℕ) (t s : List ℕ) (h : InverseTables m t s) :
    Equiv.Perm (natModel m) where
  toFun := fun i => (⟨act m t i.val, act_lt m t i.val⟩ : Fin (m + 1))
  invFun := fun i => (⟨act m s i.val, act_lt m s i.val⟩ : Fin (m + 1))
  left_inv := fun i => Fin.val_injective (act_inverse_left h i.isLt)
  right_inv := fun i => Fin.val_injective (act_inverse_right h i.isLt)

@[simp] theorem toPerm_val (m : ℕ) (t s : List ℕ) (h : InverseTables m t s)
    (i : Fin (m + 1)) : ((toPerm m t s h) i).val = act m t i.val := rfl

@[simp] theorem toPerm_inv_val (m : ℕ) (t s : List ℕ)
    (h : InverseTables m t s) (i : Fin (m + 1)) :
    (((toPerm m t s h)⁻¹) i).val = act m s i.val := rfl

/-- The table of a permutation of `{0, …, m}`. -/
def tabOf (m : ℕ) (p : Equiv.Perm (natModel m)) : List ℕ :=
  List.ofFn fun i : Fin (m + 1) => (p i).val

theorem act_tabOf (m : ℕ) (p : Equiv.Perm (natModel m)) (i : Fin (m + 1)) :
    act m (tabOf m p) i.val = (p i).val := by
  have hlen : (i : ℕ) < (tabOf m p).length := by
    rw [tabOf, List.length_ofFn]; exact i.isLt
  have hget : (tabOf m p).getD i.val 0 = (p i).val := by
    rw [List.getD_eq_getElem _ _ hlen, tabOf]
    simp
  rw [act, hget]
  have h := (p i).isLt
  omega

theorem inverseTables_tabOf (m : ℕ) (p : Equiv.Perm (natModel m)) :
    InverseTables m (tabOf m p) (tabOf m p⁻¹) := by
  constructor
  · rw [compTable, idTable]
    refine (map_range_eq_range_iff (m + 1) _).2 fun x hx => ?_
    rw [show x = ((⟨x, hx⟩ : Fin (m + 1)) : ℕ) from rfl,
      act_tabOf m p⁻¹ ⟨x, hx⟩, act_tabOf m p (p⁻¹ ⟨x, hx⟩)]
    simp
  · rw [compTable, idTable]
    refine (map_range_eq_range_iff (m + 1) _).2 fun x hx => ?_
    rw [show x = ((⟨x, hx⟩ : Fin (m + 1)) : ℕ) from rfl,
      act_tabOf m p ⟨x, hx⟩, act_tabOf m p⁻¹ (p ⟨x, hx⟩)]
    simp

/-! ## Counting moved points -/

/-- The number of points a table moves. -/
def movedCount (m : ℕ) (t : List ℕ) : ℕ :=
  natSum ((List.range (m + 1)).map fun x => if act m t x = x then 0 else 1)

/-- **Hamming distance from the identity is an exact rational.** -/
theorem hammingDistance_eq_movedCount (m : ℕ) (P : Equiv.Perm (natModel m))
    (T : List ℕ) (hP : ∀ i : Fin (m + 1), (P i).val = act m T i.val) :
    hammingDistance (natModel m) P 1 = (movedCount m T : ℝ) / ((m : ℝ) + 1) := by
  classical
  have hset : hammingDisagreement P (1 : Equiv.Perm (natModel m))
      = Finset.univ.filter fun i : Fin (m + 1) => act m T i.val ≠ i.val := by
    ext i
    rw [mem_hammingDisagreement, Finset.mem_filter]
    constructor
    · intro hne
      refine ⟨Finset.mem_univ _, fun hcon => hne ?_⟩
      refine Fin.val_injective ?_
      rw [hP i, hcon]
      rfl
    · rintro ⟨-, hne⟩ hcon
      exact hne (by rw [← hP i, hcon])
  have hcard : (hammingDisagreement P (1 : Equiv.Perm (natModel m))).card
      = movedCount m T := by
    rw [hset, Finset.card_filter, movedCount, natSum_map_range,
      ← Fin.sum_univ_eq_sum_range (fun x => if act m T x = x then 0 else 1)
        (m + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hcase : act m T i.val = i.val
    · simp [hcase]
    · simp [hcase]
  rw [hammingDistance, hcard, card_natModel, Nat.cast_add, Nat.cast_one]

/-! ## Certificates -/

/-- The effective data of a permutation microstate: a carrier size offset by
one, and for each generator a forward table paired with a backward table. -/
abbrev PermCert : Type := ℕ × List (List ℕ × List ℕ)

/-- The table pair a certificate assigns to a raw letter index. -/
def certGen (c : PresentationCode) (cert : PermCert) (i : ℕ) :
    List ℕ × List ℕ :=
  cert.2.getD (i % (c.1 + 1)) ([], [])

/-- Well-formedness: every generator's two tables are mutually inverse. -/
def CertValid (c : PresentationCode) (cert : PermCert) : Prop :=
  ∀ i, i < c.1 + 1 →
    InverseTables cert.1 (certGen c cert i).1 (certGen c cert i).2

/-- A raw letter index and its reduction name the same table pair. -/
theorem certGen_letterOf (c : PresentationCode) (cert : PermCert) (n : ℕ) :
    certGen c cert ((letterOf c n : Fin (genCount c)) : ℕ)
      = certGen c cert n := by
  rw [certGen, certGen]
  congr 1
  show n % (c.1 + 1) % (c.1 + 1) = n % (c.1 + 1)
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos _))

/-- The permutation microstate a valid certificate names. -/
def certMicrostate (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) : PermMicrostate c where
  carrier := natModel cert.1
  nonempty := by rw [card_natModel]; exact Nat.succ_pos _
  gen := fun j => toPerm cert.1 (certGen c cert (j : ℕ)).1
    (certGen c cert (j : ℕ)).2 (h (j : ℕ) j.isLt)

theorem certMicrostate_gen_val (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (j : Fin (genCount c)) (i : Fin (cert.1 + 1)) :
    (((certMicrostate c cert h).gen j) i).val
      = act cert.1 (certGen c cert (j : ℕ)).1 i.val := rfl

theorem certMicrostate_gen_inv_val (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (j : Fin (genCount c)) (i : Fin (cert.1 + 1)) :
    ((((certMicrostate c cert h).gen j)⁻¹) i).val
      = act cert.1 (certGen c cert (j : ℕ)).2 i.val := rfl

/-! ## Evaluating a word in a certificate -/

/-- The table of one signed letter. -/
def letterTable (c : PresentationCode) (cert : PermCert) (p : ℕ × Bool) :
    List ℕ :=
  bif p.2 then (certGen c cert p.1).1 else (certGen c cert p.1).2

/-- The table of a raw word. -/
def wordTable (c : PresentationCode) (cert : PermCert)
    (w : List (ℕ × Bool)) : List ℕ :=
  w.foldr (fun p acc => compTable cert.1 (letterTable c cert p) acc)
    (idTable cert.1)

@[simp] theorem wordTable_nil (c : PresentationCode) (cert : PermCert) :
    wordTable c cert [] = idTable cert.1 := rfl

@[simp] theorem wordTable_cons (c : PresentationCode) (cert : PermCert)
    (p : ℕ × Bool) (w : List (ℕ × Bool)) :
    wordTable c cert (p :: w)
      = compTable cert.1 (letterTable c cert p) (wordTable c cert w) := rfl

theorem hom_letter_val (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (p : ℕ × Bool) (j : Fin (cert.1 + 1)) :
    act cert.1 (letterTable c cert p) j.val
      = (((certMicrostate c cert h).hom (wordOf c [p])) j).val := by
  obtain ⟨n, s⟩ := p
  have hgen : certGen c cert ((letterOf c n : Fin (genCount c)) : ℕ)
      = certGen c cert n := certGen_letterOf c cert n
  cases s with
  | true =>
      rw [wordOf_pos, PermMicrostate.hom_of, certMicrostate_gen_val, hgen]
      rfl
  | false =>
      rw [wordOf_neg, map_inv, PermMicrostate.hom_of,
        certMicrostate_gen_inv_val, hgen]
      rfl

theorem act_wordTable_val (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) :
    ∀ (w : List (ℕ × Bool)) (i : Fin (cert.1 + 1)),
      act cert.1 (wordTable c cert w) i.val
        = (((certMicrostate c cert h).hom (wordOf c w)) i).val
  | [], i => by
      rw [wordTable_nil, wordOf_nil, map_one]
      exact act_idTable cert.1 i.val i.isLt
  | p :: w, i => by
      have hcons : wordOf c (p :: w) = wordOf c [p] * wordOf c w := by
        show wordOf c ([p] ++ w) = _
        rw [wordOf_append]
      rw [hcons, map_mul, Equiv.Perm.mul_apply, wordTable_cons,
        act_compTable cert.1 _ _ i.isLt, act_wordTable_val c cert h w i]
      exact hom_letter_val c cert h p _

/-- **The certificate computes the displacement exactly.** -/
theorem len_certMicrostate (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (w : List (ℕ × Bool)) :
    (certMicrostate c cert h).len w
      = (movedCount cert.1 (wordTable c cert w) : ℝ) / ((cert.1 : ℝ) + 1) := by
  rw [PermMicrostate.len_def]
  exact hammingDistance_eq_movedCount cert.1
    ((certMicrostate c cert h).hom (wordOf c w)) (wordTable c cert w)
    fun i => (act_wordTable_val c cert h w i).symm

/-! ## The certificate read off a microstate -/

/-- The certificate assembled from a family of permutations of `{0, …, m}`. -/
def certOf (c : PresentationCode) (m : ℕ)
    (g : Fin (genCount c) → Equiv.Perm (natModel m)) : PermCert :=
  (m, List.ofFn fun j : Fin (genCount c) => (tabOf m (g j), tabOf m (g j)⁻¹))

theorem certGen_certOf (c : PresentationCode) (m : ℕ)
    (g : Fin (genCount c) → Equiv.Perm (natModel m)) (j : Fin (genCount c)) :
    certGen c (certOf c m g) (j : ℕ) = (tabOf m (g j), tabOf m (g j)⁻¹) := by
  rw [certGen, certOf]
  have hj : (j : ℕ) % (c.1 + 1) = (j : ℕ) := Nat.mod_eq_of_lt j.isLt
  rw [hj]
  have hlen : (j : ℕ) <
      (List.ofFn fun j : Fin (genCount c) =>
        (tabOf m (g j), tabOf m (g j)⁻¹)).length := by
    rw [List.length_ofFn]; exact j.isLt
  rw [List.getD_eq_getElem _ _ hlen]
  simp

theorem certValid_certOf (c : PresentationCode) (m : ℕ)
    (g : Fin (genCount c) → Equiv.Perm (natModel m)) :
    CertValid c (certOf c m g) := by
  intro i hi
  have hi' : i = ((⟨i, hi⟩ : Fin (genCount c)) : ℕ) := rfl
  rw [hi', certGen_certOf]
  exact inverseTables_tabOf m (g ⟨i, hi⟩)

theorem certOf_gen (c : PresentationCode) (m : ℕ)
    (g : Fin (genCount c) → Equiv.Perm (natModel m)) (j : Fin (genCount c)) :
    (certMicrostate c (certOf c m g) (certValid_certOf c m g)).gen j = g j := by
  refine Equiv.ext fun i => Fin.val_injective ?_
  rw [certMicrostate_gen_val, certGen_certOf]
  exact act_tabOf m (g j) i

theorem certOf_hom (c : PresentationCode) (m : ℕ)
    (g : Fin (genCount c) → Equiv.Perm (natModel m))
    (x : FreeGroup (Fin (genCount c))) :
    (certMicrostate c (certOf c m g) (certValid_certOf c m g)).hom x
      = FreeGroup.lift g x := by
  have hEq : (certMicrostate c (certOf c m g) (certValid_certOf c m g)).hom
      = FreeGroup.lift g := by
    refine FreeGroup.ext_hom _ _ fun j => ?_
    rw [PermMicrostate.hom_of, FreeGroup.lift_apply_of, certOf_gen]
  rw [hEq]

/-! ## Transporting a microstate to `{0, …, m}` -/

/-- Conjugating permutations along a bijection of models. -/
def permCongrHom {X Y : Type} (e : X ≃ Y) : Equiv.Perm X →* Equiv.Perm Y where
  toFun p := (e.symm.trans p).trans e
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp

@[simp] theorem permCongrHom_apply {X Y : Type} (e : X ≃ Y)
    (p : Equiv.Perm X) (y : Y) : (permCongrHom e p) y = e (p (e.symm y)) := rfl

theorem hammingDistance_permCongrHom (X Y : FiniteModel) (e : X ≃ Y)
    (p q : Equiv.Perm X) :
    hammingDistance Y (permCongrHom e p) (permCongrHom e q)
      = hammingDistance X p q := by
  classical
  have himg : hammingDisagreement (permCongrHom e p) (permCongrHom e q)
      = (hammingDisagreement p q).map e.toEmbedding := by
    ext y
    rw [mem_hammingDisagreement, Finset.mem_map_equiv, mem_hammingDisagreement,
      permCongrHom_apply, permCongrHom_apply]
    exact not_congr e.apply_eq_iff_eq
  rw [hammingDistance, hammingDistance, himg, Finset.card_map,
    Fintype.card_congr e.symm]

/-! ## The microstate disjunct is a certificate search -/

/-- Compare `movedCount / (m+1)` with `1 / (k+1)` by clearing denominators. -/
theorem div_le_div_iff_nat {a m k : ℕ} :
    (a : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) ↔ a * (k + 1) ≤ m + 1 := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ hm hk, one_mul]
  constructor
  · intro h
    have : ((a * (k + 1) : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((a * (k + 1) : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

/-- Compare `movedCount / (m+1)` with `1/2` by clearing denominators. -/
theorem half_le_div_iff_nat {a m : ℕ} :
    (1 : ℝ) / 2 ≤ (a : ℝ) / ((m : ℝ) + 1) ↔ m + 1 ≤ 2 * a := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hm, one_mul]
  constructor
  · intro h
    have : ((m + 1 : ℕ) : ℝ) ≤ ((2 * a : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((m + 1 : ℕ) : ℝ) ≤ ((2 * a : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

/-- The relator clause, as a Boolean test. -/
def relatorOk (c : PresentationCode) (cert : PermCert) (k : ℕ)
    (r : List (ℕ × Bool)) : Bool :=
  decide (movedCount cert.1 (wordTable c cert r) * (k + 1) ≤ cert.1 + 1)

/-- The separation clause, as a Boolean test. -/
def wordOk (c : PresentationCode) (cert : PermCert) (w : List (ℕ × Bool)) :
    Bool :=
  decide (cert.1 + 1 ≤ 2 * movedCount cert.1 (wordTable c cert w))

/-- The well-formedness clause, as a Boolean test. -/
def validOk (c : PresentationCode) (cert : PermCert) (i : ℕ) : Bool :=
  decide (compTable cert.1 (certGen c cert i).1 (certGen c cert i).2
      = idTable cert.1) &&
    decide (compTable cert.1 (certGen c cert i).2 (certGen c cert i).1
      = idTable cert.1)

/-- **The certificate checker.**  Every clause is a comparison of naturals or
an equality of lists of naturals, so this is a total Boolean function of raw
data. -/
def passesCheck (x : PresentationCode × List (List (ℕ × Bool)) × ℕ)
    (cert : PermCert) : Bool :=
  (decide ((List.range (x.1.1 + 1)).map (validOk x.1 cert)
        = (List.range (x.1.1 + 1)).map fun _ => true) &&
      decide (x.1.2.map (relatorOk x.1 cert x.2.2)
        = x.1.2.map fun _ => true)) &&
    decide (x.2.1.map (wordOk x.1 cert) = x.2.1.map fun _ => true)

theorem passesCheck_eq_true_iff
    (x : PresentationCode × List (List (ℕ × Bool)) × ℕ) (cert : PermCert) :
    passesCheck x cert = true ↔
      (CertValid x.1 cert ∧
        (∀ r ∈ x.1.2,
          movedCount cert.1 (wordTable x.1 cert r) * (x.2.2 + 1)
            ≤ cert.1 + 1) ∧
        ∀ w ∈ x.2.1,
          cert.1 + 1 ≤ 2 * movedCount cert.1 (wordTable x.1 cert w)) := by
  rw [passesCheck, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, decide_eq_true_iff, map_eq_map_iff, map_eq_map_iff,
    map_eq_map_iff]
  constructor
  · rintro ⟨⟨hv, hr⟩, hw⟩
    refine ⟨fun i hi => ?_, fun r hrmem => ?_, fun w hwmem => ?_⟩
    · have h := hv i (List.mem_range.2 hi)
      rw [validOk, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        at h
      exact h
    · have h := hr r hrmem
      rwa [relatorOk, decide_eq_true_iff] at h
    · have h := hw w hwmem
      rwa [wordOk, decide_eq_true_iff] at h
  · rintro ⟨hv, hr, hw⟩
    refine ⟨⟨fun i hi => ?_, fun r hrmem => ?_⟩, fun w hwmem => ?_⟩
    · rw [validOk, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      exact hv i (List.mem_range.1 hi)
    · rw [relatorOk, decide_eq_true_iff]
      exact hr r hrmem
    · rw [wordOk, decide_eq_true_iff]
      exact hw w hwmem

/-- **The microstate disjunct is a certificate search.** -/
theorem passes_iff_exists_cert (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) :
    (∃ M : PermMicrostate c, Passes c W k M)
      ↔ ∃ cert : PermCert, passesCheck (c, W, k) cert = true := by
  constructor
  · rintro ⟨M, hrel, hsep⟩
    classical
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card M.carrier = m + 1 :=
      ⟨Fintype.card M.carrier - 1, by omega⟩
    obtain e : M.carrier ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
    set g : Fin (genCount c) → Equiv.Perm (natModel m) :=
      fun j => permCongrHom e (M.gen j) with hg
    have hlift : FreeGroup.lift g = (permCongrHom e).comp M.hom := by
      refine FreeGroup.ext_hom _ _ fun j => ?_
      rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, PermMicrostate.hom_of, hg]
    have hlen : ∀ w : List (ℕ × Bool),
        (certMicrostate c (certOf c m g) (certValid_certOf c m g)).len w
          = M.len w := by
      intro w
      rw [PermMicrostate.len_def, PermMicrostate.len_def,
        certOf_hom c m g (wordOf c w), hlift, MonoidHom.comp_apply,
        show (1 : Equiv.Perm (natModel m)) = permCongrHom e 1 from
          (map_one (permCongrHom e)).symm,
        hammingDistance_permCongrHom]
    refine ⟨certOf c m g, (passesCheck_eq_true_iff (c, W, k) _).2
      ⟨certValid_certOf c m g, ?_, ?_⟩⟩
    · intro r hr
      have h := hrel r hr
      rw [← hlen r, len_certMicrostate] at h
      exact div_le_div_iff_nat.1 h
    · intro w hw
      have h := hsep w hw
      rw [← hlen w, len_certMicrostate] at h
      exact half_le_div_iff_nat.1 h
  · rintro ⟨cert, hcert⟩
    obtain ⟨hvalid, hrel, hsep⟩ := (passesCheck_eq_true_iff (c, W, k) cert).1 hcert
    refine ⟨certMicrostate c cert hvalid, fun r hr => ?_, fun w hw => ?_⟩
    · rw [len_certMicrostate]
      exact div_le_div_iff_nat.2 (hrel r hr)
    · rw [len_certMicrostate]
      exact half_le_div_iff_nat.2 (hsep w hw)

/-! ## The checker is primitive recursive -/

section Effective

variable {α : Type} [Primcodable α]

theorem primrec_act {fm : α → ℕ} {ft : α → List ℕ} {fx : α → ℕ}
    (hm : Primrec fm) (ht : Primrec ft) (hx : Primrec fx) :
    Primrec fun a => act (fm a) (ft a) (fx a) :=
  (Primrec.nat_min.comp ((Primrec.list_getD (0 : ℕ)).comp ht hx) hm).of_eq
    fun _ => rfl

theorem primrec_idTable {fm : α → ℕ} (hm : Primrec fm) :
    Primrec fun a => idTable (fm a) :=
  (Primrec.list_range.comp (Primrec.succ.comp hm)).of_eq fun _ => rfl

theorem primrec_compTable {fm : α → ℕ} {ft fs : α → List ℕ}
    (hm : Primrec fm) (ht : Primrec ft) (hs : Primrec fs) :
    Primrec fun a => compTable (fm a) (ft a) (fs a) := by
  have hrange : Primrec fun a => List.range (fm a + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hm)
  have hinner : Primrec₂ fun (a : α) (x : ℕ) =>
      act (fm a) (ft a) (act (fm a) (fs a) x) :=
    (primrec_act (hm.comp Primrec.fst) (ht.comp Primrec.fst)
      (primrec_act (hm.comp Primrec.fst) (hs.comp Primrec.fst)
        Primrec.snd)).to₂
  exact (Primrec.list_map hrange hinner).of_eq fun _ => rfl

theorem primrec_natSum : Primrec natSum :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun _ => rfl

theorem primrec_movedCount {fm : α → ℕ} {ft : α → List ℕ}
    (hm : Primrec fm) (ht : Primrec ft) :
    Primrec fun a => movedCount (fm a) (ft a) := by
  have hrange : Primrec fun a => List.range (fm a + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hm)
  have hcond : PrimrecPred fun z : α × ℕ =>
      act (fm z.1) (ft z.1) z.2 = z.2 :=
    Primrec.eq.comp (primrec_act (hm.comp Primrec.fst) (ht.comp Primrec.fst)
      Primrec.snd) Primrec.snd
  have hinner : Primrec₂ fun (a : α) (x : ℕ) =>
      if act (fm a) (ft a) x = x then 0 else 1 :=
    (Primrec.ite hcond (Primrec.const 0) (Primrec.const 1)).to₂
  exact (primrec_natSum.comp (Primrec.list_map hrange hinner)).of_eq
    fun _ => rfl

theorem primrec_certGen {fc : α → PresentationCode} {fcert : α → PermCert}
    {fi : α → ℕ} (hc : Primrec fc) (hcert : Primrec fcert) (hi : Primrec fi) :
    Primrec fun a => certGen (fc a) (fcert a) (fi a) :=
  ((Primrec.list_getD (([], []) : List ℕ × List ℕ)).comp
    (Primrec.snd.comp hcert)
    (Primrec.nat_mod.comp hi
      (Primrec.succ.comp (Primrec.fst.comp hc)))).of_eq fun _ => rfl

theorem primrec_letterTable {fc : α → PresentationCode} {fcert : α → PermCert}
    {fp : α → ℕ × Bool} (hc : Primrec fc) (hcert : Primrec fcert)
    (hp : Primrec fp) :
    Primrec fun a => letterTable (fc a) (fcert a) (fp a) :=
  (Primrec.cond (Primrec.snd.comp hp)
    (Primrec.fst.comp (primrec_certGen hc hcert (Primrec.fst.comp hp)))
    (Primrec.snd.comp
      (primrec_certGen hc hcert (Primrec.fst.comp hp)))).of_eq fun _ => rfl

theorem primrec_wordTable {fc : α → PresentationCode} {fcert : α → PermCert}
    {fw : α → List (ℕ × Bool)} (hc : Primrec fc) (hcert : Primrec fcert)
    (hw : Primrec fw) :
    Primrec fun a => wordTable (fc a) (fcert a) (fw a) := by
  have hstep : Primrec₂ fun (a : α) (z : (ℕ × Bool) × List ℕ) =>
      compTable (fcert a).1 (letterTable (fc a) (fcert a) z.1) z.2 :=
    (primrec_compTable (Primrec.fst.comp (hcert.comp Primrec.fst))
      (primrec_letterTable (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hw
    (primrec_idTable (Primrec.fst.comp hcert)) hstep).of_eq fun _ => rfl

theorem primrec_validOk {fc : α → PresentationCode} {fcert : α → PermCert}
    {fi : α → ℕ} (hc : Primrec fc) (hcert : Primrec fcert) (hi : Primrec fi) :
    Primrec fun a => validOk (fc a) (fcert a) (fi a) := by
  have hm : Primrec fun a : α => (fcert a).1 := Primrec.fst.comp hcert
  have hgen := primrec_certGen hc hcert hi
  have h1 : Primrec fun a : α =>
      compTable (fcert a).1 (certGen (fc a) (fcert a) (fi a)).1
        (certGen (fc a) (fcert a) (fi a)).2 :=
    primrec_compTable hm (Primrec.fst.comp hgen) (Primrec.snd.comp hgen)
  have h2 : Primrec fun a : α =>
      compTable (fcert a).1 (certGen (fc a) (fcert a) (fi a)).2
        (certGen (fc a) (fcert a) (fi a)).1 :=
    primrec_compTable hm (Primrec.snd.comp hgen) (Primrec.fst.comp hgen)
  have hid : Primrec fun a : α => idTable (fcert a).1 := primrec_idTable hm
  exact (Primrec.and.comp (Primrec.eq.comp h1 hid).decide
    (Primrec.eq.comp h2 hid).decide).of_eq fun _ => rfl

theorem primrec_relatorOk {fc : α → PresentationCode} {fcert : α → PermCert}
    {fk : α → ℕ} {fr : α → List (ℕ × Bool)} (hc : Primrec fc)
    (hcert : Primrec fcert) (hk : Primrec fk) (hr : Primrec fr) :
    Primrec fun a => relatorOk (fc a) (fcert a) (fk a) (fr a) := by
  have hcount : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTable (fc a) (fcert a) (fr a)) :=
    primrec_movedCount (Primrec.fst.comp hcert)
      (primrec_wordTable hc hcert hr)
  have hleft : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTable (fc a) (fcert a) (fr a)) * (fk a + 1) :=
    Primrec.nat_mul.comp hcount (Primrec.succ.comp hk)
  have hright : Primrec fun a : α => (fcert a).1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp hcert)
  exact (Primrec.nat_le.comp hleft hright).decide.of_eq fun _ => rfl

theorem primrec_wordOk {fc : α → PresentationCode} {fcert : α → PermCert}
    {fw : α → List (ℕ × Bool)} (hc : Primrec fc) (hcert : Primrec fcert)
    (hw : Primrec fw) :
    Primrec fun a => wordOk (fc a) (fcert a) (fw a) := by
  have hcount : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTable (fc a) (fcert a) (fw a)) :=
    primrec_movedCount (Primrec.fst.comp hcert)
      (primrec_wordTable hc hcert hw)
  have hright : Primrec fun a : α =>
      2 * movedCount (fcert a).1 (wordTable (fc a) (fcert a) (fw a)) :=
    Primrec.nat_mul.comp (Primrec.const 2) hcount
  have hleft : Primrec fun a : α => (fcert a).1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp hcert)
  exact (Primrec.nat_le.comp hleft hright).decide.of_eq fun _ => rfl

end Effective

/-- The checker input type, abbreviated so the `Primrec` proof stays
readable. -/
abbrev CheckInput : Type := PresentationCode × List (List (ℕ × Bool)) × ℕ

theorem primrec_passesCheck : Primrec₂ passesCheck := by
  have hc : Primrec fun z : CheckInput × PermCert => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hW : Primrec fun z : CheckInput × PermCert => z.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec fun z : CheckInput × PermCert => z.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hcert : Primrec fun z : CheckInput × PermCert => z.2 := Primrec.snd
  have hrange : Primrec fun z : CheckInput × PermCert =>
      List.range (z.1.1.1 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp hc))
  have hrelators : Primrec fun z : CheckInput × PermCert => z.1.1.2 :=
    Primrec.snd.comp hc
  have hvalidList : Primrec fun z : CheckInput × PermCert =>
      (List.range (z.1.1.1 + 1)).map (validOk z.1.1 z.2) :=
    Primrec.list_map hrange
      (primrec_validOk (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        Primrec.snd).to₂
  have hrelList : Primrec fun z : CheckInput × PermCert =>
      z.1.1.2.map (relatorOk z.1.1 z.2 z.1.2.2) :=
    Primrec.list_map hrelators
      (primrec_relatorOk (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        (hk.comp Primrec.fst) Primrec.snd).to₂
  have hwordList : Primrec fun z : CheckInput × PermCert =>
      z.1.2.1.map (wordOk z.1.1 z.2) :=
    Primrec.list_map hW
      (primrec_wordOk (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        Primrec.snd).to₂
  have htrueRange : Primrec fun z : CheckInput × PermCert =>
      (List.range (z.1.1.1 + 1)).map fun _ : ℕ => true :=
    Primrec.list_map hrange (Primrec.const true).to₂
  have htrueRel : Primrec fun z : CheckInput × PermCert =>
      z.1.1.2.map fun _ : List (ℕ × Bool) => true :=
    Primrec.list_map hrelators (Primrec.const true).to₂
  have htrueWord : Primrec fun z : CheckInput × PermCert =>
      z.1.2.1.map fun _ : List (ℕ × Bool) => true :=
    Primrec.list_map hW (Primrec.const true).to₂
  exact (Primrec.and.comp
    (Primrec.and.comp (Primrec.eq.comp hvalidList htrueRange).decide
      (Primrec.eq.comp hrelList htrueRel).decide)
    (Primrec.eq.comp hwordList htrueWord).decide).of_eq fun _ => rfl

/-! ## Answering a challenge is recursively enumerable -/

/-- The search space for one challenge: a raw word together with a word-problem
derivation certificate for the void disjunct, paired with a permutation
certificate for the microstate disjunct. -/
abbrev AnswerData : Type :=
  (List (ℕ × Bool) × WordProblemRE.SearchData) × PermCert

/-- The matrix of the answer search. -/
def answerCheck (x : CheckInput) (b : AnswerData) : Bool :=
  (decide (b.1.1 ∈ x.2.1) && WordProblemRE.searchCheck (x.1, b.1.1) b.1.2)
    || passesCheck x b.2

theorem exists_or_of_pair {α β : Type} [Inhabited α] [Inhabited β]
    (f : α → Bool) (g : β → Bool) :
    (∃ b : α × β, (f b.1 || g b.2) = true)
      ↔ (∃ a, f a = true) ∨ ∃ b, g b = true := by
  constructor
  · rintro ⟨⟨a, b⟩, hb⟩
    rw [Bool.or_eq_true] at hb
    rcases hb with h | h
    · exact Or.inl ⟨a, h⟩
    · exact Or.inr ⟨b, h⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨(a, default), by simp [ha]⟩
    · exact ⟨(default, b), by simp [hb]⟩

theorem exists_void_iff (c : PresentationCode) (W : List (List (ℕ × Bool))) :
    (∃ y : List (ℕ × Bool) × WordProblemRE.SearchData,
        (decide (y.1 ∈ W) && WordProblemRE.searchCheck (c, y.1) y.2) = true)
      ↔ ∃ w ∈ W, WordProblem c w := by
  constructor
  · rintro ⟨⟨w, p⟩, hb⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at hb
    refine ⟨w, hb.1, ?_⟩
    have := (WordProblemRE.wordProblemPred_iff_exists (c, w)).2 ⟨p, hb.2⟩
    exact this
  · rintro ⟨w, hw, htriv⟩
    obtain ⟨p, hp⟩ :=
      (WordProblemRE.wordProblemPred_iff_exists (c, w)).1 htriv
    exact ⟨(w, p), by rw [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hw, hp⟩⟩

theorem answerCheck_iff (x : CheckInput) :
    (∃ b : AnswerData, answerCheck x b = true) ↔ Answers x.1 x.2.1 x.2.2 := by
  rw [Answers, answerCheck]
  rw [show (∃ b : AnswerData, ((decide (b.1.1 ∈ x.2.1) &&
      WordProblemRE.searchCheck (x.1, b.1.1) b.1.2) || passesCheck x b.2) = true)
      ↔ (∃ y : List (ℕ × Bool) × WordProblemRE.SearchData,
          (decide (y.1 ∈ x.2.1) &&
            WordProblemRE.searchCheck (x.1, y.1) y.2) = true) ∨
        ∃ cert : PermCert, passesCheck x cert = true from
      exists_or_of_pair _ _]
  rw [exists_void_iff]
  exact or_congr Iff.rfl (passes_iff_exists_cert x.1 x.2.1 x.2.2).symm

theorem primrec_answerCheck : Primrec₂ answerCheck := by
  have hmem : PrimrecPred fun z : CheckInput × AnswerData =>
      z.2.1.1 ∈ z.1.2.1 := by
    have h : PrimrecRel fun (L : List (List (ℕ × Bool)))
        (u : List (ℕ × Bool)) => ∃ a ∈ L, a = u :=
      PrimrecRel.exists_mem_list Primrec.eq
    refine (h.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).of_eq fun z => ?_
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      exact ⟨z.2.1.1, hz, rfl⟩
  have hsearch : Primrec fun z : CheckInput × AnswerData =>
      WordProblemRE.searchCheck (z.1.1, z.2.1.1) z.2.1.2 :=
    WordProblemRE.primrec_searchCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hpass : Primrec fun z : CheckInput × AnswerData =>
      passesCheck z.1 z.2.2 :=
    primrec_passesCheck.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (Primrec.or.comp (Primrec.and.comp hmem.decide hsearch) hpass).of_eq
    fun _ => rfl

/-- **Answering one challenge is recursively enumerable.** -/
theorem rePred_answers :
    REPred fun x : PresentationCode × (List (List (ℕ × Bool)) × ℕ) =>
      Answers x.1 x.2.1 x.2.2 :=
  (WordProblemRE.rePred_exists_eq_true primrec_answerCheck.to_comp).of_eq
    fun x => (answerCheck_iff x).symm

/-! ## The arithmetical bounds -/

/-- The challenge named by a scale index.  Surjectivity onto all challenges is
what makes `∀ n` equivalent to `∀ W k`. -/
def decodeChallenge (n : ℕ) : List (List (ℕ × Bool)) × ℕ :=
  (Encodable.decode (α := List (List (ℕ × Bool)) × ℕ) n).getD ([], 0)

theorem primrec_decodeChallenge : Primrec decodeChallenge :=
  (Primrec.option_getD.comp Primrec.decode
    (Primrec.const (([], 0) : List (List (ℕ × Bool)) × ℕ))).of_eq fun _ => rfl

theorem decodeChallenge_surjective (Wk : List (List (ℕ × Bool)) × ℕ) :
    decodeChallenge (Encodable.encode Wk) = Wk := by
  rw [decodeChallenge, Encodable.encodek]
  rfl

/-- **Recognising soficity from a finite presentation code is `Π⁰₂`.** -/
theorem pi02_isSofic :
    Pi02 fun c : PresentationCode => IsSofic (Carrier c) := by
  refine ⟨fun z : PresentationCode × ℕ =>
    Answers z.1 (decodeChallenge z.2).1 (decodeChallenge z.2).2, ?_, ?_⟩
  · have hmap : Computable fun z : PresentationCode × ℕ =>
        (z.1, decodeChallenge z.2) :=
      (Primrec.pair Primrec.fst (primrec_decodeChallenge.comp
        Primrec.snd)).to_comp
    exact rePred_answers.comp hmap
  · intro c
    rw [isSofic_iff_forall_answers c]
    constructor
    · intro h n
      exact h _ _
    · intro h W k
      have := h (Encodable.encode (W, k))
      rwa [decodeChallenge_surjective (W, k)] at this

/-- **Recognising non-soficity from a finite presentation code is `Σ⁰₂`.** -/
theorem sigma02_not_isSofic :
    Sigma02 fun c : PresentationCode => ¬ IsSofic (Carrier c) :=
  (sigma02_compl_iff _).2 pi02_isSofic

/-! ## The strict first-level separation

`Computability.SoficMarkov` reduces the word problem to soficity recognition;
`Computability.WordProblemRE` shows the negative side of the word problem is
not recursively enumerable, unconditionally; and
`SoficRecognitionSecondLevel.exists_nonsofic_presentationCode` supplies the
forbidden code with no hypothesis.  So the non-enumerability of the negative
side is unconditional, and pairs with the `Π⁰₂` bound above. -/

/-- **No enumeration lists the nonsofic finite presentation codes.** -/
theorem nonsofic_not_re :
    ¬ REPred fun c : PresentationCode => ¬ IsSofic (Carrier c) := by
  obtain ⟨seed, hseed⟩ :=
    SoficRecognitionSecondLevel.exists_nonsofic_presentationCode
  exact SoficMarkov.sofic_negative_side_not_re (H := Carrier seed) hseed
    WordProblemRE.not_rePred_compl_wordProblemPred

/-- **The arithmetical position of soficity recognition on finite presentation
codes**: `Π⁰₂` but not `Π⁰₁`, and its complement `Σ⁰₂` but not `Σ⁰₁`. -/
theorem sofic_fp_strict_position :
    (Pi02 (fun c : PresentationCode => IsSofic (Carrier c)) ∧
        ¬ Pi01 (fun c : PresentationCode => IsSofic (Carrier c))) ∧
      (Sigma02 (fun c : PresentationCode => ¬ IsSofic (Carrier c)) ∧
        ¬ Sigma01 (fun c : PresentationCode => ¬ IsSofic (Carrier c))) :=
  strict_first_level_pair pi02_isSofic nonsofic_not_re

/-! ## The closed form -/

/-- **The `Π⁰₂` upper bound for soficity recognition**, as a closed
proposition. -/
def SoficRecognitionPi02Bound : Prop :=
  Pi02 (fun c : PresentationCode => IsSofic (Carrier c)) ∧
    Sigma02 (fun c : PresentationCode => ¬ IsSofic (Carrier c))

/-- **The bound holds.**  No hypothesis, no construction datum. -/
theorem soficRecognitionPi02Bound : SoficRecognitionPi02Bound :=
  ⟨pi02_isSofic, sigma02_not_isSofic⟩

end SoficRecognitionPi02
end GroupApproximation
