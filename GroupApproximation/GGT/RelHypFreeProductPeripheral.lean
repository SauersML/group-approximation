import GroupApproximation.GGT.RelHypKazhdanNonElementary
import GroupApproximation.Algebra.FreeProductCyclicWord
import GroupApproximation.Algebra.CoprodIWordInverse

/-!
# The peripheral factor of a free product is isolated, and what that leaves of
Osin's Theorem 2.34

`GGT/RelHypDefinition.lean` states `FreeProductRelativelyHyperbolicStatement`,
the one geometric input of the Fournier-Facio quotient sentence:

> if `H` is word hyperbolic then `U ∗ H` is hyperbolic relative to the factor
> `U`.

`IsRelativelyHyperbolic` has two clauses at the same relative generating set:
Farb's -- the coned-off Cayley graph `Γ(G, X ⊔ ℋ)` is Gromov hyperbolic -- and
Dahmani--Guirardel--Osin's -- the metric `d̂` that the *avoiding* relative paths
induce on each peripheral subgroup is locally finite.  **This module proves the
second one outright**, for the free product at the canonical relative generating
set, and reduces the statement to the first.

## What is proved, and why it is the clause that needed proving

The second clause is the one with content.  Farb's condition alone certifies
pairs that are not relatively hyperbolic, and the standing example is
`ℤ² = ⟨a⟩ × ⟨b⟩` relative to `⟨a⟩`: the coned graph is quasi-isometric to a
line, so it is hyperbolic, while `d̂(1, aⁿ) ≤ 3` for every `n` by the path
`b, aⁿ, b⁻¹` through the *other* coset `b⟨a⟩`, so every `d̂`-ball is infinite.
`RelativeGeneratingSet.AvoidsPeripheral` is written so that this path is legal
-- a step across a different coset is allowed, only a step both of whose
endpoints lie in `H l` is not -- and the theorem below says that in a free
product no such path reaches a nontrivial peripheral element at all.

`peripheralBall_subset_one`: for `G = U ∗ H` with peripheral factor `U`, the
`d̂`-ball of any radius about `1` is `{1}`.  So the clause holds with room to
spare, and it holds for *every* radius rather than by a counting argument.

## The mechanism: the head letter never changes

The proof is one invariant, carried along the path and stated with no geometry
in it.  Write the reduced word of `g ∈ U ∗ H` in Mathlib's normal form.  The
partial products `1 = p₀, p₁, …, p_k` of a relative path are built by
multiplying **on the right** by letters, and right multiplication cannot touch
the *first* syllable of a reduced word unless the word collapses to `1`
(`headIdx_mul_of`).  So:

* `p₀ = 1` lies in the peripheral factor, hence `p₁` does not, hence `p₁` is a
  letter of `X ⊆ H` -- its first syllable is in the partner factor;
* every later `p_i` keeps a first syllable in the partner factor, or is `1`
  (`headsPartner_prod`);
* a nontrivial element of the peripheral factor has its first syllable in the
  peripheral factor, so `p_k` peripheral forces `p_k = 1`.

Mathlib's word API is head-oriented and multiplies on the left, so the invariant
is proved at the *last* letter under left multiplication
(`lastIdx_of_mul`, on `FreeProductCyclic.toList_of_smul` and the companion
`toList_of_smul_of_fstIdx_ne` proved here for the case where the two factors
differ) and transported to the first letter under right multiplication by
`CoprodIWordInverse.fstIdx_inv`, which reads the last letter of `x` as the first
letter of `x⁻¹`.

## What is left of the citation

`FreeProductConedHyperbolicStatement` -- Farb's clause, at the explicit
generating set this module builds -- and
`freeProductRelativelyHyperbolicStatement_of_coned` proves
`FreeProductRelativelyHyperbolicStatement` from it.  That is the whole of the
remaining debt: the Bass--Serre tree of the free product, whose vertex spaces
are copies of `Γ(H, X)` glued along the crushed peripheral cosets, is
hyperbolic.  Nothing about the peripheral metric is owed any more.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## 0.  A list lemma

The repository's copy of this is `private`, so it is restated. -/

/-- The last entry of a `cons` is the last entry of its tail, when the tail has
one. -/
theorem getLast?_cons_ne_nil {α : Type*} (a : α) {l : List α} (hl : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl hl
  | cons _ _ => exact List.getLast?_cons_cons

/-! ## 1.  The first and last letters of a reduced word

Mathlib's `Word.fstIdx` reads the first letter; `lastIdx` reads the last, and
`CoprodIWordInverse.fstIdx_inv` is the bridge.  The one lemma with content is
`lastIdx_of_mul`: multiplying at the front leaves the back alone. -/

section Letters

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- **The index of the first letter** of the reduced word of `g`, and `none` at
the identity. -/
def headIdx (g : CoprodI G) : Option ι := Word.fstIdx (Word.equiv g)

/-- **The index of the last letter** of the reduced word of `g`, and `none` at
the identity. -/
def lastIdx (g : CoprodI G) : Option ι :=
  ((Word.equiv g).toList.getLast?).map Sigma.fst

theorem headIdx_eq (g : CoprodI G) :
    headIdx g = ((Word.equiv g).toList.head?).map Sigma.fst := rfl

theorem lastIdx_eq (g : CoprodI G) :
    lastIdx g = ((Word.equiv g).toList.getLast?).map Sigma.fst := rfl

/-- The last letter of `g` is the first letter of `g⁻¹`. -/
theorem lastIdx_eq_headIdx_inv (g : CoprodI G) : lastIdx g = headIdx g⁻¹ :=
  (CoprodIWordInverse.fstIdx_inv g).symm

/-- The first letter of `g` is the last letter of `g⁻¹`. -/
theorem headIdx_eq_lastIdx_inv (g : CoprodI G) : headIdx g = lastIdx g⁻¹ := by
  rw [lastIdx_eq_headIdx_inv, inv_inv]

/-- **Left multiplication by a letter of a different factor prepends it.**  The
companion of `FreeProductCyclic.toList_of_smul`, which covers the case where the
word already begins in the same factor. -/
theorem toList_of_smul_of_fstIdx_ne {i : ι} {z : G i} (hz : z ≠ 1) {w : Word G}
    (hne : Word.fstIdx w ≠ some i) :
    ((CoprodI.of z : CoprodI G) • w).toList
      = (⟨i, z⟩ : Σ i, G i) :: w.toList := by
  have h : (CoprodI.of z : CoprodI G) • w = Word.cons z w hne hz :=
    (Word.cons_eq_smul (m := z) (ls := w) (h1 := hne) (h2 := hz)).symm
  exact congrArg Word.toList h

/-- The reduced word of a nontrivial element is not empty. -/
theorem toList_ne_nil {g : CoprodI G} (hg : g ≠ 1) :
    (Word.equiv g).toList ≠ [] := by
  intro h
  apply hg
  apply FreeProductCyclic.sylLength_eq_zero_iff.mp
  show (Word.equiv g).toList.length = 0
  simp [h]

/-- A single nontrivial letter is a one-letter word: its first letter has the
index of the factor it comes from. -/
theorem headIdx_of {i : ι} {z : G i} (hz : z ≠ 1) :
    headIdx (CoprodI.of z : CoprodI G) = some i := by
  have hemp : Word.fstIdx (Word.empty : Word G) ≠ some i := by
    simp [Word.fstIdx, Word.empty]
  have hlist : (Word.equiv (CoprodI.of z : CoprodI G)).toList
      = (⟨i, z⟩ : Σ i, G i) :: (Word.empty : Word G).toList := by
    show ((CoprodI.of z : CoprodI G) • (Word.empty : Word G)).toList = _
    exact toList_of_smul_of_fstIdx_ne hz hemp
  simp [headIdx_eq, hlist, Word.empty]

theorem headIdx_one : headIdx (1 : CoprodI G) = none := by
  simp [headIdx_eq, FreeProductCyclic.equiv_one, Word.empty]

/-- Replacing the head letter of a nonempty word by another letter of the same
factor does not move the index of its last letter. -/
theorem getLast?_map_fst_cons {i : ι} (y y' : G i) (l : List (Σ i, G i)) :
    (((⟨i, y⟩ : Σ i, G i) :: l).getLast?).map Sigma.fst
      = (((⟨i, y'⟩ : Σ i, G i) :: l).getLast?).map Sigma.fst := by
  cases l with
  | nil => rfl
  | cons b t =>
      rw [getLast?_cons_ne_nil _ (List.cons_ne_nil b t),
        getLast?_cons_ne_nil _ (List.cons_ne_nil b t)]

/-- **The last letter is untouched by multiplication at the front.**  If `g` and
`of z * g` are both nontrivial, their reduced words end in the same factor.

Three cases: the letter merges with the head (`z * x ≠ 1`), it cancels the head
(`z * x = 1`, and then the tail is nonempty because the product is not `1`), or
it comes from another factor and is simply prepended. -/
theorem lastIdx_of_mul {i : ι} (z : G i) {g : CoprodI G} (hg : g ≠ 1)
    (hzg : (CoprodI.of z : CoprodI G) * g ≠ 1) :
    lastIdx ((CoprodI.of z : CoprodI G) * g) = lastIdx g := by
  by_cases hz : z = 1
  · rw [hz, map_one, one_mul]
  have hlen : (Word.equiv g).toList ≠ [] := toList_ne_nil hg
  have heq : Word.equiv ((CoprodI.of z : CoprodI G) * g)
      = (CoprodI.of z : CoprodI G) • Word.equiv g :=
    FreeProductCyclic.equiv_of_mul z g
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hlen
  obtain ⟨j, x⟩ := a
  simp only [lastIdx_eq]
  by_cases hij : i = j
  · subst hij
    have hsm := FreeProductCyclic.toList_of_smul z hl
    by_cases hzx : z * x = 1
    · rw [if_pos hzx] at hsm
      have hlne : l ≠ [] := by
        intro hnil
        apply hzg
        apply FreeProductCyclic.sylLength_eq_zero_iff.mp
        show (Word.equiv ((CoprodI.of z : CoprodI G) * g)).toList.length = 0
        simp [heq, hsm, hnil]
      rw [heq, hsm, hl, getLast?_cons_ne_nil _ hlne]
    · rw [if_neg hzx] at hsm
      rw [heq, hsm, hl]
      exact getLast?_map_fst_cons _ _ _
  · have hfst : Word.fstIdx (Word.equiv g) = some j := by
      show ((Word.equiv g).toList.head?).map Sigma.fst = some j
      simp [hl]
    have hne : Word.fstIdx (Word.equiv g) ≠ some i := by
      rw [hfst]
      intro hcon
      exact hij (Option.some.inj hcon).symm
    have hsm := toList_of_smul_of_fstIdx_ne (z := z) hz hne
    rw [heq, hsm, getLast?_cons_ne_nil _ hlen]

/-- **The first letter is untouched by multiplication at the back.**  The form
the relative path uses: its partial products grow on the right.

Proved from `lastIdx_of_mul` by inverting, which turns a statement about the
back of a word into one about the front. -/
theorem headIdx_mul_of {i : ι} (z : G i) {g : CoprodI G} (hg : g ≠ 1)
    (hgz : g * (CoprodI.of z : CoprodI G) ≠ 1) :
    headIdx (g * (CoprodI.of z : CoprodI G)) = headIdx g := by
  have hinv : (g * (CoprodI.of z : CoprodI G))⁻¹
      = (CoprodI.of z⁻¹ : CoprodI G) * g⁻¹ := by
    rw [mul_inv_rev, map_inv]
  have hg' : g⁻¹ ≠ 1 := inv_ne_one.mpr hg
  have hzg' : (CoprodI.of z⁻¹ : CoprodI G) * g⁻¹ ≠ 1 := by
    rw [← hinv]
    exact inv_ne_one.mpr hgz
  rw [headIdx_eq_lastIdx_inv (g * (CoprodI.of z : CoprodI G)),
    headIdx_eq_lastIdx_inv g, hinv, lastIdx_of_mul z⁻¹ hg' hzg']

end Letters

/-! ## 2.  The two-factor free product and its peripheral factor -/

section TwoFactor

/-- **The peripheral factor** of a two-factor free product: the image of the
factor at index `false`.  At `G = pairFamily U H` this is
`freeProductPeripheral U H`, definitionally. -/
def pairPeripheral (G : Bool → Type) [∀ b, Group (G b)] :
    Subgroup (CoprodI G) :=
  MonoidHom.range (CoprodI.of : G false →* CoprodI G)

variable {G : Bool → Type} [∀ b, Group (G b)]

theorem mem_pairPeripheral {g : CoprodI G} :
    g ∈ pairPeripheral G ↔ ∃ u : G false, (CoprodI.of u : CoprodI G) = g :=
  MonoidHom.mem_range

theorem of_mem_pairPeripheral (u : G false) :
    (CoprodI.of u : CoprodI G) ∈ pairPeripheral G :=
  MonoidHom.mem_range.mpr ⟨u, rfl⟩

/-! ### The invariant carried along an avoiding path -/

section Invariant

variable [∀ b, DecidableEq (G b)]

/-- **The invariant**: the reduced word of `g` begins in the partner factor,
unless `g` is trivial. -/
def HeadsPartner (g : CoprodI G) : Prop := g = 1 ∨ headIdx g = some true

/-- The invariant pins the peripheral factor down to its identity: a nontrivial
peripheral element begins in the peripheral factor. -/
theorem eq_one_of_headsPartner_of_mem {g : CoprodI G} (hgood : HeadsPartner g)
    (hmem : g ∈ pairPeripheral G) : g = 1 := by
  rcases hgood with h | h
  · exact h
  · exfalso
    obtain ⟨u, rfl⟩ := mem_pairPeripheral.mp hmem
    by_cases hu : u = 1
    · rw [hu, map_one, headIdx_one] at h
      exact Option.noConfusion h
    · rw [headIdx_of hu] at h
      exact Bool.noConfusion (Option.some.inj h)

/-- **One step of an avoiding path keeps the invariant.**

At a trivial partial product the avoidance hypothesis is what does the work: the
next vertex is not peripheral, so the letter is not peripheral, so it comes from
the partner factor.  At a nontrivial one the head is simply unchanged. -/
theorem headsPartner_mul {g a : CoprodI G} (hg : HeadsPartner g)
    (ha : ∃ (i : Bool) (z : G i), (CoprodI.of z : CoprodI G) = a)
    (havoid : ¬ (g ∈ pairPeripheral G ∧ g * a ∈ pairPeripheral G)) :
    HeadsPartner (g * a) := by
  obtain ⟨i, z, rfl⟩ := ha
  rcases hg with rfl | hhead
  · rw [one_mul]
    have hmem1 : (1 : CoprodI G) ∈ pairPeripheral G := one_mem _
    have hnot : (CoprodI.of z : CoprodI G) ∉ pairPeripheral G := by
      intro hcon
      refine havoid ⟨hmem1, ?_⟩
      rwa [one_mul]
    have hz : z ≠ 1 := by
      intro hz1
      apply hnot
      rw [hz1, map_one]
      exact one_mem _
    cases i with
    | false => exact absurd (of_mem_pairPeripheral z) hnot
    | true => exact Or.inr (headIdx_of hz)
  · have hg1 : g ≠ 1 := by
      intro hcon
      rw [hcon, headIdx_one] at hhead
      exact Option.noConfusion hhead
    by_cases hzero : g * (CoprodI.of z : CoprodI G) = 1
    · exact Or.inl hzero
    · refine Or.inr ?_
      rw [headIdx_mul_of z hg1 hzero]
      exact hhead

/-- **The invariant survives a whole avoiding path.**

`g₀` is the vertex the path starts from; the hypothesis is the avoidance
condition based there, and the conclusion is the invariant at the far end. -/
theorem headsPartner_prod :
    ∀ (w : List (CoprodI G)) (g₀ : CoprodI G),
      (∀ a ∈ w, ∃ (i : Bool) (z : G i), (CoprodI.of z : CoprodI G) = a) →
      HeadsPartner g₀ →
      (∀ k, k + 1 ≤ w.length →
        ¬ (g₀ * (w.take k).prod ∈ pairPeripheral G ∧
           g₀ * (w.take (k + 1)).prod ∈ pairPeripheral G)) →
      HeadsPartner (g₀ * w.prod) := by
  intro w
  induction w with
  | nil =>
      intro g₀ _ hg₀ _
      rw [List.prod_nil, mul_one]
      exact hg₀
  | cons a t ih =>
      intro g₀ hlet hg₀ havoid
      have ha : ∃ (i : Bool) (z : G i), (CoprodI.of z : CoprodI G) = a :=
        hlet a (by simp)
      have h0 : ¬ (g₀ ∈ pairPeripheral G ∧ g₀ * a ∈ pairPeripheral G) := by
        have h := havoid 0 (by simp only [List.length_cons]; omega)
        have e1 : ((a :: t).take 0).prod = 1 := by simp
        have e2 : ((a :: t).take (0 + 1)).prod = a := by simp
        rw [e1, e2, mul_one] at h
        exact h
      have hstep : HeadsPartner (g₀ * a) := headsPartner_mul hg₀ ha h0
      have havoid' : ∀ k, k + 1 ≤ t.length →
          ¬ (g₀ * a * (t.take k).prod ∈ pairPeripheral G ∧
             g₀ * a * (t.take (k + 1)).prod ∈ pairPeripheral G) := by
        intro k hk
        have h := havoid (k + 1) (by simp only [List.length_cons]; omega)
        have e1 : ((a :: t).take (k + 1)).prod = a * (t.take k).prod := by
          rw [List.take_succ_cons, List.prod_cons]
        have e2 : ((a :: t).take (k + 1 + 1)).prod = a * (t.take (k + 1)).prod := by
          rw [List.take_succ_cons, List.prod_cons]
        rw [e1, e2, ← mul_assoc, ← mul_assoc] at h
        exact h
      have hkey := ih (g₀ * a)
        (fun x hx => hlet x (List.mem_cons_of_mem _ hx)) hstep havoid'
      have hprod : g₀ * a * t.prod = g₀ * (a :: t).prod := by
        rw [List.prod_cons, mul_assoc]
      rwa [hprod] at hkey

end Invariant

/-! ### The relative generating set, and the isolation theorem -/

/-- **Osin's relative generating set for `U ∗ H` relative to `U`**: a finite
symmetric generating set of the partner factor, mapped into the free product.

It generates nothing like the free product on its own -- no element of the
peripheral factor is in its closure -- and it does not have to: what
`RelativeGeneratingSet.closure_eq` asks is that the union with the peripheral
subgroups generates, and the two factors together do. -/
def pairRelGen (S : Finset (G true))
    (hS : IsSymmetricGeneratingSet (S : Set (G true))) :
    RelativeGeneratingSet (CoprodI G) (fun _ : Unit => pairPeripheral G) where
  carrier := (fun s : G true => (CoprodI.of s : CoprodI G)) '' (S : Set (G true))
  finite := S.finite_toSet.image _
  inv_mem := by
    rintro x ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, hS.inv_mem s hs, by simp⟩
  closure_eq := by
    refine Subgroup.eq_top_iff'.mpr ?_
    intro g
    induction g using Monoid.CoprodI.induction_on with
    | one => exact one_mem _
    | of i x =>
        cases i with
        | false =>
            refine Subgroup.subset_closure (Or.inr ?_)
            exact Set.mem_iUnion.mpr ⟨(), of_mem_pairPeripheral x⟩
        | true =>
            have hx : x ∈ Subgroup.closure ((S : Set (G true))) := by
              rw [hS.closure_eq]
              exact Subgroup.mem_top x
            induction hx using Subgroup.closure_induction with
            | mem s hs => exact Subgroup.subset_closure (Or.inl ⟨s, hs, rfl⟩)
            | one =>
                rw [map_one]
                exact one_mem _
            | mul _ _ _ _ hp hq =>
                rw [map_mul]
                exact mul_mem hp hq
            | inv _ _ hp =>
                rw [map_inv]
                exact inv_mem hp
    | mul _ _ hx hy => exact mul_mem hx hy

@[simp] theorem pairRelGen_carrier (S : Finset (G true))
    (hS : IsSymmetricGeneratingSet (S : Set (G true))) :
    (pairRelGen S hS).carrier
      = (fun s : G true => (CoprodI.of s : CoprodI G)) '' (S : Set (G true)) :=
  rfl

/-- Every letter of the relative alphabet is a single syllable: either a
peripheral element or a generator of the partner factor. -/
theorem exists_of_mem_pairRelGen_alphabet {S : Finset (G true)}
    {hS : IsSymmetricGeneratingSet (S : Set (G true))} {a : CoprodI G}
    (ha : a ∈ (pairRelGen S hS).alphabet.carrier) :
    ∃ (i : Bool) (z : G i), (CoprodI.of z : CoprodI G) = a := by
  rw [RelativeGeneratingSet.alphabet_carrier, pairRelGen_carrier] at ha
  rcases ha with ha | ha
  · obtain ⟨s, -, rfl⟩ := ha
    exact ⟨true, s, rfl⟩
  · rw [Set.mem_iUnion] at ha
    obtain ⟨-, hu⟩ := ha
    obtain ⟨u, rfl⟩ := mem_pairPeripheral.mp hu
    exact ⟨false, u, rfl⟩

/-- **A relative path avoiding the peripheral subgraph reaches no nontrivial
peripheral element.**

This is the free-product form of Dahmani--Guirardel--Osin's second clause, and
it is sharp: the path is allowed to cross any *other* coset of the peripheral
factor, which is exactly the freedom that makes the clause fail for
`ℤ²` relative to `⟨a⟩`. -/
theorem eq_one_of_avoidsPeripheral {S : Finset (G true)}
    {hS : IsSymmetricGeneratingSet (S : Set (G true))} {g : CoprodI G}
    (hg : g ∈ pairPeripheral G) {w : List (CoprodI G)}
    (hword : IsWord (pairRelGen S hS).alphabet.carrier w g)
    (hav : RelativeGeneratingSet.AvoidsPeripheral
      (fun _ : Unit => pairPeripheral G) () w) : g = 1 := by
  classical
  have hlet : ∀ a ∈ w, ∃ (i : Bool) (z : G i), (CoprodI.of z : CoprodI G) = a :=
    fun a ha => exists_of_mem_pairRelGen_alphabet (hS := hS) (hword.letters a ha)
  have havoid : ∀ k, k + 1 ≤ w.length →
      ¬ ((1 : CoprodI G) * (w.take k).prod ∈ pairPeripheral G ∧
         (1 : CoprodI G) * (w.take (k + 1)).prod ∈ pairPeripheral G) := by
    intro k hk
    rw [one_mul, one_mul]
    exact hav k hk
  have hgood := headsPartner_prod w 1 hlet (Or.inl rfl) havoid
  rw [one_mul, hword.prod_eq] at hgood
  exact eq_one_of_headsPartner_of_mem hgood hg

/-- **The induced metric on the peripheral factor is discrete**: every ball
about the identity is `{1}`.  Local finiteness is then immediate, and no
counting is involved. -/
theorem peripheralBall_subset_one (S : Finset (G true))
    (hS : IsSymmetricGeneratingSet (S : Set (G true))) (l : Unit) (n : ℕ) :
    {h : CoprodI G | h ∈ (fun _ : Unit => pairPeripheral G) l ∧
      ∃ m ∈ (pairRelGen S hS).peripheralLengths l h, m ≤ n} ⊆ {1} := by
  cases l
  rintro h ⟨hmem, _m, ⟨_w, hword, hav, -⟩, -⟩
  exact eq_one_of_avoidsPeripheral (hS := hS) hmem hword hav

/-- **Dahmani--Guirardel--Osin's second clause, proved for the free product.**
-/
theorem peripheralMetricLocallyFinite_pairRelGen (S : Finset (G true))
    (hS : IsSymmetricGeneratingSet (S : Set (G true))) :
    PeripheralMetricLocallyFinite (pairRelGen S hS) := by
  intro l n
  exact Set.Finite.subset (Set.finite_singleton (1 : CoprodI G))
    (peripheralBall_subset_one S hS l n)

end TwoFactor

/-! ## 3.  What is left of Osin's Theorem 2.34 -/

section FreeProduct

/-- **The relative generating set of `U ∗ H` relative to `U`.**  The two-factor
construction of section 2 at `G = pairFamily U H`; the peripheral family is
`freeProductPeripheral U H`, which is `pairPeripheral (pairFamily U H)`. -/
def freeProductRelGen (U H : Type) [Group U] [Group H] (S : Finset H)
    (hS : IsSymmetricGeneratingSet (S : Set H)) :
    RelativeGeneratingSet (CoprodI (pairFamily U H))
      (fun _ : Unit => freeProductPeripheral U H) :=
  pairRelGen (G := pairFamily U H) S hS

/-- The peripheral clause, at the free product. -/
theorem peripheralMetricLocallyFinite_freeProductRelGen (U H : Type) [Group U]
    [Group H] (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H)) :
    PeripheralMetricLocallyFinite (freeProductRelGen U H S hS) :=
  peripheralMetricLocallyFinite_pairRelGen (G := pairFamily U H) S hS

/-- **Farb's clause for the free product, as a named `Prop`**: the coned-off
Cayley graph `Γ(U ∗ H, X ⊔ U)` is Gromov hyperbolic, at the explicit `X` built
from a finite symmetric generating set of `H` satisfying the four-point
condition.

This is all that is left of Osin, Memoirs 179 (2006), Theorem 2.34 (Bowditch,
*Relatively hyperbolic groups*, §9) once
`peripheralMetricLocallyFinite_freeProductRelGen` has discharged the second
clause.  The hypotheses are stated at the *same* `S` and `δ` that
`Hyperbolic.IsHyperbolicGroup H` supplies, so nothing has to be transported
between generating sets -- which matters, because generating-set independence of
hyperbolicity is the Morse lemma and is not available here. -/
def FreeProductConedHyperbolicStatement : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H) (S : Finset H)
    (hS : IsSymmetricGeneratingSet (S : Set H)) (δ : ℕ),
      Hyperbolic.IsFourPointHyperbolic (S : Set H) δ →
        ∃ Δ : ℝ, HullGeometry.IsHyperbolicSpace Δ
          (Cayley (freeProductRelGen U H S hS).alphabet)

/-- **`FreeProductRelativelyHyperbolicStatement` from Farb's clause alone.**

Both clauses of `IsRelativelyHyperbolic` are supplied at the same relative
generating set, which is what the definition demands; the second is a theorem of
this module and only the first remains a citation. -/
theorem freeProductRelativelyHyperbolicStatement_of_coned
    (h : FreeProductConedHyperbolicStatement) :
    FreeProductRelativelyHyperbolicStatement := by
  intro U H instU instH hhyp
  obtain ⟨S, hS, δ, hδ⟩ := hhyp
  obtain ⟨Δ, hΔ⟩ := h U H instU instH S hS δ hδ
  exact ⟨freeProductRelGen U H S hS, Δ, hΔ,
    peripheralMetricLocallyFinite_freeProductRelGen U H S hS⟩

/-- **The Fournier-Facio quotient sentence, on three inputs, the geometric one
weakened.**

`fournierFacioQuotientStatement_of_osin'` runs on `OsinTheorem24`,
`OsinRelatorDesign` and the full `FreeProductRelativelyHyperbolicStatement`.
Here the third is `FreeProductConedHyperbolicStatement` -- Farb's clause alone,
because the Dahmani--Guirardel--Osin clause is now a theorem. -/
theorem fournierFacioQuotientStatement_of_coned
    (hOsin : OsinTheorem24) (hDesign : OsinRelatorDesign)
    (hCone : FreeProductConedHyperbolicStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_osin' hOsin hDesign
    (freeProductRelativelyHyperbolicStatement_of_coned hCone)

end FreeProduct

end RelHyp
end GGT
end GroupApproximation
