import GroupApproximation.GGT.RelHypOsin24CollapseModel
import GroupApproximation.GGT.RelHypOsinTheorem24Repaired

/-!
# The weighted Greendlinger leaf is false at every length floor

`GGT/RelHypOsinTheorem24Refuted.lean` refutes the first generation of the
weighted leaf with a relator that is not a geodesic word.
`GGT/RelHypAbelianPartnerNoGo.lean` refutes the second with an abelian partner
factor, conditionally on a weighted router design existing.  Both diagnoses
suggested a third generation in which the length floor `rho` is produced from
the length function *before* the relator family, on the ground that over a fixed
alphabet an elementary partner cannot supply arbitrarily long small-cancellation
families.

That ground is not available, because `RelativeLength` never says the alphabet
is finite -- or that the ambient group is hyperbolic relative to the peripheral
family, or indeed anything geometric at all.  This module makes the gap into a
theorem.

## The witness

Both factors are `ℤ`.  `L` is the length function of
`GGT/RelHypOsin24CollapseModel.lean`: the indicator of `g ≠ 1`, maximised
against the norm `|a| ≤ 1` plus `|b|` of the abelianisation `(a, b) ∈ ℤ × ℤ`.
It is a `RelativeLength`, it has geodesic spellings, and it measures each factor
exactly -- the partner's `t^k` has length `|k|`.

The relator family is `R_m = {t^m spelled by m letters, its formal inverse}`,
for any `m` at all.  Every hypothesis of the third-generation leaf holds:

* symmetrized -- a constant list is fixed by every rotation, and formal
  inversion exchanges the two members;
* cyclically reduced -- two adjacent letters multiply to `t^{±2}`, of length
  two;
* letters -- `t^{±1}` have length one;
* **geodesic** -- `|t^m| = m`, which is what the first witness failed;
* **longer than any prescribed `rho`** -- take `m = max rho 42`, which is what
  the third generation asks for and what the first two witnesses could not
  survive;
* the fragment slack at `lam = 1/7`, since `m ≥ 42`;
* **the metric condition over Osin's group pieces** -- a prefix of `t^m` and a
  prefix of `t^{-m}` are equal in the group only when both are empty, so the
  only group piece is the empty word.

And the conclusion fails.  The commutator `[t^m, s]` of the partner element with
a source element lies in the relator subgroup, is nontrivial -- it survives the
map to the infinite dihedral group of `ℤ`, where it acts as translation by `2m`
-- and has `L`-length **one**, because the abelianisation cannot see it.
`RelativeLengthBound` would demand a relator shorter than two letters.

## What the leaf is missing

Not a length floor and not a piece condition: the alphabet.  Osin's Theorem 2.4
is stated for the relative Cayley graph `Γ(G, X ∪ H)` with `X` **finite** and
`G` hyperbolic relative to `{H}`.  Here the unit ball of `L` contains every
commutator of the two factors (`L_len_commutator_le_one`), so `L` is the word
metric of an infinite alphabet, and no relative hyperbolicity hypothesis is
present to exclude it.  A fourth generation has to carry the relatively
hyperbolic structure itself -- the length function must be `X ∪ U` for a finite
`X`, and the pair `(G, {U})` must satisfy `IsRelativelyHyperbolic` -- rather
than an abstract length function with five clauses.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric

namespace Osin24Collapse

/-! ## 1.  The relator family -/

/-- `t` repeated `m` times. -/
def w (m : ℕ) : List (CoprodI Fam) := List.replicate m tLet

/-- `t⁻¹` repeated `m` times. -/
def wInv (m : ℕ) : List (CoprodI Fam) := List.replicate m tLet⁻¹

theorem w_def (m : ℕ) : w m = List.replicate m tLet := rfl

theorem wInv_def (m : ℕ) : wInv m = List.replicate m tLet⁻¹ := rfl

/-- The symmetrized family: one relator and its formal inverse. -/
def relSet (m : ℕ) : Set (List (CoprodI Fam)) := {w m, wInv m}

theorem w_mem (m : ℕ) : w m ∈ relSet m := Or.inl rfl

theorem wInv_mem (m : ℕ) : wInv m ∈ relSet m := Or.inr rfl

theorem length_of_mem {m : ℕ} {r : List (CoprodI Fam)} (hr : r ∈ relSet m) :
    r.length = m := by
  rcases hr with rfl | rfl
  · rw [w_def, List.length_replicate]
  · rw [wInv_def, List.length_replicate]

theorem prod_w (m : ℕ) : (w m).prod = tLet ^ m := by
  rw [w_def, List.prod_replicate]

theorem prod_wInv (m : ℕ) : (wInv m).prod = (tLet ^ m)⁻¹ := by
  rw [wInv_def, List.prod_replicate, inv_pow]

/-! ## 2.  The five list-level certificates -/

theorem symmetrized (m : ℕ) : LetterSymmetrized (relSet m) := by
  constructor
  · rintro r hr n
    rcases hr with rfl | rfl
    · rw [w_def, List.rotate_replicate, ← w_def]
      exact w_mem m
    · rw [wInv_def, List.rotate_replicate, ← wInv_def]
      exact wInv_mem m
  · rintro r hr
    rcases hr with rfl | rfl
    · have hmap : (((w m).map fun a => a⁻¹).reverse) = wInv m := by
        rw [w_def, wInv_def]
        simp
      rw [hmap]
      exact wInv_mem m
    · have hmap : (((wInv m).map fun a => a⁻¹).reverse) = w m := by
        rw [wInv_def, w_def]
        simp
      rw [hmap]
      exact w_mem m

theorem letters (m : ℕ) : ∀ r ∈ relSet m, ∀ a ∈ r, L.len a ≤ 1 := by
  rintro r hr a ha
  rcases hr with rfl | rfl
  · rw [w_def] at ha
    rw [List.eq_of_mem_replicate ha]
    exact L_len_tLet_le_one
  · rw [wInv_def] at ha
    rw [List.eq_of_mem_replicate ha]
    exact L_len_tLet_inv_le_one

theorem reduced (m : ℕ) : ∀ r ∈ relSet m, LetterReduced L r := by
  have hsq : L.len (tLet * tLet) = 2 := by
    have h3 : tLet * tLet = tLet ^ 2 := (pow_two tLet).symm
    rw [h3]
    exact L_len_tLet_pow 2 (by norm_num)
  have hsqi : L.len (tLet⁻¹ * tLet⁻¹) = 2 := by
    have h3 : tLet⁻¹ * tLet⁻¹ = (tLet ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
    rw [h3, L.len_inv]
    exact L_len_tLet_pow 2 (by norm_num)
  rintro r hr
  rcases hr with rfl | rfl
  · intro n s t' a b hEq
    rw [w_def, List.rotate_replicate] at hEq
    have ha : a = tLet := List.eq_of_mem_replicate (n := m) (by rw [hEq]; simp)
    have hb : b = tLet := List.eq_of_mem_replicate (n := m) (by rw [hEq]; simp)
    rw [ha, hb]
    omega
  · intro n s t' a b hEq
    rw [wInv_def, List.rotate_replicate] at hEq
    have ha : a = tLet⁻¹ := List.eq_of_mem_replicate (n := m) (by rw [hEq]; simp)
    have hb : b = tLet⁻¹ := List.eq_of_mem_replicate (n := m) (by rw [hEq]; simp)
    rw [ha, hb]
    omega

/-- **The relators are geodesic words.**  This is the clause
`GGT/RelHypOsinTheorem24Refuted.lean`'s witness failed. -/
theorem geodesic (m : ℕ) (hm : 1 ≤ m) : ∀ r ∈ relSet m, LetterGeodesic L r := by
  rintro r hr
  rcases hr with rfl | rfl
  · show (w m).length = L.len (w m).prod
    rw [w_def, List.length_replicate, List.prod_replicate, L_len_tLet_pow m hm]
  · show (wInv m).length = L.len (wInv m).prod
    rw [wInv_def, List.length_replicate, List.prod_replicate, inv_pow, L.len_inv,
      L_len_tLet_pow m hm]

theorem slack (m : ℕ) (hm : 42 ≤ m) : LetterFragmentSlack (relSet m) (1 / 7) :=
  letterFragmentSlack_of_le_seventh le_rfl fun r hr => by
    rw [length_of_mem hr]; exact hm

/-! ## 3.  Osin's pieces, compared in the group

A prefix of `t^m` and a prefix of `t^{-m}` are equal in the group only if both
are empty, so the family has no nonempty group piece and the metric condition
holds at every positive constant.  This is the clause
`GGT/RelHypOsinTheorem24Repaired.lean` added, and the witness meets it. -/

theorem prod_prefix_w {m : ℕ} {p : List (CoprodI Fam)} (hp : p <+: w m) :
    p.prod = tLet ^ p.length :=
  List.prod_eq_pow_card p tLet fun x hx =>
    List.eq_of_mem_replicate (n := m) (by rw [← w_def m]; exact hp.subset hx)

theorem prod_prefix_wInv {m : ℕ} {p : List (CoprodI Fam)} (hp : p <+: wInv m) :
    p.prod = (tLet ^ p.length)⁻¹ := by
  have h : p.prod = tLet⁻¹ ^ p.length :=
    List.prod_eq_pow_card p tLet⁻¹ fun x hx =>
      List.eq_of_mem_replicate (n := m) (by rw [← wInv_def m]; exact hp.subset hx)
  rw [h, inv_pow]

/-- **The only group piece is the empty word.** -/
theorem groupPiece_nil {m : ℕ} {p : List (CoprodI Fam)}
    (hp : LetterIsGroupPiece (relSet m) p) : p = [] := by
  have key : ∀ a b : List (CoprodI Fam), a <+: w m → b <+: wInv m →
      a.prod = b.prod → a.length = 0 ∧ b.length = 0 := by
    intro a b ha hb hab
    have h1 : ab a.prod = (0, (a.length : ℤ)) := by
      rw [prod_prefix_w ha, ab_tLet_pow]
    have h2 : ab b.prod = (0, -(b.length : ℤ)) := by
      rw [prod_prefix_wInv hb, ab_inv, ab_tLet_pow]
      simp
    rw [hab, h2] at h1
    have h3 : -((b.length : ℤ)) = (a.length : ℤ) := congrArg Prod.snd h1
    omega
  have hp0 : p.length = 0 := by
    obtain ⟨r₁, h₁, r₂, h₂, hne, hpre, q, hq, hpq⟩ := hp
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact absurd rfl hne
    · exact (key p q hpre hq hpq).1
    · exact (key q p hq hpre hpq.symm).2
    · exact absurd rfl hne
  cases p with
  | nil => rfl
  | cons x xs => simp at hp0

theorem groupSmallCancellation {m : ℕ} (hm : 0 < m) :
    LetterMetricGroupSmallCancellation (relSet m) (1 / 7) := by
  intro p hp r hr _
  rw [groupPiece_nil hp, List.length_nil, length_of_mem hr]
  have hpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  push_cast
  linarith

/-! ## 4.  The short element of the relator subgroup

The two factors act on `ℤ` as the infinite dihedral group -- the partner by
translation, the source by negation -- and the commutator of `t^m` with a source
letter acts as translation by `2m`.  So it is nontrivial in the free product,
while its abelianisation is zero and its `L`-length is therefore one. -/

/-- Translation by one. -/
def shiftPerm : Equiv.Perm ℤ where
  toFun x := x + 1
  invFun x := x - 1
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Negation. -/
def negPerm : Equiv.Perm ℤ where
  toFun x := -x
  invFun x := -x
  left_inv := by intro x; simp
  right_inv := by intro x; simp

theorem shiftPerm_apply (x : ℤ) : shiftPerm x = x + 1 := rfl

theorem negPerm_apply (x : ℤ) : negPerm x = -x := rfl

theorem shiftPerm_pow_apply : ∀ (k : ℕ) (x : ℤ), (shiftPerm ^ k) x = x + k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ j ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, shiftPerm_apply]
      push_cast
      ring

theorem shiftPerm_pow_inv_apply (k : ℕ) (x : ℤ) :
    (shiftPerm ^ k)⁻¹ x = x - k := by
  have h : (shiftPerm ^ k) (x - k) = x := by
    rw [shiftPerm_pow_apply]
    ring
  calc (shiftPerm ^ k)⁻¹ x = (shiftPerm ^ k)⁻¹ ((shiftPerm ^ k) (x - k)) := by
        rw [h]
    _ = x - k := by simp

theorem negPerm_inv_apply (x : ℤ) : negPerm⁻¹ x = -x := by
  calc negPerm⁻¹ x = negPerm⁻¹ (negPerm (-x)) := by rw [negPerm_apply, neg_neg]
    _ = -x := by simp

/-- The source factor negates, the partner factor translates. -/
def psiFactor : ∀ b, Fam b →* Equiv.Perm ℤ
  | false => zpowersHom (Equiv.Perm ℤ) negPerm
  | true => zpowersHom (Equiv.Perm ℤ) shiftPerm

/-- The infinite dihedral action of the free product. -/
def psi : CoprodI Fam →* Equiv.Perm ℤ := CoprodI.lift psiFactor

/-- **The generators act as the shift and the negation.**

Proved by unfolding rather than by a general lemma about `emT`: a statement
quantified over `y : Fam true` would put the exponent of `shiftPerm ^ _` at the
type `Fam true`, which whnfs to a `match` on `Bool` and leaves `HPow` unsolvable.
Every exponent below is an honest `ℤ`. -/
theorem psi_tLet : psi tLet = shiftPerm := by
  simp [psi, tLet, emT, psiFactor]
  show zpowersHom (Equiv.Perm ℤ) shiftPerm (Multiplicative.ofAdd (1 : ℤ)) = shiftPerm
  rw [zpowersHom_apply, toAdd_ofAdd, zpow_one]

theorem psi_sLet : psi sLet = negPerm := by
  simp [psi, sLet, emF, psiFactor]
  show zpowersHom (Equiv.Perm ℤ) negPerm (Multiplicative.ofAdd (1 : ℤ)) = negPerm
  rw [zpowersHom_apply, toAdd_ofAdd, zpow_one]

/-- The commutator of the relator with a source letter. -/
def bad (m : ℕ) : CoprodI Fam := tLet ^ m * (sLet * (tLet ^ m)⁻¹ * sLet⁻¹)

theorem bad_def (m : ℕ) :
    bad m = tLet ^ m * (sLet * (tLet ^ m)⁻¹ * sLet⁻¹) := rfl

theorem psi_bad_apply (m : ℕ) : psi (bad m) 0 = (m : ℤ) + m := by
  have hpsi : psi (bad m)
      = shiftPerm ^ m * (negPerm * (shiftPerm ^ m)⁻¹ * negPerm⁻¹) := by
    simp only [bad_def, map_mul, map_inv, map_pow, psi_tLet, psi_sLet]
  rw [hpsi]
  simp only [Equiv.Perm.mul_apply, negPerm_inv_apply, shiftPerm_pow_inv_apply,
    negPerm_apply, shiftPerm_pow_apply]
  ring

theorem bad_ne_one (m : ℕ) (hm : 1 ≤ m) : bad m ≠ 1 := by
  intro h
  have h0 : psi (bad m) 0 = (0 : ℤ) := by simp [h]
  rw [psi_bad_apply] at h0
  omega

theorem bad_mem (m : ℕ) : bad m ∈ letterRelatorSubgroup (relSet m) := by
  have hwp : tLet ^ m ∈ letterRelatorSubgroup (relSet m) := by
    rw [← prod_w m]
    exact mem_letterRelatorSubgroup (w_mem m)
  rw [bad_def]
  exact mul_mem hwp
    ((letterRelatorSubgroup_normal (relSet m)).conj_mem _ (inv_mem hwp) sLet)

/-- **The abelianisation does not see the commutator.**  This is the whole of
why the collapse model is a collapse. -/
theorem ab_bad (m : ℕ) : ab (bad m) = 0 := by
  simp only [bad_def, ab_mul, ab_inv]
  abel

theorem L_len_bad (m : ℕ) : L.len (bad m) ≤ 1 := by
  refine L_len_le_one_of_abNorm ?_
  rw [ab_bad]
  simp

/-- **The unit ball of `L` contains every commutator of the two factors.**  So
`L` is not the word metric of an alphabet `X ∪ U` with `X` finite, which is the
alphabet Osin's Theorem 2.4 is stated over, and no clause of `RelativeLength`
excludes it. -/
theorem L_len_commutator_le_one (x : Fam false) (y : Fam true) :
    L.len (CoprodI.of x * CoprodI.of y * (CoprodI.of x)⁻¹ * (CoprodI.of y)⁻¹)
      ≤ 1 := by
  refine L_len_le_one_of_abNorm ?_
  have hz : ab (CoprodI.of x * CoprodI.of y * (CoprodI.of x)⁻¹
      * (CoprodI.of y)⁻¹) = 0 := by
    simp only [ab_mul, ab_inv]
    abel
  rw [hz]
  simp

/-! ## 5.  The refutations -/

/-- **The Greendlinger conclusion fails at the witness**, for every `m ≥ 42`:
the commutator `[t^m, s]` is a nonidentity element of the relator subgroup of
length one, and every relator has `m ≥ 42` letters. -/
theorem not_relativeLengthBound (m : ℕ) (hm : 42 ≤ m) :
    ¬ RelativeLengthBound L (relSet m) := by
  refine not_relativeLengthBound_of_short (bad_ne_one m (by omega)) (bad_mem m) ?_
  intro r hr
  have h1 := L_len_bad m
  have h2 : r.length = m := length_of_mem hr
  omega

/-- **`OsinTheorem24Repaired` is false.**  Unlike
`not_weightedGreendlingerLeafRepaired_of_abelian_partner`, this needs no
weighted router design to exist: the family below meets both clauses the repair
added -- the relators are geodesic words and the pieces are compared in the
group -- and still kills a commutator. -/
theorem not_osinTheorem24Repaired : ¬ OsinTheorem24Repaired := by
  intro h
  have hleaf := (h Fam instFamGroup L (relSet 42) (1 / 7)).1
  exact not_relativeLengthBound 42 le_rfl
    (hleaf hasGeodesicSpellings_L (symmetrized 42) (reduced 42) (letters 42)
      (geodesic 42 (by norm_num)) (slack 42 le_rfl)
      (groupSmallCancellation (by norm_num)))

/-- **The third generation is false as well.**

This is the negation of the universal closure of `WeightedGreendlingerLeafFinal`
written out, quantifier order and all: `rho` is chosen after the length function
and before the relator family, exactly as
`GGT/RelHypOsinTheorem24Final.lean` asks.  The witness answers any `rho` by
taking `m = max rho 42`.

A consumer holding `OsinTheorem24Final` contradicts this by taking the first
component of the conjunction:

    fun h => not_weightedGreendlingerLeafFinal_universal
      (fun G inst LL lam => (h G inst LL lam).imp (fun _ hr R => (hr R).1))

which is the one-line bridge to add once both modules are in the closure. -/
theorem not_weightedGreendlingerLeafFinal_universal :
    ¬ ∀ (G : Bool → Type) (_ : ∀ b, Group (G b)) (LL : RelativeLength G) (lam : ℚ),
        ∃ rho : ℕ, ∀ R : Set (List (CoprodI G)),
          HasGeodesicSpellings LL → LetterSymmetrized R →
            (∀ r ∈ R, LetterReduced LL r) →
              (∀ r ∈ R, ∀ a ∈ r, LL.len a ≤ 1) →
                (∀ r ∈ R, LetterGeodesic LL r) → (∀ r ∈ R, rho ≤ r.length) →
                  LetterFragmentSlack R lam →
                    LetterMetricGroupSmallCancellation R lam →
                      RelativeLengthBound LL R := by
  intro h
  obtain ⟨rho, hleaf⟩ := h Fam instFamGroup L (1 / 7)
  have hm42 : 42 ≤ max rho 42 := le_max_right _ _
  have hmrho : rho ≤ max rho 42 := le_max_left _ _
  refine not_relativeLengthBound (max rho 42) hm42 ?_
  exact hleaf (relSet (max rho 42)) hasGeodesicSpellings_L (symmetrized _)
    (reduced _) (letters _) (geodesic _ (by omega))
    (fun r hr => by rw [length_of_mem hr]; exact hmrho)
    (slack _ hm42) (groupSmallCancellation (by omega))

end Osin24Collapse

end RelHyp
end GGT
end GroupApproximation
