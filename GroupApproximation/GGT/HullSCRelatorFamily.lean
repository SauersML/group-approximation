import GroupApproximation.GGT.HullSCSmallCancellation

/-!
# The symmetrized family of one relator, and Hull's §6 reduced to an estimate

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii and after D. Osin,
*Small cancellations over relatively hyperbolic groups and embedding theorems*,
Ann. of Math. 172 (2010), §4.

`HullSC.HullRelatorStatement` asks for a `C(ε, μ, ρ)` family containing a word
spelling `t⁻¹u` with `u ∈ N`.  Five of the six clauses of
`RelWord.IsSmallCancellation` are bookkeeping about the *family*, and Hull's §6
never argues them: the family is the symmetrized closure of a single relator, so
closure under cyclic permutation and formal inversion holds by construction and
the length, admissibility and depth clauses are inherited from the one word.
This module discharges all five and leaves the sixth.

## What the plan for the sixth clause is

`pieces_small` is Hull's estimate and it is the only content of §6.  The
reduction here splits it in two, which is how Olshanskii's argument runs:

* **A length bound.**  `pieces_small_of_longMatch`: if every `ε`-match of a
  prefix longer than `B` is a *global translation* of the relator -- the case
  Olshanskii's exclusion clause carves out, `listVal w' = y (listVal w) y⁻¹` --
  then every `ε`-piece has length at most `B`, and `B < μ |v|` finishes.  So
  the estimate never has to mention `μ`: it has to produce a constant `B`, and
  then the relator is taken long enough.
* **The separation itself**, which is what `RelatorChoice` records.  Hull's
  relator is `v = p · h₁^{n₁} h₂^{n₂} ⋯` with `p` a base spelling of `t⁻¹` and
  the `H`-letters deep, and the two facts that make the matches short are
  available in this repository rather than assumed:
  `HullGeometry.IsLoxodromic` for `E.lox` gives `|a^n|_A ≥ l n - B₀`, so two
  powers of `a` at different exponents cannot be joined by base words of length
  at most `ε`; and `E.embedded.locallyFinite` makes `relBall ρ` finite, so all
  but finitely many powers of `a` are legal deep letters.  What is *not* yet in
  the repository, and what the estimate needs, is the acylindricity input:
  `A.acylindrical` bounds the number of elements moving a long segment of the
  axis of `a` a bounded amount, which is what rules out a match whose
  conjugator `y` is short but does not commute with `a`.  That is the shape of
  the remaining work, and it is why the leaf is stated with the conjugator
  quantified.

`u` itself is free: the `H`-letters are powers of `E.lox ∈ E.H ≤ N`, so their
product lies in `N`, and `u = t · listVal v` is that product.  The clause
`u ∈ N` is therefore not part of the estimate either.

## What the family is

`RelWord.Sym v` is the closure of `{v}` under cyclic permutation and formal
inversion, taken inductively so that two of the six clauses are constructors.
`RelWord.Sym.exists_rotate` identifies its members concretely -- the rotations
of `v` and the rotations of `revInv v` -- which is what an attack on the
estimate needs, and it rests on `RelWord.revInv_rotate`: reversing and inverting
a cyclic permutation is a cyclic permutation of the reversed inverse, by the
complementary amount.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelWord

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The value of a word, letter by letter -/

/-- The value of a word with one letter split off. -/
theorem listVal_cons (a : GGT.RelLetter G Λ) (t : List (GGT.RelLetter G Λ)) :
    GGT.RelLetter.listVal (a :: t) = a.val * GGT.RelLetter.listVal t := by
  show ((a :: t).map GGT.RelLetter.val).prod
    = a.val * (t.map GGT.RelLetter.val).prod
  rw [List.map_cons, List.prod_cons]

/-- The value of a one-letter word. -/
theorem listVal_singleton (a : GGT.RelLetter G Λ) :
    GGT.RelLetter.listVal [a] = a.val := by
  show ([a].map GGT.RelLetter.val).prod = a.val
  rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-! ## Formal inversion -/

/-- Formal inversion is an involution on letters. -/
theorem inv_inv_letter (a : GGT.RelLetter G Λ) : inv (inv a) = a := by
  cases a with
  | base g =>
      show GGT.RelLetter.base g⁻¹⁻¹ = GGT.RelLetter.base g
      rw [inv_inv]
  | comp lam h =>
      show GGT.RelLetter.comp lam h⁻¹⁻¹ = GGT.RelLetter.comp lam h
      rw [inv_inv]

/-- Formal inversion does not change which component a letter belongs to. -/
theorem isCompOf_inv {lam : Λ} (a : GGT.RelLetter G Λ) :
    GGT.RelLetter.IsCompOf lam (inv a) ↔ GGT.RelLetter.IsCompOf lam a := by
  cases a <;> exact Iff.rfl

/-- Formal inversion carries legal letters to legal letters, the base being
symmetric and the family a family of subgroups. -/
theorem isLetter_inv {D : GGT.RelGenSet G Λ}
    (hbase : ∀ g ∈ D.base, g⁻¹ ∈ D.base) {a : GGT.RelLetter G Λ}
    (ha : D.IsLetter a) : D.IsLetter (inv a) := by
  cases a with
  | base g => exact hbase g ha
  | comp lam h => exact (D.fam lam).inv_mem ha

/-- The formal inverse of a one-letter word. -/
theorem revInv_singleton (a : GGT.RelLetter G Λ) : revInv [a] = [inv a] := rfl

/-- The formal inverse of a word with one letter split off. -/
theorem revInv_cons (a : GGT.RelLetter G Λ) (t : List (GGT.RelLetter G Λ)) :
    revInv (a :: t) = revInv t ++ [inv a] := by
  show ((a :: t).map inv).reverse = (t.map inv).reverse ++ [inv a]
  rw [List.map_cons, List.reverse_cons]

/-- Formal inversion reverses concatenation. -/
theorem revInv_append (v w : List (GGT.RelLetter G Λ)) :
    revInv (v ++ w) = revInv w ++ revInv v := by
  show ((v ++ w).map inv).reverse = (w.map inv).reverse ++ (v.map inv).reverse
  rw [List.map_append, List.reverse_append]

/-- Formal inversion preserves length. -/
theorem length_revInv (v : List (GGT.RelLetter G Λ)) :
    (revInv v).length = v.length := by
  show ((v.map inv).reverse).length = v.length
  rw [List.length_reverse, List.length_map]

/-- Formal inversion is an involution on words. -/
theorem revInv_revInv (v : List (GGT.RelLetter G Λ)) : revInv (revInv v) = v := by
  induction v with
  | nil => rfl
  | cons a t ih =>
      rw [revInv_cons, revInv_append, revInv_singleton, inv_inv_letter, ih]
      rfl

/-- A letter of the formal inverse is the formal inverse of a letter. -/
theorem inv_mem_of_mem_revInv {a : GGT.RelLetter G Λ}
    {v : List (GGT.RelLetter G Λ)} (h : a ∈ revInv v) : inv a ∈ v := by
  have h' : a ∈ (v.map inv).reverse := h
  rw [List.mem_reverse] at h'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h'
  rw [inv_inv_letter]
  exact hb

/-- **The formal inverse of a word names the inverse element.** -/
theorem listVal_revInv (v : List (GGT.RelLetter G Λ)) :
    GGT.RelLetter.listVal (revInv v) = (GGT.RelLetter.listVal v)⁻¹ := by
  induction v with
  | nil =>
      have h : revInv ([] : List (GGT.RelLetter G Λ)) = [] := rfl
      rw [h, GGT.RelLetter.listVal_nil, inv_one]
  | cons a t ih =>
      rw [revInv_cons, listVal_append, ih, listVal_singleton, val_inv,
        listVal_cons, mul_inv_rev]

/-- **Formal inversion turns a cyclic permutation into the complementary
one.**  Splitting `v` as `T ++ D` with `|T| = n`, the permutation is `D ++ T`,
whose formal inverse is `revInv T ++ revInv D`; and `revInv v` is
`revInv D ++ revInv T`, which the permutation by `|revInv D| = |v| - n` turns
into the same word. -/
theorem revInv_rotate (v : List (GGT.RelLetter G Λ)) {n : ℕ} (hn : n ≤ v.length) :
    revInv (v.rotate n) = (revInv v).rotate (v.length - n) := by
  have hsplit : v = v.take n ++ v.drop n := (List.take_append_drop n v).symm
  have h1 : revInv (v.rotate n) = revInv (v.take n) ++ revInv (v.drop n) := by
    rw [List.rotate_eq_drop_append_take hn, revInv_append]
  have h2 : revInv v = revInv (v.drop n) ++ revInv (v.take n) := by
    conv_lhs => rw [hsplit]
    rw [revInv_append]
  have hlen : (revInv (v.drop n)).length = v.length - n := by
    rw [length_revInv, List.length_drop]
  rw [h1, h2, ← hlen,
    List.rotate_eq_drop_append_take (by simp : (revInv (v.drop n)).length ≤
      (revInv (v.drop n) ++ revInv (v.take n)).length)]
  simp

/-- The formal inverse of a cyclic permutation is *some* cyclic permutation of
the formal inverse.  The index is `|v| - n mod |v|`, but only its existence is
used. -/
theorem exists_revInv_rotate (v : List (GGT.RelLetter G Λ)) (n : ℕ) :
    ∃ m : ℕ, revInv (v.rotate n) = (revInv v).rotate m := by
  rcases Nat.eq_zero_or_pos v.length with h0 | hpos
  · have hv : v = [] := List.length_eq_zero_iff.mp h0
    subst hv
    refine ⟨0, ?_⟩
    rw [List.rotate_nil, List.rotate_zero]
  · refine ⟨v.length - n % v.length, ?_⟩
    have hle : n % v.length ≤ v.length := le_of_lt (Nat.mod_lt _ hpos)
    have hrot : v.rotate n = v.rotate (n % v.length) := (List.rotate_mod v n).symm
    rw [hrot, revInv_rotate v hle]

/-! ## The symmetrized closure of one relator -/

/-- **The symmetrized closure of a relator**: the closure of `{v}` under cyclic
permutation and formal inversion.  Taken inductively, so that the two closure
clauses of `IsSmallCancellation` are constructors rather than lemmas. -/
inductive Sym (v : List (GGT.RelLetter G Λ)) : List (GGT.RelLetter G Λ) → Prop
  /-- The relator itself. -/
  | base : Sym v v
  /-- Cyclic permutations. -/
  | rot {w : List (GGT.RelLetter G Λ)} (n : ℕ) : Sym v w → Sym v (w.rotate n)
  /-- Formal inverses. -/
  | inv {w : List (GGT.RelLetter G Λ)} : Sym v w → Sym v (revInv w)

/-- Every member of the symmetrized closure has the length of the relator. -/
theorem Sym.length_eq {v w : List (GGT.RelLetter G Λ)} (h : Sym v w) :
    w.length = v.length := by
  induction h with
  | base => rfl
  | rot _n _hw ih =>
      rw [List.length_rotate]
      exact ih
  | inv _hw ih =>
      rw [length_revInv]
      exact ih

/-- Every letter of every member is a letter of the relator or the formal
inverse of one. -/
theorem Sym.letters {v w : List (GGT.RelLetter G Λ)} (h : Sym v w) :
    ∀ a ∈ w, a ∈ v ∨ RelWord.inv a ∈ v := by
  induction h with
  | base => exact fun a ha => Or.inl ha
  | rot _n _hw ih =>
      intro a ha
      exact ih a (List.mem_rotate.mp ha)
  | inv _hw ih =>
      intro a ha
      rcases ih (RelWord.inv a) (inv_mem_of_mem_revInv ha) with h1 | h1
      · exact Or.inr h1
      · rw [inv_inv_letter] at h1
        exact Or.inl h1

/-- **The members, concretely**: the cyclic permutations of the relator and the
cyclic permutations of its formal inverse.  This is what an attack on the
estimate has to range over. -/
theorem Sym.exists_rotate {v w : List (GGT.RelLetter G Λ)} (h : Sym v w) :
    (∃ n : ℕ, w = v.rotate n) ∨ (∃ n : ℕ, w = (revInv v).rotate n) := by
  induction h with
  | base => exact Or.inl ⟨0, (List.rotate_zero v).symm⟩
  | rot n _hw ih =>
      rcases ih with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine Or.inl ⟨m + n, ?_⟩
        rw [hm, List.rotate_rotate]
      · refine Or.inr ⟨m + n, ?_⟩
        rw [hm, List.rotate_rotate]
  | inv _hw ih =>
      rcases ih with ⟨m, hm⟩ | ⟨m, hm⟩
      · obtain ⟨k, hk⟩ := exists_revInv_rotate v m
        refine Or.inr ⟨k, ?_⟩
        rw [hm, hk]
      · obtain ⟨k, hk⟩ := exists_revInv_rotate (revInv v) m
        rw [revInv_revInv] at hk
        refine Or.inl ⟨k, ?_⟩
        rw [hm, hk]

/-- The symmetrized closure as a set of words. -/
def symmetrized (v : List (GGT.RelLetter G Λ)) :
    Set (List (GGT.RelLetter G Λ)) :=
  {w | Sym v w}

theorem mem_symmetrized {v w : List (GGT.RelLetter G Λ)} :
    w ∈ symmetrized v ↔ Sym v w := Iff.rfl

theorem self_mem_symmetrized (v : List (GGT.RelLetter G Λ)) :
    v ∈ symmetrized v := mem_symmetrized.mpr Sym.base

/-! ## Weakening the parameters -/

/-- The condition only gets easier as `μ` grows: a piece shorter than `μ|v|` is
shorter than `μ'|v|`. -/
theorem IsSmallCancellation.mono_mu {D : GGT.RelGenSet G Λ}
    {W : Set (List (GGT.RelLetter G Λ))} {eps rho : ℕ} {mu mu' : ℝ}
    (h : IsSmallCancellation D W eps mu rho) (hle : mu ≤ mu') :
    IsSmallCancellation D W eps mu' rho where
  admissible := h.admissible
  inv_mem := h.inv_mem
  rotate_mem := h.rotate_mem
  long := h.long
  deep := h.deep
  pieces_small := by
    intro u v hp
    have h1 := h.pieces_small u v hp
    have h2 : mu * (v.length : ℝ) ≤ mu' * (v.length : ℝ) :=
      mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
    linarith

/-! ## Five of the six clauses, discharged -/

/-- **The piece clause from a length bound.**

If every `ε`-match of a prefix longer than `B` is a global translation of the
relator -- the case Olshanskii's exclusion clause carves out -- then every
`ε`-piece has length at most `B`, and `B < μ|v|` gives `pieces_small`.

This is where `μ` leaves the estimate: what has to be produced is a constant
`B` that does not grow with the relator, and the relator is then taken long
enough. -/
theorem pieces_small_of_longMatch {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {eps : ℕ} {mu : ℝ} {B : ℕ}
    (hmatch : ∀ w w' u u' : List (GGT.RelLetter G Λ), Sym v w → Sym v w' →
      (∃ s, w = u ++ s) → (∃ s', w' = u' ++ s') → B < u.length →
      ∀ y z : G, wordNorm D.base y ≤ eps → wordNorm D.base z ≤ eps →
        GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z →
          GGT.RelLetter.listVal w'
            = y * GGT.RelLetter.listVal w * y⁻¹)
    (hB : (B : ℝ) < mu * v.length) :
    ∀ u w : List (GGT.RelLetter G Λ), IsPiece D (symmetrized v) eps u w →
      (u.length : ℝ) < mu * w.length := by
  intro u w hp
  obtain ⟨hw, hpre, w', hw', -, u', s', hw'eq, y, z, hy, hz, hval, hexcl⟩ := hp
  have hsw : Sym v w := mem_symmetrized.mp hw
  have hsw' : Sym v w' := mem_symmetrized.mp hw'
  have hlen : (w.length : ℝ) = (v.length : ℝ) := by
    rw [Sym.length_eq hsw]
  by_cases hbig : B < u.length
  · exact absurd
      (hmatch w w' u u' hsw hsw' hpre ⟨s', hw'eq⟩ hbig y z hy hz hval) hexcl
  · push Not at hbig
    have h1 : (u.length : ℝ) ≤ (B : ℝ) := by exact_mod_cast hbig
    rw [hlen]
    linarith

/-- **The five bookkeeping clauses of `C(ε, μ, ρ)`, for the symmetrized closure
of one relator.**  Closure under cyclic permutation and formal inversion are
constructors of `Sym`; length, admissibility and depth are inherited from the
relator through `Sym.length_eq` and `Sym.letters`.

The depth hypothesis is stated for the letter and its inverse, which is what
`Sym.letters` needs and what the construction supplies for free: `relBall ρ` is
finite (`GGT.RelGenSet.IsHyperbolicallyEmbedded.locallyFinite`), so all but
finitely many powers of a loxodromic element of `H` avoid it and its
inverse-image at once. -/
theorem isSmallCancellation_symmetrized {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {eps rho : ℕ} {mu : ℝ}
    (hbase : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hadm : ∀ a ∈ v, D.IsLetter a)
    (hlong : rho ≤ v.length)
    (hdeep : ∀ a ∈ v, ∀ lam : Λ, GGT.RelLetter.IsCompOf lam a →
      a.val ∉ D.relBall lam rho ∧ (a.val)⁻¹ ∉ D.relBall lam rho)
    (hpieces : ∀ u w : List (GGT.RelLetter G Λ),
      IsPiece D (symmetrized v) eps u w → (u.length : ℝ) < mu * w.length) :
    IsSmallCancellation D (symmetrized v) eps mu rho where
  admissible := by
    intro w hw a ha
    rcases Sym.letters (mem_symmetrized.mp hw) a ha with h1 | h1
    · exact hadm a h1
    · have h2 := isLetter_inv hbase (hadm _ h1)
      rwa [inv_inv_letter] at h2
  inv_mem := fun w hw => mem_symmetrized.mpr (Sym.inv (mem_symmetrized.mp hw))
  rotate_mem := fun w hw n =>
    mem_symmetrized.mpr (Sym.rot n (mem_symmetrized.mp hw))
  long := by
    intro w hw
    rw [Sym.length_eq (mem_symmetrized.mp hw)]
    exact hlong
  deep := by
    intro w hw a ha lam hcomp
    rcases Sym.letters (mem_symmetrized.mp hw) a ha with h1 | h1
    · exact (hdeep a h1 lam hcomp).1
    · have hcomp' : GGT.RelLetter.IsCompOf lam (inv a) :=
        (isCompOf_inv a).mpr hcomp
      have h2 := (hdeep (inv a) h1 lam hcomp').2
      rwa [val_inv, inv_inv] at h2
  pieces_small := hpieces

end RelWord

/-! ## Hull's §6, reduced to the estimate -/

/-- **Hull's §6, with the family bookkeeping removed.**

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let `N` be
> suitable, let `H ≤ N` be hyperbolically embedded with a loxodromic element,
> let `t ∈ G` and let `ε, ρ` and `μ > 0` be given.  Then there are `u ∈ N`, a
> word `v` over `A ⊔ H` spelling `t⁻¹u`, and a constant `B` with `B < μ|v|`,
> such that `v` has at least `ρ` letters, every letter of `v` is legal, every
> `H`-letter of `v` and its inverse escape the relative ball of radius `ρ`, and
> every `ε`-match of a prefix of a member of the symmetrized closure of `v`
> longer than `B` is a global translation of the member.

Everything else `HullRelatorStatement` asks for is proved:
`RelWord.isSmallCancellation_symmetrized` supplies the five family clauses and
`RelWord.pieces_small_of_longMatch` turns the last clause above into
`pieces_small`.

The last clause is Olshanskii's condition, and the exclusion it carves out is
the one the piece condition itself carries: a cyclic permutation of a relator
*is* a translation of it, by the prefix that was moved, so that case has to be
allowed and is (`RelWord.exists_naive_piece_of_rotate` is what happens when it
is not). -/
def RelatorChoice : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore A N), Suitable A.alphabet N → ∀ (t : G)
      (eps rho : ℕ) (mu : ℝ), 0 < mu →
        ∃ u ∈ N, ∃ (v : List (GGT.RelLetter G Unit)) (B : ℕ),
          GGT.RelLetter.listVal v = t⁻¹ * u ∧
            (∀ a ∈ v, E.rel.IsLetter a) ∧
            rho ≤ v.length ∧
            (∀ a ∈ v, ∀ lam : Unit, GGT.RelLetter.IsCompOf lam a →
              a.val ∉ E.rel.relBall lam rho ∧
                (a.val)⁻¹ ∉ E.rel.relBall lam rho) ∧
            (B : ℝ) < mu * v.length ∧
            ∀ w w' u₀ u₀' : List (GGT.RelLetter G Unit),
              RelWord.Sym v w → RelWord.Sym v w' →
                (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') → B < u₀.length →
                  ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                    wordNorm E.rel.base z ≤ eps →
                      GGT.RelLetter.listVal u₀'
                          = y * GGT.RelLetter.listVal u₀ * z →
                        GGT.RelLetter.listVal w'
                          = y * GGT.RelLetter.listVal w * y⁻¹

/-- **Hull's §6, from the estimate.**  The family is the symmetrized closure of
the relator, its five bookkeeping clauses are
`RelWord.isSmallCancellation_symmetrized`, and the sixth is
`RelWord.pieces_small_of_longMatch` applied to the estimate. -/
theorem hullRelatorStatement_of_relatorChoice (h : RelatorChoice.{u}) :
    HullRelatorStatement.{u} := by
  intro G _ A N E hN t eps rho mu hmu
  obtain ⟨u, huN, v, B, hval, hadm, hlong, hdeep, hB, hmatch⟩ :=
    h A N E hN t eps rho mu hmu
  have hbase : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base := by
    intro g hg
    rw [E.base_eq] at hg ⊢
    exact A.alphabet.symmetricGenerating.inv_mem g hg
  refine ⟨u, huN, RelWord.symmetrized v,
    ⟨v, RelWord.self_mem_symmetrized v, hval⟩, ?_⟩
  refine RelWord.isSmallCancellation_symmetrized hbase hadm hlong hdeep ?_
  exact RelWord.pieces_small_of_longMatch hmatch hB

/-- **Hull's Theorem 5.1 with the §6 relator**, with §6 reduced to the
estimate. -/
theorem hullTheorem51_of_relatorChoice (hrel : RelatorChoice.{u})
    (hquot : HullQuotientStatement.{u}) : HullTheorem51Statement.{u} :=
  hullTheorem51_of_relator_of_quotient
    (hullRelatorStatement_of_relatorChoice hrel) hquot

end HullSC
end GroupApproximation
