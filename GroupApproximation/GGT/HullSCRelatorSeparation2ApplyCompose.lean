import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyFourWay
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyQG
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyShortSide
import GroupApproximation.GGT.HullSCRelatorSeparation2Cross
import GroupApproximation.GGT.HullSCRelatorSeparation2Statement
import GroupApproximation.GGT.HullSCRelatorSeparation2Inputs

/-!
# The separation, composed

The last file of the relator chain.  Above it is
`HullSC.hullRelatorStatement₂_of_separationNe₂`, which turns the corrected
separation into the form Hull's Theorem 5.1 consumes; below it are the four
piece-level cases, assembled at one quadrilateral by
`HullSC.listVal_conj_of_sym_pieces`.  What is between is the construction:
choose the base part, then the piece threshold, then the exponent list, in that
order, and hand the four-way the quadrilateral the separation's own hypotheses
describe.

## The order of the choices

`p` first, at length one and independently of the run length `L`, which is
(C1); then `B := |p| + blockSeparation + 2`, which is (C2) and which depends on
`|p|`, on the block-count constant `cnt`, and on the norm bound `eps` --- none
of them on `L`; then, for each `L`, an exponent list longer than
`|p| + 5 * blockSeparation + 2`, which is (C3).  The statement asks for `B`
before `L` and for `p` after it, and returning the same `p` for every `L` is
what makes those two compatible.

## The letters

The four-gon's letter clause is not a hypothesis of the separation, so it is
proved here: a member of the symmetrized closure is admissible because the
relator is, and admissibility survives rotation, formal inverse and reversal.
That is the first section.

## The constant

The polygon clause is produced here rather than assumed, by
`HullSC.fourGonQG_of_sides`, and that fixes the constant.  The two long sides
are prefixes of members of the closure, so their clause is the count; the two
short sides are base spellings of `y` and `z`, and for them the clause holds
because the constant exceeds their LENGTH --- there is no geometry to appeal
to, since a short element can lie in `H λ`, where its relative norm is one
while its base spelling has length `eps`.

So the composition does not work at the count's own constant `cnt` but at
`max cnt (eps + 2)`, which it chooses itself.  Enlarging the constant only
weakens the count, and `eps` is given before anything here is chosen, so
nothing circular is asked of the caller: `cnt` stays a constant of the core.

## What rides through

Three named hypotheses, and no others beyond the geometry of the ambient graph.

* `hcount` --- item 2 of the Ledger, the block count, at every member of the
  symmetrized closure rather than at the relator alone;
* `hexcl` --- item 3, the two same-side exclusions, each carrying the
  component-start clause without which it is refuted by
  `HullSC.not_sideExclusion_of_isComp`;
There is no third.  The chain used to carry a diagonal leaf --- that no
nontrivial element of a relative ball commutes with a power of the loxodromic
--- and `GGT/HullSCRelatorSeparation2ApplyLoxGap.lean` records why it could not
be discharged: `HullSC.noCommute_of_torsionFree` asks its element to be
loxodromic in the RELATIVE graph, and the relator's letters are powers of
elements OF the family, which are elliptic there.  Hull never needs it.  What
makes the aligned case's connector trivial is (W4), `E.disjoint`, a FIELD of
the core, so the exponent design is the plain
`HullSC.exists_separated_relator_exponents₂_cross` again.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Admissible letters -/

section Letters

variable {G : Type u} [Group G] {Λ : Type v}

/-- **Inverting a letter keeps it admissible**, for the inversion the formal
inverse of a relator uses. -/
theorem isLetter_relWordInv (D : GGT.RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {a : GGT.RelLetter G Λ}
    (hlet : D.IsLetter a) : D.IsLetter (RelWord.inv a) := by
  cases a with
  | base x => exact hsymm x hlet
  | comp lam h => exact inv_mem hlet

/-- **A rotation of an admissible word is admissible.** -/
theorem isAdmissible_rotate {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} (h : RelWord.IsAdmissible D v) (n : ℕ) :
    RelWord.IsAdmissible D (v.rotate n) :=
  fun a ha => h a (List.mem_rotate.mp ha)

/-- **The formal inverse of an admissible word is admissible.** -/
theorem isAdmissible_revInv {D : GGT.RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v : List (GGT.RelLetter G Λ)}
    (h : RelWord.IsAdmissible D v) :
    RelWord.IsAdmissible D (RelWord.revInv v) := by
  intro a ha
  rw [RelWord.revInv, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact isLetter_relWordInv D hsymm (h b hb)

/-- **Every member of the symmetrized closure of an admissible word is
admissible.** -/
theorem isAdmissible_sym {D : GGT.RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v w : List (GGT.RelLetter G Λ)}
    (hw : RelWord.Sym v w) (h : RelWord.IsAdmissible D v) :
    RelWord.IsAdmissible D w := by
  induction hw with
  | base => exact h
  | rot n _hs ih => exact isAdmissible_rotate ih n
  | inv _hs ih => exact isAdmissible_revInv hsymm ih

/-- **The reversal of an admissible word is admissible**, for the reversal the
four-gon's fourth side uses. -/
theorem isAdmissible_revWord {D : GGT.RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v : List (GGT.RelLetter G Λ)}
    (h : RelWord.IsAdmissible D v) :
    RelWord.IsAdmissible D (GGT.OsinComponents.revWord v) := by
  intro a ha
  rw [GGT.OsinComponents.revWord, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact GGT.OsinComponents.isLetter_invLetter D hsymm (h b hb)

end Letters

section RelatorLetters

variable {G : Type u} [Group G]

/-- **The run's letters are admissible**, being powers of elements of the two
subgroups. -/
theorem isLetter_of_mem_blockWord {D : GGT.RelGenSet G Bool} {a : Bool → G}
    (ha : ∀ b : Bool, a b ∈ D.fam b) :
    ∀ (s : Bool) (ms : List ℕ), ∀ x ∈ blockWord (a false) (a true) s ms,
      D.IsLetter x := by
  intro s ms
  induction ms generalizing s with
  | nil =>
      intro x hx
      rw [blockWord_nil] at hx
      cases hx
  | cons m t ih =>
      intro x hx
      rw [blockWord_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · show (if s then a true else a false) ^ m ∈ D.fam s
        rw [ite_apply_eq a s]
        exact pow_mem (ha s) m
      · exact ih (!s) x hx

/-- **The relator is admissible.** -/
theorem isAdmissible_relatorWord₂ {D : GGT.RelGenSet G Bool} {p : List G}
    (hp : ∀ g ∈ p, g ∈ D.base) {a : Bool → G} (ha : ∀ b : Bool, a b ∈ D.fam b)
    (ms : List ℕ) :
    RelWord.IsAdmissible D (relatorWord₂ p (a false) (a true) ms) := by
  intro x hx
  rw [relatorWord₂, List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hp g hg
  · exact isLetter_of_mem_blockWord ha false ms x hx

end RelatorLetters

/-! ## The composition -/

section Compose

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The corrected separation, composed from the two open geometric items.**

The construction is (C1)--(C3) and nothing else: `p` at length one before `B`,
`B := |p| + blockSeparation + 2`, and the run past `|p| + 5 * blockSeparation`.
Everything the four-way asks of the design --- the exponents distinct, deep
and separated --- comes from
`HullSC.exists_separated_relator_exponents₂_cross` at radius
`max rho (Cm * 4)`, which is the given `rho` enlarged to what the matching step
wants; the given `rho` is recovered by `HullSC.notMem_relBall_of_le`. -/
theorem separationNe₂_clause_of_spelling_of_producer (E : HypEmbeddedCore₂ A N)
    (hN : Suitable A.alphabet N) (cnt : ℕ) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ)
    (t : G) (p : List G) (hp0 : 0 < p.length)
    (hpbase : ∀ g ∈ p, g ∈ E.rel.base) (hpprod : p.prod = t⁻¹)
    (hcount : ∀ (ms : List ℕ)
      (v : List (GGT.RelLetter G Bool)),
      RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v →
      ∀ i j : ℕ, i ≤ j → j ≤ v.length →
        j - i ≤ wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) v i)
          (GGT.OsinComponents.vertex (1 : G) v j) + blockConst p cnt)
    (eps rho : ℕ)
    (hproduce : ∀ (epsD Cm L : ℕ),
      ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
        (∀ m ∈ ms, ∀ s t : Bool,
          E.lox s ^ m ∉ E.rel.relBall t (max rho (Cm * 4)) ∧
            (E.lox s ^ m)⁻¹ ∉ E.rel.relBall t (max rho (Cm * 4))) ∧
        (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool,
          ∀ x ∈ E.rel.relBall s epsD, ∀ x' ∈ E.rel.relBall s epsD,
            x * E.lox s ^ i * x' ≠ E.lox s ^ j ∧
              x * E.lox s ^ i * x' ≠ (E.lox s ^ j)⁻¹) ∧
        RelatorSideExclusionAt₂ E p ms) :
    ∃ B : ℕ, ∀ L : ℕ, ∃ (p : List G) (ms : List ℕ),
      (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
        (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
          (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
        ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
          RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
            RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
              w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                B < u₀.length →
                  ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                    wordNorm E.rel.base z ≤ eps →
                      GGT.RelLetter.listVal u₀'
                          = y * GGT.RelLetter.listVal u₀ * z →
                        GGT.RelLetter.listVal w'
                          = y * GGT.RelLetter.listVal w * y⁻¹ := by
  have hsymm : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base :=
    fun g hg => (isSymmetricGeneratingSet_base₂ E).inv_mem g hg
  have hloxfam : ∀ b : Bool, E.lox b ∈ E.rel.fam b := by
    intro b
    rw [E.fam_eq]
    exact E.lox_mem b
  have hdisj : ∀ x : G, x ∈ E.rel.fam false → x ∈ E.rel.fam true → x = 1 := by
    rw [E.fam_eq]
    exact E.disjoint
  set cw := max cnt (eps + 2) with hcw
  have hmono : blockConst p cnt ≤ blockConst p cw := by
    show p.length + cnt ≤ p.length + cw
    omega
  have hshort : eps + 2 ≤ blockConst p cw := by
    show eps + 2 ≤ p.length + cw
    omega
  obtain ⟨epsD, _hepsD, hpair⟩ :=
    GGT.OsinComponents.exists_eps_matchedPair_hyp E.rel hsymm
      (blockConst p cw) hδ
  obtain ⟨Cm, _hCm, hmatch⟩ :=
    GGT.OsinComponents.exists_deep_match_hyp E.rel hsymm (blockConst p cw) hδ
  refine ⟨p.length + blockSeparation p cw eps + 2, ?_⟩
  intro L
  obtain ⟨ms, hlen, hnodup, hdeepD, hsepD, hexcl⟩ :=
    hproduce epsD Cm (max L (p.length + 5 * blockSeparation p cw eps + 3))
  have hadm : RelWord.IsAdmissible E.rel
      (relatorWord₂ p (E.lox false) (E.lox true) ms) :=
    isAdmissible_relatorWord₂ hpbase hloxfam ms
  refine ⟨p, ms, hpbase, hpprod, le_trans (Nat.le_max_left L _) hlen, ?_, ?_⟩
  · intro m hm b
    exact ⟨notMem_relBall_of_le (Nat.le_max_left rho (Cm * 4))
        (hdeepD m hm b b).1,
      notMem_relBall_of_le (Nat.le_max_left rho (Cm * 4)) (hdeepD m hm b b).2⟩
  · intro w w' u₀ u₀' hw hw' _hne hpre hpre' hBu y z hy hz hcl
    obtain ⟨sfx, hsfx⟩ := hpre
    obtain ⟨sfx', hsfx'⟩ := hpre'
    obtain ⟨py, hpy0, hpylen, hpy, hpylet, hpyval, hpynorm⟩ :=
      exists_side_spelling₂ E hN hy
    obtain ⟨pz, hpz0, hpzlen, hpz, hpzlet, hpzval, _hpznorm⟩ :=
      exists_side_spelling₂ E hN hz
    have hwadm : RelWord.IsAdmissible E.rel w := isAdmissible_sym hsymm hw hadm
    have hw'adm : RelWord.IsAdmissible E.rel w' :=
      isAdmissible_sym hsymm hw' hadm
    have hqlet : ∀ x ∈ u₀, E.rel.IsLetter x := by
      intro x hx
      refine hwadm x ?_
      rw [hsfx]
      exact List.mem_append_left _ hx
    have hslet : ∀ x ∈ u₀', E.rel.IsLetter x := by
      intro x hx
      refine hw'adm x ?_
      rw [hsfx']
      exact List.mem_append_left _ hx
    have hlet4 : ∀ x ∈ py ++ u₀ ++ pz ++ GGT.OsinComponents.revWord u₀',
        E.rel.IsLetter x := by
      intro x hx
      rcases List.mem_append.mp hx with hx1 | hx2
      · rcases List.mem_append.mp hx1 with hx3 | hx4
        · rcases List.mem_append.mp hx3 with hx5 | hx6
          · exact hpylet x hx5
          · exact hqlet x hx6
        · exact hpzlet x hx4
      · exact isAdmissible_revWord hsymm hslet x hx2
    have hclose : GGT.RelLetter.listVal u₀' = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal u₀ * GGT.RelLetter.listVal pz := by
      rw [hpyval, hpzval]
      exact hcl
    have hlongp : p.length + blockSeparation p cw eps + 1 < u₀.length := by
      omega
    have hmslong :
        p.length + 5 * blockSeparation p cw eps + 2 < ms.length := by
      omega
    have hcu : ∀ i j : ℕ, i ≤ j → j ≤ u₀.length →
        j - i ≤ wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u₀ i)
          (GGT.OsinComponents.vertex (1 : G) u₀ j) + blockConst p cw := by
      intro i j hij hj
      have hvi : GGT.OsinComponents.vertex (1 : G) u₀ i
          = GGT.OsinComponents.vertex (1 : G) w i := by
        rw [hsfx]
        exact (GGT.OsinComponents.vertex_append_of_le u₀ sfx 1 i
          (by omega)).symm
      have hvj : GGT.OsinComponents.vertex (1 : G) u₀ j
          = GGT.OsinComponents.vertex (1 : G) w j := by
        rw [hsfx]
        exact (GGT.OsinComponents.vertex_append_of_le u₀ sfx 1 j hj).symm
      have hwlen : j ≤ w.length := by
        rw [hsfx, List.length_append]
        omega
      have hc := hcount ms w hw i j hij hwlen
      rw [hvi, hvj]
      omega
    have hcu' : ∀ i j : ℕ, i ≤ j → j ≤ u₀'.length →
        j - i ≤ wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u₀' i)
          (GGT.OsinComponents.vertex (1 : G) u₀' j) + blockConst p cw := by
      intro i j hij hj
      have hvi : GGT.OsinComponents.vertex (1 : G) u₀' i
          = GGT.OsinComponents.vertex (1 : G) w' i := by
        rw [hsfx']
        exact (GGT.OsinComponents.vertex_append_of_le u₀' sfx' 1 i
          (by omega)).symm
      have hvj : GGT.OsinComponents.vertex (1 : G) u₀' j
          = GGT.OsinComponents.vertex (1 : G) w' j := by
        rw [hsfx']
        exact (GGT.OsinComponents.vertex_append_of_le u₀' sfx' 1 j hj).symm
      have hwlen : j ≤ w'.length := by
        rw [hsfx', List.length_append]
        omega
      have hc := hcount ms w' hw' i j hij hwlen
      rw [hvi, hvj]
      omega
    have hqg := fourGonQG_of_sides E.rel (le_trans hpylen hshort)
      (le_trans hpzlen hshort) hcu hcu'
    have hqgq : ∀ i j : ℕ, i ≤ j → j ≤ u₀.length →
        ((j - i : ℕ) : ℝ) / 1 - ((blockConst p cw : ℕ) : ℝ)
          ≤ ((wordDist E.rel.alphabet.carrier
                (GGT.OsinComponents.vertex (1 : G) u₀ i)
                (GGT.OsinComponents.vertex (1 : G) u₀ j) : ℕ) : ℝ) :=
      fun i j hij hj => qgClause_of_le (hcu i j hij hj)
    have hqgs : ∀ i j : ℕ, i ≤ j → j ≤ u₀'.length →
        ((j - i : ℕ) : ℝ) / 1 - ((blockConst p cw : ℕ) : ℝ)
          ≤ ((wordDist E.rel.alphabet.carrier
                (GGT.OsinComponents.vertex (1 : G) u₀' i)
                (GGT.OsinComponents.vertex (1 : G) u₀' j) : ℕ) : ℝ) :=
      fun i j hij hj => qgClause_of_le (hcu' i j hij hj)
    obtain ⟨hqside, hsside⟩ :=
      hexcl py pz u₀ u₀' ⟨w, sfx, hw, hsfx⟩ ⟨w', sfx', hw', hsfx'⟩
        hpy hpz
    have hconj := listVal_conj_of_sym_pieces hpair hmatch hnodup
      (injective_pow_lox₂ E) hsymm hsepD hdisj
      (fun m hm b => hdeepD m hm b b) (Nat.le_max_right rho (Cm * 4)) hp0
      hw hw' hsfx hsfx' hlongp hmslong hpy hpz hpy0 hpz0 hlet4 hclose hqg
      hqlet hslet hqgq hqgs (le_refl _) hpynorm hqside hsside
    rw [hpyval] at hconj
    exact hconj

end Compose

end HullSC
end GroupApproximation
