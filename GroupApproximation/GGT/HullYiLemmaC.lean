import GroupApproximation.GGT.DGOPolygonSideCountAll
import GroupApproximation.GGT.DGOIsolatedComponentCut

/-!
# Hull's Lemma C at a fixed side count, and the separation it proves

Hull, *Small cancellation in acylindrically hyperbolic groups*
(arXiv:1308.4345), Lemma C, is Dahmani--Guirardel--Osin's Proposition 4.14
verbatim -- Hull states it as `\cite[Proposition 4.14]{DGO}`:

> Suppose `{H λ} ↪_h G`.  Then there is a constant `C` such that if
> `P = p₁…p_n` is a geodesic `n`-gon in `Γ(G, X ⊔ ℋ)` and `I ⊆ {1,…,n}` is a
> set of indices at which `p_i` is an isolated `H_{λ_i}`-component of `P`, then
> `Σ_{i ∈ I} ℓ̂_{λ_i}(p_i) ≤ Cn`.

The `C` is uniform in `n`, and that uniformity is out of reach here: our tower
gives the bound with a constant that grows quadratically with the side count
(`OsinComponents.exists_isolatedComponentBound_nGon`, radius
`(N+1) · 25(δ+b+1) · (N+2)`), because Lemma 4.17's recursion costs `C ↦ C₁+C₂`
per step and only Dahmani--Guirardel--Osin's balanced cut (their 4.20) and
recursion calculus (4.19) bring it down to `Dn`.

**But the two places Hull applies Lemma C directly do not need uniformity**, and
this module supplies them.  In the proof of his Lemma `nonelsub` the step is
*"`ab` cannot belong to `H₃` by Lemma C"*, and in the proof of Lemma `yi` it is
*"`a₁…a_{k-1} ∉ E_G(f_k)` by Lemma C"*; at `k = 3` both are one and the same
statement about a product of two letters, and the polygon is a triangle.  The
side count is fixed before the constant is asked for, so a constant that grows
with the side count costs nothing: Hull's threshold is `d̂ ≥ 50C`, chosen after
`C`.

Where uniformity is genuinely needed is Lemma 4.21(b) -- the `K` consecutive
connected components -- whose counting takes the polygon with every *edge* as a
side, so that `n ≈ ℓ(Q)` grows with the words.  That is the one input still
missing under Hull's §5, and nothing here reaches it.

## The triangle

If `a ∈ H_λ`, `b ∈ H_μ` and `ab ∈ H_ν`, then

    a · b · (ab)⁻¹

is a cycle of three letters, one from each family member.  When `λ`, `μ`, `ν`
are pairwise distinct no two of its letters share an index, so each letter is a
maximal run -- a component -- and each is isolated, there being no second
component of its own index to be connected to.  Every side is a single edge, so
the `(1,0)`-quasi-geodesic clause asks only that no letter has value `1`
(`isQuasiGeodesicPolygon_triWord`, on the pattern of
`OsinComponents.isQuasiGeodesicPolygon_pairWord`).  The bound at three sides
then puts `a` in a relative ball of a radius fixed in advance, so an `a` deeper
than that radius forces `ab ∉ H_ν`.

## What the hypotheses are doing

* `a * b ≠ 1` is **necessary, not technical**: `1` lies in every subgroup, so
  with `ab = 1` the conclusion `ab ∉ H_ν` is false outright.
* `b ≠ 1` is necessary for the polygon: a letter of value `1` is a side of
  length `0`, which is not a `(1,0)`-geodesic side.  (With `b = 1` the
  conclusion reads `a ∉ H_ν`, which this argument says nothing about; `H_λ ∩ H_ν`
  is finite by 4.33(b) but finiteness does not bound `d̂_λ`.)
* `a ≠ 1` is **not** assumed: it follows from `a` being outside a relative ball,
  since `1` lies in all of them.
* Only `a` need be deep.  Hull takes both `a` and `b` deep because he needs the
  second one later, not for this step.
* `μ ≠ ν` is not needed either: what isolates the `λ`-component is that neither
  of the other two letters is a `λ`-letter.
-/

namespace GroupApproximation
namespace GGT
namespace HullYi

open GroupApproximation.WordMetric
open OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The three-letter cycle -/

/-- **The cycle `a · b · (ab)⁻¹`**, spelled with one letter from each of three
family members.  It is the polygon behind Hull's Lemma C separation. -/
def triWord (lam mu nu : Λ) (a b : G) : List (RelLetter G Λ) :=
  [RelLetter.comp lam a, RelLetter.comp mu b, RelLetter.comp nu (a * b)⁻¹]

theorem length_triWord (lam mu nu : Λ) (a b : G) :
    (triWord lam mu nu a b).length = 3 := rfl

theorem listVal_triWord (lam mu nu : Λ) (a b : G) :
    RelLetter.listVal (triWord lam mu nu a b) = 1 := by
  simp only [triWord, RelLetter.listVal, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, RelLetter.val]
  group

/-- The three letters are admissible exactly when each lies in its own family
member; the third one does because subgroups are closed under inversion. -/
theorem isLetter_triWord (D : RelGenSet G Λ) {lam mu nu : Λ} {a b : G}
    (ha : a ∈ D.fam lam) (hb : b ∈ D.fam mu) (hab : a * b ∈ D.fam nu) :
    ∀ c ∈ triWord lam mu nu a b, D.IsLetter c := by
  intro c hc
  have hc3 : c = RelLetter.comp lam a ∨ c = RelLetter.comp mu b ∨
      c = RelLetter.comp nu (a * b)⁻¹ := by
    simpa [triWord] using hc
  rcases hc3 with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact inv_mem hab

/-- **The cycle is a `(1,b')`-quasi-geodesic triangle** at every defect
`b' ≥ 0`.  Its cut function is the identity, so each side is a single edge and
the clause asks only that no letter has value `1`. -/
theorem isQuasiGeodesicPolygon_triWord (D : RelGenSet G Λ) {b' : ℝ}
    (hb' : 0 ≤ b') {lam mu nu : Λ} {a b : G} (ha : a ∈ D.fam lam)
    (hb : b ∈ D.fam mu) (hab : a * b ∈ D.fam nu) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab1 : a * b ≠ 1) :
    IsQuasiGeodesicPolygon D 1 b' 3 1 (triWord lam mu nu a b) := by
  have hlen : (triWord lam mu nu a b).length = 3 := length_triWord lam mu nu a b
  have hval : ∀ (j : ℕ) (hj : j < (triWord lam mu nu a b).length),
      ((triWord lam mu nu a b)[j]'hj).val ≠ 1 := by
    intro j hj
    have hj3 : j < 3 := by omega
    interval_cases j
    · exact ha1
    · exact hb1
    · exact inv_ne_one.mpr hab1
  refine ⟨isLetter_triWord D ha hb hab, listVal_triWord lam mu nu a b,
    fun s => s, rfl, (length_triWord lam mu nu a b).symm,
    fun s => Nat.le_succ s, ?_⟩
  intro s _ p q hp hpq hq
  have hp' : s ≤ p := hp
  have hq' : q ≤ s + 1 := hq
  rw [div_one]
  refine le_trans (sub_le_self _ hb') ?_
  have key : q - p ≤ wordDist D.alphabet.carrier
      (vertex (1 : G) (triWord lam mu nu a b) p)
      (vertex (1 : G) (triWord lam mu nu a b) q) := by
    rcases Nat.eq_or_lt_of_le hpq with heq | hlt
    · rw [heq, Nat.sub_self]
      exact Nat.zero_le _
    · have hq1 : q = p + 1 := by omega
      subst hq1
      have hpw : p < (triWord lam mu nu a b).length := by omega
      have hstep := one_le_wordDist_vertex_succ D 1 (triWord lam mu nu a b) p hpw
        (hval p hpw)
      omega
  exact_mod_cast key

/-! ## The first letter is an isolated component -/

/-- The first letter is an `H lam`-component: it is a `lam`-letter and the
letter after it is not. -/
theorem isComp_triWord_zero {lam mu nu : Λ} (hlm : lam ≠ mu) (a b : G) :
    IsComp lam (triWord lam mu nu a b) 0 1 := by
  have hlen : (triWord lam mu nu a b).length = 3 := length_triWord lam mu nu a b
  refine ⟨Nat.zero_lt_one, by omega, ?_, ?_, ?_⟩
  · intro j _ hj1 hjw
    have hj0 : j = 0 := by omega
    subst hj0
    exact rfl
  · intro j hj
    exact absurd hj (by omega)
  · intro _ hc
    have hml : mu = lam := hc
    exact hlm hml.symm

/-- **The first letter is isolated**: the only other candidates for a
`lam`-component start carry the indices `mu` and `nu`, and neither is `lam`. -/
theorem isIsolated_triWord_zero (D : RelGenSet G Λ) {lam mu nu : Λ}
    (hlm : lam ≠ mu) (hln : lam ≠ nu) (a b : G) :
    IsIsolated D.fam lam 1 (triWord lam mu nu a b) 0 := by
  have hlen : (triWord lam mu nu a b).length = 3 := length_triWord lam mu nu a b
  refine ⟨⟨1, isComp_triWord_zero hlm a b⟩, ?_⟩
  rintro j hj ⟨k, hk⟩ -
  have hjk : j < k := hk.1
  have hk3 : k ≤ (triWord lam mu nu a b).length := hk.2.1
  have hjw : j < (triWord lam mu nu a b).length := by omega
  have hletter := hk.2.2.1 j le_rfl hjk hjw
  have hj12 : j = 1 ∨ j = 2 := by omega
  rcases hj12 with rfl | rfl
  · have hml : mu = lam := hletter
    exact hlm hml.symm
  · have hnl : nu = lam := hletter
    exact hln hnl.symm

/-! ## Hull's separation step -/

/-- **Hull's Lemma C, in the form his Lemmas `nonelsub` and `yi` consume.**

There is a radius `R`, depending only on the alphabet and its hyperbolicity
constant, such that a letter `a` of one family member lying *deeper* than `R`
cannot have `a * b` in a third family member, for any letter `b` of a second
one.  This is *"`ab` cannot belong to `H₃` by Lemma C"* and
*"`a₁…a_{k-1} ∉ E_G(f_k)` by Lemma C"*, which at `k = 3` coincide.

`R` is quantified before the three indices, so one threshold serves the whole
family -- which is what Hull's `50C` needs, `C` being fixed before the `a_i` are
chosen. -/
theorem exists_radius_notMem_fam_mul (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ R : ℕ, ∀ (lam mu nu : Λ) (a b : G), lam ≠ mu → lam ≠ nu →
      a ∈ D.fam lam → b ∈ D.fam mu → b ≠ 1 → a * b ≠ 1 →
        a ∉ D.relBall lam R → a * b ∉ D.fam nu := by
  obtain ⟨R, hR⟩ := exists_isolatedComponentBound_nGon D hsymm 0 hδ 3
  refine ⟨R, ?_⟩
  intro lam mu nu a b hlm hln ha hb hb1 hab1 hdeep hab
  have ha1 : a ≠ 1 := by
    intro h
    apply hdeep
    rw [h]
    exact one_mem_relBall D lam R
  have hpoly : IsQuasiGeodesicPolygon D 1 ((0 : ℕ) : ℝ) 3 1
      (triWord lam mu nu a b) :=
    isQuasiGeodesicPolygon_triWord D (Nat.cast_nonneg 0) ha hb hab ha1 hb1 hab1
  have hspan := hR 1 (triWord lam mu nu a b) hpoly lam 0 1
    (isComp_triWord_zero hlm a b) (isIsolated_triWord_zero D hlm hln a b)
  have hvert : (vertex (1 : G) (triWord lam mu nu a b) 0)⁻¹ *
      vertex (1 : G) (triWord lam mu nu a b) 1 = a := by
    show (1 : G)⁻¹ * (1 * a) = a
    group
  rw [hvert] at hspan
  exact hdeep hspan

end HullYi
end GGT
end GroupApproximation
