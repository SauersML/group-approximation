import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.DGOProposition433Ball
import GroupApproximation.GGT.OsinTheorem54SepSymmetricFam
import GroupApproximation.GGT.WPDDGOReduction

/-!
# Dahmani--Guirardel--Osin's Proposition 4.33: almost malnormality

Their statement has two halves, and this module proves both, in the form the
rest of the tree consumes --- finiteness of the intersection rather than a
diameter bound.

* (a) for `lam ≠ mu` and **any** `g`, `H_lam^g ∩ H_mu` is finite;
* (b) for `g ∉ H_lam`, `H_lam^g ∩ H_lam` is finite.

`GGT/DGOProposition433Ball.lean` proves the ball form of both at once, under the
single hypothesis that some geodesic word for the conjugator does not begin with
a `lam`-letter, and `exists_strip_fam_prefix` removes that hypothesis here, the
way the paper's own proof removes it: pass from `g` to the element `f` its
geodesic word spells after its maximal prefix of `lam`-letters is deleted.

## Finiteness transports, the ball does not

`g = x f` with `x ∈ H_lam`, so `H_lam^g ∩ H_mu` is the image of `H_lam^f ∩ H_mu`
under conjugation by `x`, and finiteness passes along a bijection.  The
`d_lam`-ball does **not**: at `mu = lam` and `g ∈ H_lam` the intersection is the
whole of `H_lam`, which is `d_lam`-unbounded whenever `H_lam` is infinite, so no
statement of the form "`H_lam^g ∩ H_mu ⊆ relBall lam A` for every `g`" is true.
That is why Proposition 4.33 is stated as a diameter bound measured through the
reduced conjugator, and why what is exported here is finiteness.

## What the exports are for

`finite_conj_pow_mem_fam` is the shape the windowed same-side exclusion of
`GGT/HullSCRelatorSeparation2Tails.lean` needs one level up from
`HullSC.finite_pow_mem_fam`: there the tail is trivial and a power of one
element lands in the other subgroup only finitely often, by
`HullSC.mem_relBall_one_of_mem_fam_ne` alone; here the power is conjugated by a
product of block letters, which no one-letter spelling reaches, and the
quadrilateral is what replaces it.

`dgoProposition433` discharges the named statement of `GGT/WPDDGOReduction.lean`
outright.  `DGOCorollary612Malnormal.dgoCorollary612_of_611` had already routed
around it at a letter of `X`; the general `a` is now available too, so the
citation is no longer owed in either form.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u w

section Malnormal

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Almost malnormality, both halves, over a symmetric base.**

The hypothesis `¬ (mu = lam ∧ g ∈ H_lam)` is exactly the disjunction of the two
halves of Proposition 4.33: it holds whenever `lam ≠ mu`, and at `lam = mu` it
is `g ∉ H_lam`.  It cannot be dropped: at `mu = lam` and `g ∈ H_lam` the set
below is the whole of `H_lam`. -/
theorem finite_conj_inter (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (hemb : D.IsHyperbolicallyEmbedded)
    {lam mu : Λ} {g : G} (hmid : ¬ (mu = lam ∧ g ∈ D.fam lam)) :
    {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam mu}.Finite := by
  obtain ⟨δ, hδ⟩ :=
    exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  obtain ⟨w, hw⟩ := OsinComponents.existsGeodesicWord D 1 g
  obtain ⟨y, f, v, hy, hgyf, hgeo, hfst⟩ :=
    OsinComponents.exists_strip_fam_prefix D lam w g hw
  have hmid' : ¬ (mu = lam ∧ f ∈ D.fam lam) := by
    rintro ⟨hmu, hf⟩
    refine hmid ⟨hmu, ?_⟩
    rw [hgyf]
    exact mul_mem hy hf
  have hsub : {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam mu}
      ⊆ (fun x : G => y⁻¹ * x * y) ⁻¹' D.relBall lam (100 * (δ + 2)) := by
    rintro x ⟨hx, hxc⟩
    show y⁻¹ * x * y ∈ D.relBall lam (100 * (δ + 2))
    refine OsinComponents.span_mem_relBall_of_geodesicWord D hsymm hδ hgeo hfst
      hmid' (mul_mem (mul_mem (inv_mem hy) hx) hy) ?_
    have he : f⁻¹ * (y⁻¹ * x * y) * f = g⁻¹ * x * g := by
      rw [hgyf]
      group
    rw [he]
    exact hxc
  refine Set.Finite.subset
    (Set.Finite.preimage ?_ (hemb.locallyFinite lam (100 * (δ + 2)))) hsub
  intro a _ b _ hab
  have hab' : y⁻¹ * a * y = y⁻¹ * b * y := hab
  exact mul_left_cancel (mul_right_cancel hab')

/-- **Almost malnormality with no symmetry hypothesis on the base**, for a
finite family.  `OsinTheorem54SepSymmetricFam.exists_symmetric_base'` enlarges
the base to a symmetric one without changing the family, and the statement
mentions only the family. -/
theorem finite_conj_inter' [Finite Λ] (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) {lam mu : Λ} {g : G}
    (hmid : ¬ (mu = lam ∧ g ∈ D.fam lam)) :
    {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam mu}.Finite := by
  obtain ⟨D', -, hfam, hsymm, hemb', -⟩ :=
    OsinComponents.exists_symmetric_base' D hemb
  have hstep := finite_conj_inter D' hsymm hemb' (lam := lam) (mu := mu)
    (g := g) (by rw [hfam]; exact hmid)
  rwa [hfam] at hstep

/-- **Dahmani--Guirardel--Osin, Proposition 4.33(a)**: for distinct indices and
**any** conjugator, the intersection is finite.  No hypothesis on `g`: the
prefix strip inside `finite_conj_inter` supplies what the quadrilateral needs. -/
theorem finite_conj_inter_of_ne [Finite Λ] (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) {lam mu : Λ} (hne : lam ≠ mu) (g : G) :
    {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam mu}.Finite :=
  finite_conj_inter' D hemb (fun hc => hne hc.1.symm)

/-- **Dahmani--Guirardel--Osin, Proposition 4.33(b)**: at one index, for a
conjugator outside the subgroup.  The same quadrilateral; what rules out the
`mu`-letter of its third side is `g ∉ H_lam` rather than `lam ≠ mu`. -/
theorem finite_conj_inter_of_notMem [Finite Λ] (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) {lam : Λ} {g : G}
    (hg : g ∉ D.fam lam) :
    {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam lam}.Finite :=
  finite_conj_inter' D hemb (fun hc => hg hc.2)

/-- **A conjugated power lands in another member of the family only finitely
often.**

`HullSC.finite_pow_mem_fam` is this at `A = 1`, where one letter does the work.
With `A` a genuine word --- a product of block letters, say --- the only route is
Proposition 4.33, and the hypothesis is the same one: not both `lam = mu` and
`A ∈ H_mu`. -/
theorem finite_conj_pow_mem_fam [Finite Λ] (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) {lam mu : Λ} {a A : G}
    (hmid : ¬ (lam = mu ∧ A ∈ D.fam mu))
    (hinj : Function.Injective (fun n : ℕ => a ^ n))
    (hmem : ∀ n : ℕ, a ^ n ∈ D.fam lam) :
    {d : ℕ | A * a ^ d * A⁻¹ ∈ D.fam mu}.Finite := by
  have hfin := finite_conj_inter' D hemb (lam := mu) (mu := lam) (g := A) hmid
  have hsub : {d : ℕ | A * a ^ d * A⁻¹ ∈ D.fam mu}
      ⊆ (fun d : ℕ => A * a ^ d * A⁻¹) ⁻¹'
        {x : G | x ∈ D.fam mu ∧ A⁻¹ * x * A ∈ D.fam lam} := by
    intro d hd
    show A * a ^ d * A⁻¹ ∈ D.fam mu ∧ A⁻¹ * (A * a ^ d * A⁻¹) * A ∈ D.fam lam
    refine ⟨hd, ?_⟩
    have he : A⁻¹ * (A * a ^ d * A⁻¹) * A = a ^ d := by group
    rw [he]
    exact hmem d
  refine Set.Finite.subset (Set.Finite.preimage ?_ hfin) hsub
  intro c _ d _ hcd
  have hcd' : A * a ^ c * A⁻¹ = A * a ^ d * A⁻¹ := hcd
  have hpow : a ^ c = a ^ d := mul_left_cancel (mul_right_cancel hcd')
  exact hinj hpow

end Malnormal

/-! ## The named statement -/

/-- **`DGOProposition433` is proved.**

`DGOCorollary612Malnormal` routed the chain around it, at an `a` lying in the
base; the general `a` is Proposition 4.33(b), and it costs the polygon theory of
§4.2 --- the quadrilateral of `GGT/DGOProposition433Ball.lean` over the
isolated-component bound at `n = 4`. -/
theorem dgoProposition433 : DGOProposition433.{u} := by
  intro G _ D hemb a ha
  exact finite_conj_inter_of_notMem D hemb ha

end GGT
end GroupApproximation
