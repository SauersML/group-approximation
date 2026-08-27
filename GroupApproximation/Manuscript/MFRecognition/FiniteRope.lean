import GroupApproximation.Manuscript.MFRecognition.RopeObjects
import GroupApproximation.Higman.MikhailovaRopeCodeSemantics

/-!
# `mf_recognition_complexity.tex`: the second HNN extension and `lem:finite-rope`

This file is the Lean form of the two displays after `lem:central-rope`,

```
  R_e  = ⟨Γ_e × Q_e, u | u(s,1)u⁻¹ = (s, α_e(s))  (s ∈ S_e)⟩          (eq:twisted-rope)

  R̂_e = ⟨Γ_e × F,  u | u(i(a),1)u⁻¹ = (i(a), a),
                        u(v i(a) v⁻¹,1)u⁻¹ = (v i(a) v⁻¹,1)  (a ∈ {x,y,t})⟩
                                                                       (eq:finite-rope)
```

and of

> **Lemma (the finite presentation).**  The groups `R̂_e` and `R_e` are
> isomorphic by the map that is the identity on `Γ_e` and on `u` and sends
> `F` onto `Q_e` by `q_e`.  A code of the finite presentation
> `eq:finite-rope` is computable from `e`.

`R_e` is `TwistedRope`, `R̂_e` is `FiniteRope` --- the free product
`(Γ_e × F) ∗ ⟨u⟩` cut by exactly the two displayed relator families, over the
basis `{x,y,t}` of `F`; the two commutation families of `Γ_e × F` are the
direct product itself.  The isomorphism is `finiteRopeEquiv`, and its three
printed clauses are `finiteRopeEquiv_gamma`, `finiteRopeEquiv_u` and
`finiteRopeEquiv_free`.

## Where the printed proof steps live

Every sentence of the printed proof is a separate theorem below:
`finiteRope_relA`, `finiteRope_relB` (both relations hold for all `f ∈ F`,
not only on the basis, because both sides are homomorphisms in `f`),
`freeIn_eq_one_of_mem` (`(1,n) = 1` for `n ∈ N_e`, so `F` factors through
`Q_e`), `finiteRope_rel_all` (the relations then hold for all `s ∈ S_e`), and
`finiteRope_left_inverse` together with `finiteRopeEquiv` (the two
homomorphisms are mutually inverse).

## The code

The raw finite-presentation transformation of `eq:finite-rope` is the
repository's `Higman.MikhailovaRopeCode.compile`, and
`Higman.MikhailovaRopeCodeSemantics.compileEquivToRope` proves that the
carrier of the compiled code is the group built here.  What is proved below
is the computability half: the transformation is primitive recursive, so the
code of `eq:finite-rope` is computable from `e` as soon as the raw data are
(WIRING: higman-compiler supplies `e ↦ data`).
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Rope
namespace RopeInput

variable (inp : RopeInput)

/-! ## 1.  `eq:twisted-rope`: the second HNN extension -/

/-- **`eq:twisted-rope`.**  `R_e = ⟨Γ_e × Q_e, u | u(s,1)u⁻¹ = (s, α_e(s))
(s ∈ S_e)⟩`, the HNN extension of `Γ_e × Q_e` along the two displayed edge
maps of `S_e`. -/
abbrev TwistedRope : Type := Higman.Rope.RopeGroup (witness inp)

/-- The first printed edge map of `eq:twisted-rope`, `s ↦ (s, 1)`. -/
def edgeOne : ↥(RopeS inp) →* CentralRope inp × Qe inp :=
  (MonoidHom.inl (CentralRope inp) (Qe inp)).comp (RopeS inp).subtype

/-- The second printed edge map of `eq:twisted-rope`, `s ↦ (s, α_e(s))`. -/
noncomputable def edgeAlpha : ↥(RopeS inp) →* CentralRope inp × Qe inp :=
  ((RopeS inp).subtype).prod (alpha inp)

@[simp] theorem edgeOne_apply (s : ↥(RopeS inp)) :
    edgeOne inp s = ((s : CentralRope inp), 1) := rfl

@[simp] theorem edgeAlpha_apply (s : ↥(RopeS inp)) :
    edgeAlpha inp s = ((s : CentralRope inp), alpha inp s) := rfl

/-- "whose edge maps `s ↦ (s,1)` and `s ↦ (s, α_e(s))` are injective
homomorphisms of `S_e` into `Γ_e × Q_e`": the first coordinate is the
inclusion. -/
theorem edgeOne_injective : Function.Injective (edgeOne inp) := by
  intro a b hab
  exact Subtype.ext (congrArg Prod.fst hab)

/-- The same for the twisted edge map. -/
theorem edgeAlpha_injective : Function.Injective (edgeAlpha inp) := by
  intro a b hab
  exact Subtype.ext (congrArg Prod.fst hab)

/-- "so `Γ_e × Q_e` embeds in `R_e` by Britton's lemma": the base of an HNN
extension embeds in it. -/
theorem base_injective_twistedRope :
    Function.Injective
      (HNNExtension.of :
        Higman.Rope.Amb (witness inp) →* TwistedRope inp) :=
  HNNExtension.of_injective (Higman.Rope.psi (witness inp))

/-- In particular `Q_e` itself embeds in `R_e`, which is the use the
manuscript makes of the embedding. -/
theorem quotient_injective_twistedRope :
    Function.Injective (Higman.Rope.quotientEmb (witness inp)) :=
  Higman.Rope.quotientEmb_injective (witness inp)

/-- **The defining relation of `eq:twisted-rope`, inside `R_e`.**
`u(s,1)u⁻¹ = (s, α_e(s))` for every `s ∈ S_e`. -/
theorem twistedRope_conj (s : ↥(RopeS inp)) :
    (HNNExtension.of : Higman.Rope.Amb (witness inp) →* TwistedRope inp)
        ((s : CentralRope inp), alpha inp s)
      = (HNNExtension.t : TwistedRope inp) *
          (HNNExtension.of : Higman.Rope.Amb (witness inp) →* TwistedRope inp)
            ((s : CentralRope inp), 1) *
          (HNNExtension.t : TwistedRope inp)⁻¹ := by
  have h := HNNExtension.equiv_eq_conj (φ := Higman.Rope.psi (witness inp))
    ⟨(((s : CentralRope inp), (1 : Qe inp)) : Higman.Rope.Amb (witness inp)),
      Higman.Rope.pair_mem_ae (witness inp) (s : CentralRope inp) s.2⟩
  rw [Higman.Rope.coe_psi (witness inp) (s : CentralRope inp) s.2] at h
  exact h

/-! ## 2.  `eq:finite-rope`: the finite replacement -/

/-- **`eq:finite-rope`.**  `R̂_e = ⟨Γ_e × F, u | u(i(a),1)u⁻¹ = (i(a), a),
u(v i(a) v⁻¹, 1)u⁻¹ = (v i(a) v⁻¹, 1) (a ∈ {x,y,t})⟩`, where `Γ_e × F` is
equipped with the finite presentation of `lem:central-rope`(2), the basis
`x, y, t` of `F`, and the commutation relators between the two factors. -/
abbrev FiniteRope : Type := Higman.Rope.Pres (witness inp) basisXYT

/-- The printed stable letter `u` of `eq:finite-rope`, inside `R̂_e`. -/
def stableU : FiniteRope inp :=
  Higman.Rope.presMk (witness inp) basisXYT (Higman.Rope.preE (witness inp))

/-- The factor `Γ_e` of `eq:finite-rope`, inside `R̂_e`. -/
def gammaIn (g : CentralRope inp) : FiniteRope inp :=
  Higman.Rope.presMk (witness inp) basisXYT
    (Higman.Rope.preGamma (witness inp) g)

/-- The factor `F` of `eq:finite-rope`, inside `R̂_e`. -/
def freeIn (f : Fxyt) : FiniteRope inp :=
  Higman.Rope.presMk (witness inp) basisXYT (Higman.Rope.preF (witness inp) f)

/-- "`Γ_e × F` is equipped with [...] the commutation relators between the two
factors": the two factors commute in `R̂_e`. -/
theorem gammaIn_commute_freeIn (g : CentralRope inp) (f : Fxyt) :
    Commute (gammaIn inp g) (freeIn inp f) :=
  (Higman.Rope.preGamma_commute_preF (witness inp) g f).map
    (Higman.Rope.presMk (witness inp) basisXYT)

/-- **`eq:finite-rope`, first relator family, for all of `F`.**  "Both maps
`f ↦ u(i(f),1)u⁻¹` and `f ↦ (i(f), f)` are homomorphisms `F → R̂_e`, and they
agree on the basis, so `u(i(f),1)u⁻¹ = (i(f), f)` for all `f ∈ F`." -/
theorem finiteRope_relA (f : Fxyt) :
    stableU inp * gammaIn inp (iGammaHom inp f) * (stableU inp)⁻¹
      = gammaIn inp (iGammaHom inp f) * freeIn inp f :=
  Higman.Rope.presMk_relA (witness inp) closure_basisXYT f

/-- **`eq:finite-rope`, second relator family, for all of `F`.**  "likewise
`u(v i(f) v⁻¹, 1)u⁻¹ = (v i(f) v⁻¹, 1)` for all `f`." -/
theorem finiteRope_relB (f : Fxyt) :
    stableU inp * gammaIn inp (vConjHom inp f) * (stableU inp)⁻¹
      = gammaIn inp (vConjHom inp f) := by
  rw [vConjHom_eq_gammaConj]
  exact Higman.Rope.presMk_relB (witness inp) closure_basisXYT f

/-- **The step that makes `eq:finite-rope` finite.**  "If `n ∈ N_e`, then
`i(n) ∈ L_e` by `lem:central-rope`(1), so `v i(n) v⁻¹ = i(n)` in `Γ_e`, and
comparing the two relations gives `(i(n), n) = (i(n), 1)`, that is,
`(1, n) = 1` in `R̂_e`.  So the factor `F` of `R̂_e` factors through
`Q_e = F/N_e`." -/
theorem freeIn_eq_one_of_mem {n : Fxyt} (hn : n ∈ inp.N) : freeIn inp n = 1 :=
  Higman.Rope.presMk_preF_eq_one (witness inp) closure_basisXYT hn

/-- **The factor `F` of `R̂_e`, read as `Q_e`.**  The homomorphism
`Q_e → R̂_e` that `freeIn_eq_one_of_mem` makes possible. -/
noncomputable def quotIn : Qe inp →* FiniteRope inp :=
  Higman.Rope.quotientMap (witness inp) basisXYT closure_basisXYT

@[simp] theorem quotIn_mk (f : Fxyt) : quotIn inp (qe inp f) = freeIn inp f := rfl

/-- **The relations hold for all of `S_e`.**  "the relations of
`eq:finite-rope` become `u(s,1)u⁻¹ = (s, α_e(s))` for `s` in the generating
set `{i(a), v i(a) v⁻¹ : a ∈ {x,y,t}}` of `S_e`; both sides define
homomorphisms on `S_e`, so the relations hold for all `s ∈ S_e`." -/
theorem finiteRope_rel_all (s : ↥(RopeS inp)) :
    stableU inp *
        Higman.Rope.baseMap (witness inp) basisXYT closure_basisXYT
          ((s : CentralRope inp), 1) * (stableU inp)⁻¹
      = Higman.Rope.baseMap (witness inp) basisXYT closure_basisXYT
          ((s : CentralRope inp), alpha inp s) :=
  Higman.Rope.conj_baseMap (witness inp) basisXYT closure_basisXYT s

/-! ## 3.  `lem:finite-rope` -/

/-- "This defines a homomorphism `R_e → R̂_e`." -/
noncomputable def fromTwisted : TwistedRope inp →* FiniteRope inp :=
  Higman.Rope.fromRope (witness inp) basisXYT closure_basisXYT

/-- "conversely, the relations of `eq:finite-rope` hold in `R_e` after
`F → Q_e`, because `α_e(i(a)) = q_e(a)` and `α_e(v i(a) v⁻¹) = 1`." -/
noncomputable def toTwisted : FiniteRope inp →* TwistedRope inp :=
  Higman.Rope.toRope (witness inp) basisXYT

/-- "The two homomorphisms are mutually inverse on generators", first
direction. -/
theorem finiteRope_left_inverse :
    (fromTwisted inp).comp (toTwisted inp) = MonoidHom.id (FiniteRope inp) :=
  Higman.Rope.fromRope_toRope (witness inp) basisXYT closure_basisXYT

theorem toTwisted_injective : Function.Injective (toTwisted inp) :=
  Higman.Rope.toRope_injective (witness inp) basisXYT closure_basisXYT

theorem toTwisted_surjective : Function.Surjective (toTwisted inp) :=
  Higman.Rope.toRope_surjective (witness inp) basisXYT

/-- **`lem:finite-rope`, first sentence.**  "The groups `R̂_e` and `R_e` are
isomorphic by the map that is the identity on `Γ_e` and on `u` and sends `F`
onto `Q_e` by `q_e`." -/
noncomputable def finiteRopeEquiv : FiniteRope inp ≃* TwistedRope inp :=
  Higman.Rope.ropeEquiv (witness inp) basisXYT closure_basisXYT

@[simp] theorem finiteRopeEquiv_apply (z : FiniteRope inp) :
    finiteRopeEquiv inp z = toTwisted inp z := rfl

/-- "the identity on `Γ_e`". -/
theorem finiteRopeEquiv_gamma (g : CentralRope inp) :
    finiteRopeEquiv inp (gammaIn inp g)
      = (HNNExtension.of : Higman.Rope.Amb (witness inp) →* TwistedRope inp)
          (g, 1) :=
  Higman.Rope.toRope_gamma (witness inp) basisXYT g

/-- "and on `u`". -/
theorem finiteRopeEquiv_u :
    finiteRopeEquiv inp (stableU inp) = (HNNExtension.t : TwistedRope inp) :=
  Higman.Rope.toRope_e (witness inp) basisXYT

/-- "and sends `F` onto `Q_e` by `q_e`". -/
theorem finiteRopeEquiv_free (f : Fxyt) :
    finiteRopeEquiv inp (freeIn inp f)
      = (HNNExtension.of : Higman.Rope.Amb (witness inp) →* TwistedRope inp)
          (1, qe inp f) :=
  Higman.Rope.toRope_f (witness inp) basisXYT f

/-- `R̂_e` is finitely presented: it is a manifest finite presentation over the
finitely presented group `Γ_e × F` with two finite relator families. -/
theorem finiteRope_isFinitelyPresented :
    Group.IsFinitelyPresented (FiniteRope inp) :=
  Higman.Rope.isFinitelyPresented_pres (witness inp) basisXYT_finite

/-- Transporting along `lem:finite-rope`, `R_e` is finitely presented. -/
theorem twistedRope_isFinitelyPresented :
    Group.IsFinitelyPresented (TwistedRope inp) :=
  Higman.Rope.isFinitelyPresented_ropeGroup (witness inp) basisXYT
    basisXYT_finite closure_basisXYT

/-! ## 4.  `lem:finite-rope`, second sentence: the code -/

/-- **`lem:finite-rope`, second sentence.**  "A code of the finite
presentation `eq:finite-rope` is computable from `e`.  [...] Computability of
the code follows from `lem:mikhailova` and `lem:central-rope`."

`Higman.MikhailovaRopeCode.compile` is the raw transformation that spells
`eq:finite-rope`: adjoin the stable letter `v` centralizing the cutting
words, take the direct product with the source, and adjoin the outer letter
`u` with the two displayed marked relator families.  It is primitive
recursive, so a code of `eq:finite-rope` is computable from `e` as soon as
the four raw inputs are --- and those are exactly what `lem:mikhailova` and
`lem:central-rope` compute from `e` (WIRING: higman-compiler supplies
`data`).

That the compiled code really presents `R̂_e` and `R_e` is the repository's
`Higman.MikhailovaRopeCodeSemantics.compileEquivToRopePresOfRelators` and
`compileEquivToRope`. -/
theorem computable_finiteRopeCode
    (data : ℕ → Higman.MikhailovaRopeCode.Input) (hdata : Computable data) :
    Computable fun e : ℕ => Higman.MikhailovaRopeCode.compile (data e) :=
  Higman.MikhailovaRopeCode.computable_compile.comp hdata

/-- The same, from the reduced rank-three input data the manuscript actually
holds: a code for `K_e`, the cutting words of `L_e`, and the three marked
words `i(x), i(y), i(t)`. -/
theorem computable_finiteRopeCode_rankThree
    (data : ℕ → Higman.MikhailovaRopeCode.RankThreeInputData)
    (hdata : Computable data) :
    Computable fun e : ℕ =>
      Higman.MikhailovaRopeCode.compileRankThree (data e) :=
  Higman.MikhailovaRopeCode.computable_compileRankThree.comp hdata

end RopeInput
end Rope
end MFRecognition
end Manuscript
end GroupApproximation
