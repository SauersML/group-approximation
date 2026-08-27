import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic
import GroupApproximation.Manuscript.NonMF.FournierFacioDoubleHNN
import GroupApproximation.Sofic.ChiodoBelegradekTheorem
import GroupApproximation.Kazhdan.Kazhdan
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The Fournier-Facio input paragraph of `thm:torsion-free`

`non_mf_groups_exist.tex`, Section "A torsion-free group with full MF radical",
the paragraph beginning

> Following Fournier-Facio [FFF, §2], let `U` be a universal finitely presented
> torsion-free group, one containing a copy of every finitely presented
> torsion-free group [Chiodo]; let `S` be a finitely presented infinite simple
> torsion-free group [HydeLodha]; and let `H₀` be a torsion-free hyperbolic
> group with property (T), obtained from the density model at a parameter
> between `1/3` and `1/2` [Kotowski, Ollivier].

and running to

> We run the construction with the prescribed finite subset containing an
> element `s ≠ 1` of `S`.  Then `π(S) ≠ 1`, so `π|_S` is injective because `S`
> is simple.

Four objects are cited and not proved (`U`, `S`, `H₀`, `P`), as are the two
theorems that produce `E`'s acylindrical hyperbolicity and Hull's common
quotient; each is a `-- LITERATURE INPUT (sorry)` below, stated exactly as the
manuscript uses it.  Everything the paragraph *asserts on the strength of those
citations* is proved here:

* `kazhdan_of_fournierFacioQuotient` — "Consequently, `P` has property (T)."
* `containsEveryFPTorsionFree_of_fournierFacioQuotient` — `P` inherits `U`'s
  universality along the embedding `U ↪ P`.
* `exists_injective_prodProdSimple` — "By universality, `P` contains a subgroup
  `P₁ × P₂ × S` with `Pᵢ ≅ P`."  The two closure facts it consumes are
  `ProductFinitePresentation.instProd` (direct products of finitely presented
  groups are finitely presented — proved in this repository, absent from
  Mathlib) and `IsPowerTorsionFree.prod`.
* `E`, the double HNN extension of `P` with stable letters `u₁, u₂` and
  `uᵢ P uᵢ⁻¹ = Pᵢ`, with the two printed conjugation relations, finite
  presentation and torsion-freeness — all in the companion module
  `Manuscript.NonMF.FournierFacioDoubleHNN`.
* `injective_of_map_ne_one` — "`π(S) ≠ 1`, so `π|_S` is injective because `S`
  is simple."
* `commutator_eq_top_of_infinite_simple` — the perfectness of `S` used by the
  last sentence of `lem:simple-in-defect`.

The paragraph's output, in the form the printed proof of `thm:torsion-free`
consumes it, is `Configuration`; `exists_configuration` assembles one.

## Acylindrical hyperbolicity

The printed adjective is the parallel hull-saturation lane's class
`Manuscript.NonMF.TorsionFree.IsAcylindricallyHyperbolic`, imported directly:
no placeholder is used here.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

open scoped commutatorElement

/-! ## Two elementary facts the paragraph uses -/

/-- **An infinite simple group is perfect.**  `lem:simple-in-defect` ends "so
`ρ(π(S)) ≅ S` is perfect"; this is that sentence.  The commutator subgroup is
normal, so simplicity leaves `⊥` or `⊤`; `⊥` makes the group commutative, and a
commutative simple group has prime order, hence is finite. -/
theorem commutator_eq_top_of_infinite_simple (S : Type) [Group S]
    [IsSimpleGroup S] [Infinite S] : commutator S = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) inferInstance with
    hbot | htop
  · exfalso
    have hcomm : ∀ a b : S, a * b = b * a := by
      intro a b
      have hmem : ⁅a, b⁆ ∈ commutator S := by
        rw [commutator_eq_closure]
        exact Subgroup.subset_closure ⟨a, b, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    letI : CommGroup S := { (inferInstance : Group S) with mul_comm := hcomm }
    have hprime : (Nat.card S).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_eq_zero_of_infinite] at hprime
    exact Nat.not_prime_zero hprime
  · exact htop

/-- **"`π(S) ≠ 1`, so `π|_S` is injective because `S` is simple."**  The kernel
is normal, hence `⊥` or `⊤`; it is not `⊤` because one element survives. -/
theorem injective_of_map_ne_one {S H : Type} [Group S] [Group H] [IsSimpleGroup S]
    (f : S →* H) {x : S} (hx : f x ≠ 1) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with hbot | htop
  · exact hbot
  · exfalso
    apply hx
    have hmem : x ∈ f.ker := by rw [htop]; exact Subgroup.mem_top x
    exact MonoidHom.mem_ker.mp hmem

/-! ## The literature inputs -/

/-- **Chiodo's universal group `U`**, in the form this repository already
states it: `ChiodoBelegradek.Statement` is "there is a finitely presented
torsion-free group containing a copy of every finitely presented torsion-free
group". -/
-- LITERATURE INPUT (sorry): Chiodo, arXiv:1107.1489v4, Theorem 3.10
-- (= Belegradek, Theorem A.1).  Restated in this repository as
-- `GroupApproximation.ChiodoBelegradek.Statement`, where two of its three
-- clauses are proved and the missing one is named.
theorem chiodoUniversalGroup : ChiodoBelegradek.Statement := by
  sorry

/-- **Hyde--Lodha's group `S`**: a finitely presented infinite simple
torsion-free group. -/
def HydeLodhaStatement : Prop :=
  ∃ (S : Type) (_ : Group S),
    Group.IsFinitelyPresented S ∧ Infinite S ∧ IsSimpleGroup S ∧
      IsPowerTorsionFree S

-- LITERATURE INPUT (sorry): Hyde--Lodha, a finitely presented infinite simple
-- torsion-free group.
theorem hydeLodhaSimpleGroup : HydeLodhaStatement := by
  sorry

/-- **The density-model group `H₀`.**  The manuscript takes `H₀` torsion-free
hyperbolic with property (T); only the three properties used downstream are
recorded — finite presentation, torsion-freeness, property (T).  Hyperbolicity
enters inside the cited small-cancellation step and nowhere in this
development. -/
def KotowskiOllivierStatement : Prop :=
  ∃ (H₀ : Type) (_ : Group H₀),
    Group.IsFinitelyPresented H₀ ∧ IsPowerTorsionFree H₀ ∧
      HasKazhdanPropertyT.{0, 0} H₀

-- LITERATURE INPUT (sorry): Kotowski--Kotowski and Ollivier--Wise, the density
-- model at a parameter between 1/3 and 1/2: a torsion-free hyperbolic group
-- with property (T).
theorem kotowskiOllivierBase : KotowskiOllivierStatement := by
  sorry

/-- **The small-cancellation quotient `P`.**  "Small cancellation over the
relatively hyperbolic pair `(U * H₀, U)` embeds `U` in a finitely presented
torsion-free quotient `P` of `H₀`; torsion-freeness is preserved by Osin's
embedding theorem."  The two clauses used downstream are the surjection
`H₀ ↠ P` and the embedding `U ↪ P`. -/
def FournierFacioQuotientStatement : Prop :=
  ∀ (H₀ U : Type) (_ : Group H₀) (_ : Group U),
    Group.IsFinitelyPresented H₀ → IsPowerTorsionFree H₀ →
      Group.IsFinitelyPresented U → IsPowerTorsionFree U →
        ∃ (P : Type) (_ : Group P),
          Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
            (∃ p : H₀ →* P, Function.Surjective p) ∧
            (∃ e : U →* P, Function.Injective e)

-- LITERATURE INPUT (sorry): Fournier-Facio et al., Proposition 2.3, together
-- with Osin, "Small cancellations over relatively hyperbolic groups and
-- embedding theorems", Theorem 2.4(5).
theorem fournierFacioQuotient : FournierFacioQuotientStatement := by
  sorry

/-- **Minasyan--Osin's tree criterion.**  "Its Bass--Serre action makes it
acylindrically hyperbolic."  Stated exactly at the manuscript's `E`: the double
HNN extension of `P` along the two `P`-factors of `P₁ × P₂ × S`. -/
def MinasyanOsinStatement : Prop :=
  ∀ (P S : Type) (_ : Group P) (_ : Group S) (f : (P × P × S) →* P)
    (hf : Function.Injective f), TorsionFree.IsAcylindricallyHyperbolic (Skeleton f hf)

-- LITERATURE INPUT (sorry): Minasyan--Osin, acylindrical hyperbolicity of
-- groups acting on trees, applied to the Bass--Serre tree of the double HNN
-- extension.
theorem minasyanOsinAcylindricallyHyperbolic : MinasyanOsinStatement := by
  sorry

/-- **Hull's common quotient theorem, Corollary 7.4**, in the form the
manuscript uses it: applied to `E` and `H₀` it gives a surjection `π : E ↠ G₀`
onto a finitely presented torsion-free group with property (T), injective on a
prescribed finite subset of `E`; since `E` is finitely generated, the proof of
that corollary produces `G₀` acylindrically hyperbolic. -/
def HullCommonQuotientStatement : Prop :=
  ∀ (E : Type) (_ : Group E) (H₀ : Type) (_ : Group H₀),
    Group.IsFinitelyPresented E → IsPowerTorsionFree E → TorsionFree.IsAcylindricallyHyperbolic E →
      Group.IsFinitelyPresented H₀ → HasKazhdanPropertyT.{0, 0} H₀ →
        ∀ F : Finset E,
          ∃ (G₀ : Type) (_ : Group G₀) (pi : E →* G₀),
            Function.Surjective pi ∧ Group.IsFinitelyPresented G₀ ∧
              IsPowerTorsionFree G₀ ∧ HasKazhdanPropertyT.{0, 0} G₀ ∧
              TorsionFree.IsAcylindricallyHyperbolic G₀ ∧ Set.InjOn pi (F : Set E)

-- LITERATURE INPUT (sorry): Hull, "Small cancellation in acylindrically
-- hyperbolic groups", Corollary 7.4.
theorem hullCommonQuotient : HullCommonQuotientStatement := by
  sorry

/-! ## What the paragraph proves about `P` -/

/-- **"Consequently, `P` has property (T)."**  `P` is a quotient of `H₀`. -/
theorem kazhdan_of_fournierFacioQuotient {H₀ P : Type} [Group H₀] [Group P]
    (hH₀ : HasKazhdanPropertyT.{0, 0} H₀) (p : H₀ →* P)
    (hp : Function.Surjective p) : HasKazhdanPropertyT.{0, 0} P :=
  HasKazhdanPropertyT.of_surjective p hp hH₀

/-- `P` inherits `U`'s universality along the embedding `U ↪ P`: the "by
universality" of the next printed sentence. -/
theorem containsEveryFPTorsionFree_of_fournierFacioQuotient {U P : Type}
    [Group U] [Group P] (hU : ChiodoBelegradek.ContainsEveryFPTorsionFree U)
    (e : U →* P) (he : Function.Injective e) :
    ChiodoBelegradek.ContainsEveryFPTorsionFree P :=
  hU.comp e he

/-- **"By universality, `P` contains a subgroup `P₁ × P₂ × S` with `Pᵢ ≅ P`."**

The proof is the printed one: `P × P × S` is finitely presented (Mathlib does
not close finite presentation under direct products; this repository does, in
`ProductFinitePresentation.instProd`) and torsion-free
(`IsPowerTorsionFree.prod`), so universality of `P` embeds it in `P`. -/
theorem exists_injective_prodProdSimple {P S : Type} [Group P] [Group S]
    [Group.IsFinitelyPresented P] [Group.IsFinitelyPresented S]
    (hP : IsPowerTorsionFree P) (hS : IsPowerTorsionFree S)
    (huniv : ChiodoBelegradek.ContainsEveryFPTorsionFree P) :
    ∃ f : (P × P × S) →* P, Function.Injective f :=
  huniv.embeds (P × P × S) (hP.prod (hP.prod hS))

/-! ## The output of the paragraph -/

/-- **The state of the construction at the end of the Fournier-Facio
paragraph.**

Every field is a printed sentence of that paragraph, transported through `π`.
`Ambient` is `G₀`; `core` is `π ∘ ι : P → G₀`, whose range is the printed
`Γ = π(P)`; `simple` is `π|_S : S → G₀`, whose range is the printed `π(S)`; and
`t` is the printed `t = π(u₁)`.

`core_mem_of_simple` is "`π(S) ≤ Γ`" (already true before `π`, because `S ≤ P`);
`t_compresses` is "`tΓt⁻¹ = π(P₁) ≤ Γ`"; and `simple_commute_conj` is the
printed "`S` commutes with `P₁ = u₁ P u₁⁻¹`", from which `thm:torsion-free`'s
"`J` centralizes `Γ`" is derived. -/
structure Configuration where
  /-- `G₀`, Hull's common quotient. -/
  Ambient : Type
  [groupAmbient : Group Ambient]
  [fpAmbient : Group.IsFinitelyPresented Ambient]
  /-- `G₀` is torsion-free. -/
  torsionFreeAmbient : IsPowerTorsionFree Ambient
  /-- `G₀` has property (T). -/
  kazhdanAmbient : HasKazhdanPropertyT.{0, 0} Ambient
  /-- `G₀` is acylindrically hyperbolic. -/
  acylAmbient : TorsionFree.IsAcylindricallyHyperbolic Ambient
  /-- The Hyde--Lodha simple group `S`. -/
  Simple : Type
  [groupSimple : Group Simple]
  /-- `S` is simple. -/
  simpleSimple : IsSimpleGroup Simple
  /-- `S` is infinite. -/
  infiniteSimple : Infinite Simple
  /-- The Fournier-Facio base `P`. -/
  Core : Type
  [groupCore : Group Core]
  /-- `P` has property (T). -/
  kazhdanCore : HasKazhdanPropertyT.{0, 0} Core
  /-- `π ∘ ι : P → G₀`; its range is `Γ = π(P)`. -/
  core : Core →* Ambient
  /-- `π|_S : S → G₀`; its range is `π(S)`. -/
  simple : Simple →* Ambient
  /-- `π|_S` is injective. -/
  simple_injective : Function.Injective simple
  /-- `π(S) ≤ Γ`. -/
  core_mem_of_simple : ∀ x : Simple, ∃ p : Core, simple x = core p
  /-- `t = π(u₁)`. -/
  t : Ambient
  /-- `t Γ t⁻¹ = π(P₁) ≤ Γ`. -/
  t_compresses : ∀ p : Core, ∃ q : Core, t * core p * t⁻¹ = core q
  /-- `[S, P₁] = 1`, transported: `π(S)` commutes with `t Γ t⁻¹`. -/
  simple_commute_conj : ∀ (x : Simple) (p : Core),
    Commute (simple x) (t * core p * t⁻¹)

namespace Configuration

instance instGroupAmbient (C : Configuration) : Group C.Ambient := C.groupAmbient

instance instFPAmbient (C : Configuration) :
    Group.IsFinitelyPresented C.Ambient := C.fpAmbient

instance instGroupSimple (C : Configuration) : Group C.Simple := C.groupSimple

instance instSimpleSimple (C : Configuration) : IsSimpleGroup C.Simple :=
  C.simpleSimple

instance instInfiniteSimple (C : Configuration) : Infinite C.Simple :=
  C.infiniteSimple

instance instGroupCore (C : Configuration) : Group C.Core := C.groupCore

instance instAcylAmbient (C : Configuration) :
    TorsionFree.IsAcylindricallyHyperbolic C.Ambient := C.acylAmbient

/-- `G₀` is countable: it is finitely presented. -/
theorem countableAmbient (C : Configuration) : Countable C.Ambient :=
  ChiodoBelegradek.countable_of_isFinitelyPresented C.Ambient

end Configuration

/-! ## Assembling the paragraph -/

/-- **The Fournier-Facio paragraph, assembled.**  Each literature input above
is used exactly once, and every other step is one of the proofs of this
module. -/
theorem exists_configuration : Nonempty Configuration := by
  classical
  obtain ⟨U, instU, hUfp, hUtf, hUuniv⟩ := chiodoUniversalGroup
  obtain ⟨S, instS, hSfp, hSinf, hSsimple, hStf⟩ := hydeLodhaSimpleGroup
  obtain ⟨H₀, instH₀, hH₀fp, hH₀tf, hH₀T⟩ := kotowskiOllivierBase
  obtain ⟨P, instP, hPfp, hPtf, ⟨quot, hquot⟩, ⟨emb, hemb⟩⟩ :=
    fournierFacioQuotient H₀ U instH₀ instU hH₀fp hH₀tf hUfp hUtf
  letI := instU
  letI := instS
  letI := instH₀
  letI := instP
  haveI := hSfp
  haveI := hPfp
  haveI := hSinf
  haveI := hSsimple
  -- "Consequently, `P` has property (T)."
  have hPT : HasKazhdanPropertyT.{0, 0} P :=
    kazhdan_of_fournierFacioQuotient hH₀T quot hquot
  -- "By universality, `P` contains a subgroup `P₁ × P₂ × S` with `Pᵢ ≅ P`."
  have hPuniv : ChiodoBelegradek.ContainsEveryFPTorsionFree P :=
    containsEveryFPTorsionFree_of_fournierFacioQuotient hUuniv emb hemb
  obtain ⟨f, hf⟩ :=
    exists_injective_prodProdSimple (P := P) (S := S) hPtf hStf hPuniv
  -- `E`, the double HNN extension, and its three printed properties.
  have hEfp : Group.IsFinitelyPresented (Skeleton f hf) :=
    skeleton_isFinitelyPresented f hf
  have hEtf : IsPowerTorsionFree (Skeleton f hf) := skeleton_torsionFree f hf hPtf
  have hEacyl : TorsionFree.IsAcylindricallyHyperbolic (Skeleton f hf) :=
    minasyanOsinAcylindricallyHyperbolic P S inferInstance inferInstance f hf
  -- "the prescribed finite subset containing an element `s ≠ 1` of `S`"
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  obtain ⟨G₀, instG₀, pi, -, hG₀fp, hG₀tf, hG₀T, hG₀acyl, hinj⟩ :=
    hullCommonQuotient (Skeleton f hf) inferInstance H₀ instH₀ hEfp hEtf hEacyl
      hH₀fp hH₀T {1, skeletonIota f hf (factorSimple f s)}
  letI := instG₀
  haveI := hG₀fp
  have hmem1 : (1 : Skeleton f hf) ∈
      ((({1, skeletonIota f hf (factorSimple f s)} : Finset (Skeleton f hf)) :
        Set (Skeleton f hf))) := by simp
  have hmems : skeletonIota f hf (factorSimple f s) ∈
      ((({1, skeletonIota f hf (factorSimple f s)} : Finset (Skeleton f hf)) :
        Set (Skeleton f hf))) := by simp
  -- "Then `π(S) ≠ 1`, so `π|_S` is injective because `S` is simple."
  have hne : pi (skeletonIota f hf (factorSimple f s)) ≠ 1 := by
    intro hz
    have h1 : pi (skeletonIota f hf (factorSimple f s)) = pi 1 := by
      rw [hz, map_one]
    have h2 := hinj hmems hmem1 h1
    apply hs
    apply factorSimple_injective f hf
    apply skeletonIota_injective f hf
    rw [h2, map_one, map_one]
  have hsimpleInj : Function.Injective
      ((pi.comp (skeletonIota f hf)).comp (factorSimple f)) :=
    injective_of_map_ne_one _ (x := s) hne
  -- The compression relation, transported through `π`.
  have hconj : ∀ p : P, pi (skeletonU₁ f hf) *
      (pi.comp (skeletonIota f hf)) p * (pi (skeletonU₁ f hf))⁻¹
        = (pi.comp (skeletonIota f hf)) (factorOne f p) := by
    intro p
    have h := congrArg pi (skeleton_conj_u₁ f hf p)
    simpa using h
  refine ⟨{
    Ambient := G₀
    torsionFreeAmbient := hG₀tf
    kazhdanAmbient := hG₀T
    acylAmbient := hG₀acyl
    Simple := S
    simpleSimple := hSsimple
    infiniteSimple := hSinf
    Core := P
    kazhdanCore := hPT
    core := pi.comp (skeletonIota f hf)
    simple := (pi.comp (skeletonIota f hf)).comp (factorSimple f)
    simple_injective := hsimpleInj
    core_mem_of_simple := fun x => ⟨factorSimple f x, rfl⟩
    t := pi (skeletonU₁ f hf)
    t_compresses := fun p => ⟨factorOne f p, hconj p⟩
    simple_commute_conj := ?_ }⟩
  intro x p
  rw [hconj p]
  exact (factorSimple_commute_factorOne f x p).map (pi.comp (skeletonIota f hf))

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
