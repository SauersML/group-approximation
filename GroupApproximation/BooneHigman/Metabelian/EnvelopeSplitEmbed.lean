import GroupApproximation.BooneHigman.Metabelian.EnvelopeReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Zaremsky's envelope: the regrouped copy of a self-similar group

`RoverNekrashevychEnvelopeStatement` (`EnvelopeReduction.lean`) asks for *some* alphabet `Y` and
*some* `K ≤ Aut(T_Y)` with `H ↪ K`.  This module fixes the construction; `EnvelopeSplit.lean`
splits the statement into four independent facts about one concrete group.

* `envelopeY X m = Fin m × X`, and `envelopeEmbed m : Aut(T_X) →* Aut(T_Y)`: `g` acts on the
  `X`-coordinates of a word over `Y` and leaves the `Fin m`-coordinates alone
  (`embedFun g w = zip (w.map fst) (g • w.map snd)`).  It is injective for `m ≠ 0`.
* `state_envelopeEmbed`: `(envelopeEmbed g)|_[(i, x)] = envelopeEmbed (g|_[x])`, so
  `envelopeK m H = H.map (envelopeEmbed m)` is self-similar when `H` is
  (`isSelfSimilar_envelopeK`), and `envelopeHom m H : H ≃ K` (`envelopeHom_injective`,
  `envelopeHom_surjective`, `isFinitelyPresented_envelopeK`).

Route: words over `Y` are zipped pairs of a `Fin m`-word and an `X`-word
(`map_fst_embedFun`, `map_snd_embedFun`); the tree-map property follows from
`TreeAut.smul_append` and `List.zip_append`; injectivity evaluates at `zip (replicate n 0) w`;
the state formula is `TreeAut.smul_cons` on both sides.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

variable {X : Type*} {m : ℕ}

/-- The regrouped alphabet `Fin m × X`. -/
abbrev envelopeY (X : Type*) (m : ℕ) : Type _ := Fin m × X

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeY

/-- `g` acting on the `X`-coordinates of a word over `Fin m × X`. -/
def embedFun (g : TreeAut X) (w : List (envelopeY X m)) : List (envelopeY X m) :=
  List.zip (w.map Prod.fst) (g • w.map Prod.snd)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.embedFun

theorem length_embedFun (g : TreeAut X) (w : List (envelopeY X m)) :
    (embedFun g w).length = w.length := by
  simp only [embedFun, List.length_zip, TreeAut.length_smul, List.length_map, min_self]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.length_embedFun

theorem map_fst_embedFun (g : TreeAut X) (w : List (envelopeY X m)) :
    (embedFun g w).map Prod.fst = w.map Prod.fst :=
  List.map_fst_zip (le_of_eq (by rw [TreeAut.length_smul, List.length_map, List.length_map]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.map_fst_embedFun

theorem map_snd_embedFun (g : TreeAut X) (w : List (envelopeY X m)) :
    (embedFun g w).map Prod.snd = g • w.map Prod.snd :=
  List.map_snd_zip (le_of_eq (by rw [TreeAut.length_smul, List.length_map, List.length_map]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.map_snd_embedFun

theorem embedFun_embedFun (g h : TreeAut X) (w : List (envelopeY X m)) :
    embedFun g (embedFun h w) = embedFun (g * h) w := by
  show List.zip _ _ = List.zip _ _
  rw [map_fst_embedFun, map_snd_embedFun, mul_smul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.embedFun_embedFun

theorem embedFun_one (w : List (envelopeY X m)) : embedFun (1 : TreeAut X) w = w := by
  rw [embedFun, one_smul]
  exact (List.zip_of_prod (xs := w) rfl rfl).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.embedFun_one

theorem isTreeMap_embedFun (g : TreeAut X) : IsTreeMap (embedFun (m := m) g) := by
  refine ⟨length_embedFun g, fun w v => ?_⟩
  have hl : (w.map Prod.fst).length = (g • w.map Prod.snd).length := by
    rw [TreeAut.length_smul, List.length_map, List.length_map]
  show List.zip _ _ <+: List.zip _ _
  rw [List.map_append, List.map_append, TreeAut.smul_append, List.zip_append hl]
  exact List.prefix_append _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isTreeMap_embedFun

/-- `embedFun g` as a permutation of words. -/
def embedPerm (g : TreeAut X) : Equiv.Perm (List (envelopeY X m)) where
  toFun := embedFun g
  invFun := embedFun g⁻¹
  left_inv w := by rw [embedFun_embedFun, inv_mul_cancel, embedFun_one]
  right_inv w := by rw [embedFun_embedFun, mul_inv_cancel, embedFun_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.embedPerm

variable (m) in
/-- `Aut(T_X) ↪ Aut(T_{Fin m × X})`, acting on the `X`-coordinates. -/
def envelopeEmbed : TreeAut X →* TreeAut (envelopeY X m) where
  toFun g := ⟨embedPerm g, isTreeMap_embedFun g⟩
  map_one' := TreeAut.ext fun w => by rw [one_smul]; exact embedFun_one w
  map_mul' g h := TreeAut.ext fun w => by rw [mul_smul]; exact (embedFun_embedFun g h w).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeEmbed

theorem envelopeEmbed_smul (g : TreeAut X) (w : List (envelopeY X m)) :
    envelopeEmbed m g • w = embedFun g w := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeEmbed_smul

theorem envelopeEmbed_injective [NeZero m] : Function.Injective (envelopeEmbed (X := X) m) := by
  intro g h hgh
  refine TreeAut.ext fun w => ?_
  have hz : (List.zip (List.replicate w.length (0 : Fin m)) w).map Prod.snd = w :=
    List.map_snd_zip List.length_replicate.ge
  have e := congrArg
    (fun k => (k • List.zip (List.replicate w.length (0 : Fin m)) w).map Prod.snd) hgh
  simp only [envelopeEmbed_smul, map_snd_embedFun, hz] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeEmbed_injective

theorem state_envelopeEmbed (g : TreeAut X) (i : Fin m) (x : X) :
    TreeAut.state (envelopeEmbed m g) [(i, x)] = envelopeEmbed m (TreeAut.state g [x]) := by
  refine TreeAut.ext fun v => TreeAut.state_smul_eq_of_smul_append _ ?_
  show embedFun g ([(i, x)] ++ v) = embedFun g [(i, x)] ++ embedFun (TreeAut.state g [x]) v
  simp only [embedFun, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    TreeAut.smul_cons, TreeAut.smul_nil, List.zip_cons_cons, List.zip_nil_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.state_envelopeEmbed

variable (m) in
/-- The regrouped copy `K = H.map (envelopeEmbed m)` of `H`. -/
def envelopeK (H : Subgroup (TreeAut X)) : Subgroup (TreeAut (envelopeY X m)) :=
  H.map (envelopeEmbed m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeK

theorem isSelfSimilar_envelopeK {H : Subgroup (TreeAut X)} (hH : IsSelfSimilar H) :
    IsSelfSimilar (envelopeK m H) := by
  rintro _ ⟨g, hg, rfl⟩ ⟨i, x⟩
  rw [state_envelopeEmbed]
  exact Subgroup.mem_map_of_mem _ (hH g hg x)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isSelfSimilar_envelopeK

variable (m) in
/-- `H → K`, the corestriction of `envelopeEmbed m`. -/
def envelopeHom (H : Subgroup (TreeAut X)) : ↥H →* ↥(envelopeK m H) :=
  ((envelopeEmbed m).comp H.subtype).codRestrict (envelopeK m H) fun h =>
    Subgroup.mem_map_of_mem _ h.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeHom

theorem envelopeHom_injective [NeZero m] (H : Subgroup (TreeAut X)) :
    Function.Injective (envelopeHom m H) :=
  (MonoidHom.injective_codRestrict _ _ _).2
    ((envelopeEmbed_injective (X := X) (m := m)).comp Subtype.val_injective)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeHom_injective

theorem envelopeHom_surjective (H : Subgroup (TreeAut X)) :
    Function.Surjective (envelopeHom m H) := by
  rintro ⟨_, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeHom_surjective

theorem isFinitelyPresented_envelopeK [NeZero m] {H : Subgroup (TreeAut X)}
    (hH : Group.IsFinitelyPresented H) : Group.IsFinitelyPresented (envelopeK m H) :=
  Group.IsFinitelyPresented.equiv
    (MulEquiv.ofBijective (envelopeHom m H) ⟨envelopeHom_injective H, envelopeHom_surjective H⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isFinitelyPresented_envelopeK

end GroupApproximation.BooneHigman.Metabelian.Envelope
