import GroupApproximation.Computability.SoficRecognitionPi02

/-!
# The arithmetical position of residual finiteness on finite presentations

`research/arithmetical-complexity-table-of-group-properties.md` places
residual finiteness of a *finite* presentation at `Pi^0_2 \ Pi^0_1`, one level
below its position on recursive and enumerated presentations
(`research/residual-finiteness-of-enumerated-presentations-is-pi3-complete.md`,
whose upper-bound section records that "for finite presentations `RF_fp` is
`Pi^0_2` and `Sigma^0_1`-hard").  This file proves that cell.

The drop of one quantifier is exactly the finiteness of the relator list.  A
homomorphism out of a finitely presented group to a finite group is named by
finitely many permutation tables, and "this table family kills every relator"
is a *bounded* conjunction --- a decidable test, not a `Pi^0_1` condition.  So
residual finiteness reads as

```text
  for every word w:  either w dies in the coded group        (Sigma^0_1)
                     or some permutation table family kills every
                     relator and moves w                     (Sigma^0_1)
```

a universal quantifier in front of a recursively enumerable matrix, which is
`Pi^0_2`.

## What is reused

Everything about permutation tables --- the totalised action `act`, the
composite table, mutually inverse table pairs, the permutation `toPerm` they
name, the table `wordTable` of a raw word, and the whole `Primrec` layer --- is
`Computability.SoficRecognitionPi02`, which built it for the soficity bound.
Nothing there is about soficity: a certificate is a permutation representation
of the free group on the code's alphabet, and only the *test* applied to it is
property-specific.  Soficity asks for approximate relator triviality in Hamming
distance; residual finiteness asks for exact relator triviality, which is the
strictly simpler test `wordTable = identity`, and that is the only difference.

## What is proved

* `residuallyFinite_iff_forall_answers` --- the void-challenge normal form: a
  coded group is residually finite exactly when every raw word either dies or
  is separated by a permutation representation killing all relators.
* `sep_iff_exists_cert` --- the separation disjunct is a certificate search
  with a decidable matrix.
* `rePred_rfAnswers` --- one challenge being answered is recursively
  enumerable.
* `pi02_residuallyFinite`, `sigma02_not_residuallyFinite` --- the bounds.
* `rfMarkovData` --- residual finiteness is a Markov property, so
  `Computability.AdianRabinGeneral` applies: `rf_recognition_undecidable` and
  `rf_negative_side_not_re`.
* `rf_fp_strict_position` --- the bound together with the unconditional
  non-enumerability of the negative side, i.e. the ledger cell
  `RF_fp ∈ Π⁰₂ \ Π⁰₁` and `NONRF_fp ∈ Σ⁰₂ \ Σ⁰₁`.

Completeness of `RF_fp` at the second level is **not** claimed: that is the
residually finite Higman problem, the open cell `[RF-Higman]` of the ledger.
The hardness that is proved here is the first-level one, and it comes from the
Adian--Rabin engine of
`research/second-level-rice-theorem-for-local-approximation-properties.md`.

## Research nodes

* `research/arithmetical-complexity-table-of-group-properties.md`
* `research/residual-finiteness-of-enumerated-presentations-is-pi3-complete.md`
* `research/second-level-rice-theorem-for-local-approximation-properties.md`

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace RFPresentationPi02

open ArithmeticalHierarchy
open PresentationCodes AdianRabinWordProblem RawWord
open SoficRecognitionPi02
open AdianRabinGeneral

/-! ## From a finite quotient to a permutation representation

Residual finiteness is stated in Mathlib through finite-index normal
subgroups; a certificate has to be a permutation table family.  The bridge is
Cayley's theorem: a finite group acts faithfully on itself by left
multiplication, and its underlying set is `{0, …, m}` after a bijection. -/

/-- Left multiplication, as a permutation. -/
def leftRegularPerm {Q : Type} [Group Q] (a : Q) : Equiv.Perm Q where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem leftRegularPerm_apply {Q : Type} [Group Q] (a x : Q) :
    leftRegularPerm a x = a * x := rfl

/-- **Cayley's theorem, as a homomorphism.** -/
def leftRegularHom (Q : Type) [Group Q] : Q →* Equiv.Perm Q where
  toFun := leftRegularPerm
  map_one' := Equiv.ext fun x => by simp
  map_mul' a b := Equiv.ext fun x => by simp [mul_assoc]

@[simp] theorem leftRegularHom_apply {Q : Type} [Group Q] (a x : Q) :
    (leftRegularHom Q a) x = a * x := rfl

/-- The left-regular representation is faithful. -/
theorem leftRegularHom_ne_one {Q : Type} [Group Q] {a : Q} (ha : a ≠ 1) :
    leftRegularHom Q a ≠ 1 := by
  intro hcon
  refine ha ?_
  have h := congrArg (fun p : Equiv.Perm Q => p 1) hcon
  simpa using h

/-- Transporting permutations along a bijection is faithful. -/
theorem permCongrHom_ne_one {X Y : Type} (e : X ≃ Y) {p : Equiv.Perm X}
    (hp : p ≠ 1) : permCongrHom e p ≠ 1 := by
  intro hcon
  refine hp (Equiv.ext fun x => ?_)
  have h := congrArg (fun q : Equiv.Perm Y => q (e x)) hcon
  simp only [permCongrHom_apply, Equiv.symm_apply_apply,
    Equiv.Perm.one_apply] at h
  exact e.injective h

/-- **A homomorphism separating a point from `1` in a finite group becomes a
permutation representation on `{0, …, m}`.** -/
theorem exists_perm_hom_of_ne_one {G Q : Type} [Group G] [Group Q] [Finite Q]
    (φ : G →* Q) {g : G} (hg : φ g ≠ 1) :
    ∃ (m : ℕ) (F : G →* Equiv.Perm (Fin (m + 1))), F g ≠ 1 := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card Q = m + 1 := by
    have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.2 ⟨1⟩
    exact ⟨Fintype.card Q - 1, by omega⟩
  refine ⟨m, (permCongrHom (Fintype.equivFinOfCardEq hm)).comp
    ((leftRegularHom Q).comp φ), ?_⟩
  exact permCongrHom_ne_one _ (leftRegularHom_ne_one hg)

/-! ## The challenge and its two answers -/

/-- **The separation certificate, as group theory.**  A representation of the
code's alphabet by permutations of `{0, …, m}` under which every relator of the
code acts trivially --- so that it factors through the coded group, a finite
quotient --- and under which the given word does not. -/
def SeparatedByFiniteQuotient (c : PresentationCode) (w : List (ℕ × Bool)) :
    Prop :=
  ∃ (m : ℕ) (σ : Fin (genCount c) → Equiv.Perm (Fin (m + 1))),
    (∀ r ∈ c.2, FreeGroup.lift σ (wordOf c r) = 1) ∧
      FreeGroup.lift σ (wordOf c w) ≠ 1

/-- One challenge answered: the word either dies in the coded group, or is
separated from `1` by a finite quotient. -/
def Answers (c : PresentationCode) (w : List (ℕ × Bool)) : Prop :=
  WordProblem c w ∨ SeparatedByFiniteQuotient c w

/-- Killing the listed relators kills the relator set. -/
theorem lift_eq_one_of_mem_relatorSet {c : PresentationCode} {m : ℕ}
    {σ : Fin (genCount c) → Equiv.Perm (Fin (m + 1))}
    (h : ∀ r ∈ c.2, FreeGroup.lift σ (wordOf c r) = 1) :
    ∀ x ∈ relatorSet c, FreeGroup.lift σ x = 1 := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_relatorSet_iff.1 hx
  exact h u hu

/-- The homomorphism out of the coded group a separation certificate names. -/
def sepHom {c : PresentationCode} {m : ℕ}
    {σ : Fin (genCount c) → Equiv.Perm (Fin (m + 1))}
    (h : ∀ r ∈ c.2, FreeGroup.lift σ (wordOf c r) = 1) :
    Carrier c →* Equiv.Perm (Fin (m + 1)) :=
  PresentedGroup.toGroup (lift_eq_one_of_mem_relatorSet h)

theorem sepHom_comp_mk {c : PresentationCode} {m : ℕ}
    {σ : Fin (genCount c) → Equiv.Perm (Fin (m + 1))}
    (h : ∀ r ∈ c.2, FreeGroup.lift σ (wordOf c r) = 1) :
    (sepHom h).comp (PresentedGroup.mk (relatorSet c)) = FreeGroup.lift σ := by
  refine FreeGroup.ext_hom _ _ fun j => ?_
  rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  exact PresentedGroup.toGroup.of _

theorem sepHom_mk {c : PresentationCode} {m : ℕ}
    {σ : Fin (genCount c) → Equiv.Perm (Fin (m + 1))}
    (h : ∀ r ∈ c.2, FreeGroup.lift σ (wordOf c r) = 1)
    (y : FreeGroup (Fin (genCount c))) :
    sepHom h (PresentedGroup.mk (relatorSet c) y) = FreeGroup.lift σ y :=
  DFunLike.congr_fun (sepHom_comp_mk h) y

/-- **Residual finiteness of a coded group is a void-challenge statement.**
Every raw word either dies in the group, or is separated from the identity by a
permutation representation of the alphabet that kills all the relators.

The forward direction is Cayley's theorem applied to the finite quotient
Mathlib's definition supplies; the backward direction is the universal property
of the presentation, which turns a relator-killing permutation family into a
homomorphism to a finite group. -/
theorem residuallyFinite_iff_forall_answers (c : PresentationCode) :
    Group.ResiduallyFinite (Carrier c) ↔ ∀ w : List (ℕ × Bool), Answers c w := by
  constructor
  · intro hRF w
    by_cases hw : WordProblem c w
    · exact Or.inl hw
    refine Or.inr ?_
    haveI := hRF
    have hxne : (PresentedGroup.mk (relatorSet c) (wordOf c w) : Carrier c) ≠ 1 :=
      hw
    obtain ⟨N, hN⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem
        (PresentedGroup.mk (relatorSet c) (wordOf c w) : Carrier c) hxne
    have h1 : (QuotientGroup.mk' N.toSubgroup)
        (PresentedGroup.mk (relatorSet c) (wordOf c w) : Carrier c) ≠ 1 := by
      intro hcon
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcon
      exact hN (FiniteIndexNormalSubgroup.mem_toSubgroup_iff.1 hcon)
    obtain ⟨m, F, hF⟩ :=
      exists_perm_hom_of_ne_one (QuotientGroup.mk' N.toSubgroup) h1
    have hlift : ∀ y : FreeGroup (Fin (genCount c)),
        FreeGroup.lift
            (fun j => F (PresentedGroup.mk (relatorSet c) (FreeGroup.of j))) y
          = F (PresentedGroup.mk (relatorSet c) y) := by
      intro y
      have hcomp : F.comp (PresentedGroup.mk (relatorSet c))
          = FreeGroup.lift
              (fun j => F (PresentedGroup.mk (relatorSet c) (FreeGroup.of j))) := by
        refine FreeGroup.ext_hom _ _ fun j => ?_
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact (DFunLike.congr_fun hcomp y).symm
    refine ⟨m, fun j => F (PresentedGroup.mk (relatorSet c) (FreeGroup.of j)),
      ?_, ?_⟩
    · intro r hr
      rw [hlift, PresentedGroup.one_of_mem (wordOf_mem_relatorSet hr), map_one]
    · rw [hlift]
      exact hF
  · intro h
    apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
    intro g hg
    obtain ⟨y, hy⟩ := PresentedGroup.mk_surjective (relatorSet c) g
    obtain ⟨w, hw⟩ := wordOf_surjective c y
    have hgw : PresentedGroup.mk (relatorSet c) (wordOf c w) = g := by
      rw [hw, hy]
    have hnot : ¬ WordProblem c w := by
      intro hcon
      refine hg ?_
      rw [← hgw]
      exact hcon
    rcases h w with hvoid | ⟨m, σ, hrel, hne⟩
    · exact absurd hvoid hnot
    refine ⟨Equiv.Perm (Fin (m + 1)), inferInstance, inferInstance,
      sepHom hrel, ?_⟩
    rw [← hgw, sepHom_mk]
    exact hne

/-! ## The separation certificate, as raw data

The tables and their `Primrec` layer are `SoficRecognitionPi02`; only the test
is new, and it is the exact one: the word's table is the identity table. -/

/-- The permutation representation a valid certificate names, at the explicit
type `Equiv.Perm (Fin (m + 1))`. -/
def certPerm (c : PresentationCode) (cert : PermCert) (h : CertValid c cert)
    (j : Fin (genCount c)) : Equiv.Perm (Fin (cert.1 + 1)) :=
  toPerm cert.1 (certGen c cert (j : ℕ)).1 (certGen c cert (j : ℕ)).2
    (h (j : ℕ) j.isLt)

theorem lift_certPerm (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (x : FreeGroup (Fin (genCount c))) :
    FreeGroup.lift (certPerm c cert h) x
      = (certMicrostate c cert h).hom x := rfl

/-- `SoficRecognitionPi02.act_wordTable_val`, restated at the explicit type
`Fin (cert.1 + 1)`.  The two statements are definitionally the same --- the
microstate's carrier *is* `{0, …, m}` --- but only this spelling puts
`Fin (cert.1 + 1)` where the rewriting below needs to see it. -/
theorem act_wordTable_certPerm (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (w : List (ℕ × Bool)) (i : Fin (cert.1 + 1)) :
    act cert.1 (wordTable c cert w) i.val
      = ((FreeGroup.lift (certPerm c cert h) (wordOf c w)) i).val :=
  act_wordTable_val c cert h w i

/-- `SoficRecognitionPi02.certOf_hom`, restated the same way. -/
theorem lift_certPerm_certOf (c : PresentationCode) (m : ℕ)
    (g : Fin (genCount c) → Equiv.Perm (Fin (m + 1)))
    (x : FreeGroup (Fin (genCount c))) :
    FreeGroup.lift (certPerm c (certOf c m g) (certValid_certOf c m g)) x
      = FreeGroup.lift g x :=
  certOf_hom c m g x

/-- A table acts as the identity on `{0, …, m}`, as a Boolean test. -/
def idOk (m : ℕ) (t : List ℕ) : Bool :=
  decide ((List.range (m + 1)).map (act m t) = List.range (m + 1))

theorem idOk_eq_true_iff (m : ℕ) (t : List ℕ) :
    idOk m t = true ↔ ∀ x, x < m + 1 → act m t x = x := by
  rw [idOk, decide_eq_true_iff]
  exact map_range_eq_range_iff (m + 1) (act m t)

/-- **The exact test.**  A word acts trivially in the certificate's
representation exactly when its table is the identity.  This is the whole
difference from the soficity bound, where the same certificate is tested
approximately, in Hamming distance. -/
theorem lift_certPerm_eq_one_iff (c : PresentationCode) (cert : PermCert)
    (h : CertValid c cert) (w : List (ℕ × Bool)) :
    FreeGroup.lift (certPerm c cert h) (wordOf c w) = 1
      ↔ idOk cert.1 (wordTable c cert w) = true := by
  rw [idOk_eq_true_iff]
  constructor
  · intro h1 x hx
    have h2 := act_wordTable_certPerm c cert h w ⟨x, hx⟩
    rw [h1] at h2
    simpa using h2
  · intro h1
    refine Equiv.ext fun i => Fin.val_injective ?_
    show ((FreeGroup.lift (certPerm c cert h) (wordOf c w)) i).val = (i : ℕ)
    rw [← act_wordTable_certPerm c cert h w i]
    exact h1 i.val i.isLt

/-- Well-formedness at every generator, as a Boolean test. -/
def validAllOk (c : PresentationCode) (cert : PermCert) : Bool :=
  decide ((List.range (c.1 + 1)).map (validOk c cert)
    = (List.range (c.1 + 1)).map fun _ => true)

theorem validAllOk_eq_true_iff (c : PresentationCode) (cert : PermCert) :
    validAllOk c cert = true ↔ CertValid c cert := by
  rw [validAllOk, decide_eq_true_iff, map_eq_map_iff]
  constructor
  · intro hv i hi
    have h := hv i (List.mem_range.2 hi)
    rw [validOk, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
    exact h
  · intro hv i hi
    rw [validOk, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact hv i (List.mem_range.1 hi)

/-- Every relator acts trivially, as a Boolean test.  This is the bounded
conjunction that a *finite* presentation makes decidable, and it is the whole
reason `RF_fp` sits one level below `RF_rec`. -/
def relatorsOk (c : PresentationCode) (cert : PermCert) : Bool :=
  decide (c.2.map (fun r => idOk cert.1 (wordTable c cert r))
    = c.2.map fun _ => true)

theorem relatorsOk_eq_true_iff (c : PresentationCode) (cert : PermCert) :
    relatorsOk c cert = true
      ↔ ∀ r ∈ c.2, idOk cert.1 (wordTable c cert r) = true := by
  rw [relatorsOk, decide_eq_true_iff, map_eq_map_iff]

/-- **The separation checker.**  Every clause is an equality of lists of
naturals, so this is a total Boolean function of raw data. -/
def sepCheck (x : PresentationCode × List (ℕ × Bool)) (cert : PermCert) : Bool :=
  (validAllOk x.1 cert && relatorsOk x.1 cert) &&
    decide (idOk cert.1 (wordTable x.1 cert x.2) = false)

theorem sepCheck_eq_true_iff (x : PresentationCode × List (ℕ × Bool))
    (cert : PermCert) :
    sepCheck x cert = true ↔
      (CertValid x.1 cert ∧
        (∀ r ∈ x.1.2, idOk cert.1 (wordTable x.1 cert r) = true) ∧
        idOk cert.1 (wordTable x.1 cert x.2) = false) := by
  rw [sepCheck, Bool.and_eq_true, Bool.and_eq_true, validAllOk_eq_true_iff,
    relatorsOk_eq_true_iff, decide_eq_true_iff, and_assoc]

/-- **The separation disjunct is a certificate search.** -/
theorem sep_iff_exists_cert (c : PresentationCode) (w : List (ℕ × Bool)) :
    SeparatedByFiniteQuotient c w
      ↔ ∃ cert : PermCert, sepCheck (c, w) cert = true := by
  constructor
  · rintro ⟨m, σ, hrel, hne⟩
    refine ⟨certOf c m σ, (sepCheck_eq_true_iff (c, w) _).2
      ⟨certValid_certOf c m σ, ?_, ?_⟩⟩
    · intro r hr
      rw [← lift_certPerm_eq_one_iff c (certOf c m σ) (certValid_certOf c m σ) r,
        lift_certPerm_certOf c m σ (wordOf c r)]
      exact hrel r hr
    · have hno : ¬ (FreeGroup.lift
          (certPerm c (certOf c m σ) (certValid_certOf c m σ))
          (wordOf c w) = 1) := by
        rw [lift_certPerm_certOf c m σ (wordOf c w)]
        exact hne
      rw [lift_certPerm_eq_one_iff] at hno
      cases hb : idOk (certOf c m σ).1 (wordTable c (certOf c m σ) w) with
      | false => rfl
      | true => exact absurd hb hno
  · rintro ⟨cert, hc⟩
    obtain ⟨hvalid, hrel, hne⟩ := (sepCheck_eq_true_iff (c, w) cert).1 hc
    refine ⟨cert.1, certPerm c cert hvalid, ?_, ?_⟩
    · intro r hr
      rw [lift_certPerm_eq_one_iff]
      exact hrel r hr
    · intro hcon
      rw [lift_certPerm_eq_one_iff] at hcon
      rw [hcon] at hne
      exact Bool.noConfusion hne

/-! ## The checker is primitive recursive -/

section Effective

variable {α : Type} [Primcodable α]

theorem primrec_idOk {fm : α → ℕ} {ft : α → List ℕ}
    (hm : Primrec fm) (ht : Primrec ft) :
    Primrec fun a => idOk (fm a) (ft a) := by
  have hrange : Primrec fun a => List.range (fm a + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hm)
  have hmap : Primrec fun a => (List.range (fm a + 1)).map (act (fm a) (ft a)) :=
    Primrec.list_map hrange
      (primrec_act (hm.comp Primrec.fst) (ht.comp Primrec.fst)
        Primrec.snd).to₂
  exact (Primrec.eq.comp hmap hrange).decide.of_eq fun _ => rfl

theorem primrec_validAllOk {fc : α → PresentationCode} {fcert : α → PermCert}
    (hc : Primrec fc) (hcert : Primrec fcert) :
    Primrec fun a => validAllOk (fc a) (fcert a) := by
  have hrange : Primrec fun a : α => List.range ((fc a).1 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp hc))
  have hleft : Primrec fun a : α =>
      (List.range ((fc a).1 + 1)).map (validOk (fc a) (fcert a)) :=
    Primrec.list_map hrange
      (primrec_validOk (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        Primrec.snd).to₂
  have hright : Primrec fun a : α =>
      (List.range ((fc a).1 + 1)).map fun _ : ℕ => true :=
    Primrec.list_map hrange (Primrec.const true).to₂
  exact (Primrec.eq.comp hleft hright).decide.of_eq fun _ => rfl

theorem primrec_relatorsOk {fc : α → PresentationCode} {fcert : α → PermCert}
    (hc : Primrec fc) (hcert : Primrec fcert) :
    Primrec fun a => relatorsOk (fc a) (fcert a) := by
  have hrelators : Primrec fun a : α => (fc a).2 := Primrec.snd.comp hc
  have hleft : Primrec fun a : α =>
      (fc a).2.map fun r => idOk (fcert a).1 (wordTable (fc a) (fcert a) r) :=
    Primrec.list_map hrelators
      (primrec_idOk (Primrec.fst.comp (hcert.comp Primrec.fst))
        (primrec_wordTable (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
          Primrec.snd)).to₂
  have hright : Primrec fun a : α =>
      (fc a).2.map fun _ : List (ℕ × Bool) => true :=
    Primrec.list_map hrelators (Primrec.const true).to₂
  exact (Primrec.eq.comp hleft hright).decide.of_eq fun _ => rfl

end Effective

/-- The checker input type, abbreviated so the `Primrec` proof stays
readable. -/
abbrev SepInput : Type := PresentationCode × List (ℕ × Bool)

theorem primrec_sepCheck : Primrec₂ sepCheck := by
  have hc : Primrec fun z : SepInput × PermCert => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hw : Primrec fun z : SepInput × PermCert => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hcert : Primrec fun z : SepInput × PermCert => z.2 := Primrec.snd
  have hvalid : Primrec fun z : SepInput × PermCert =>
      validAllOk z.1.1 z.2 := primrec_validAllOk hc hcert
  have hrel : Primrec fun z : SepInput × PermCert =>
      relatorsOk z.1.1 z.2 := primrec_relatorsOk hc hcert
  have hword : Primrec fun z : SepInput × PermCert =>
      idOk z.2.1 (wordTable z.1.1 z.2 z.1.2) :=
    primrec_idOk (Primrec.fst.comp hcert) (primrec_wordTable hc hcert hw)
  exact (Primrec.and.comp (Primrec.and.comp hvalid hrel)
    (Primrec.eq.comp hword (Primrec.const false)).decide).of_eq fun _ => rfl

/-! ## Answering a challenge is recursively enumerable -/

/-- The search space for one word: a word-problem derivation certificate for
the void disjunct, paired with a permutation certificate for the separation
disjunct. -/
abbrev RFAnswerData : Type := WordProblemRE.SearchData × PermCert

/-- The matrix of the answer search. -/
def rfAnswerCheck (x : SepInput) (b : RFAnswerData) : Bool :=
  WordProblemRE.searchCheck x b.1 || sepCheck x b.2

theorem rfAnswerCheck_iff (x : SepInput) :
    (∃ b : RFAnswerData, rfAnswerCheck x b = true) ↔ Answers x.1 x.2 := by
  constructor
  · rintro ⟨⟨p, cert⟩, hb⟩
    rw [rfAnswerCheck, Bool.or_eq_true] at hb
    rcases hb with h | h
    · exact Or.inl ((WordProblemRE.wordProblemPred_iff_exists x).2 ⟨p, h⟩)
    · exact Or.inr ((sep_iff_exists_cert x.1 x.2).2 ⟨cert, h⟩)
  · rintro (hvoid | hsep)
    · obtain ⟨p, hp⟩ := (WordProblemRE.wordProblemPred_iff_exists x).1 hvoid
      exact ⟨(p, default), by
        rw [rfAnswerCheck, Bool.or_eq_true]; exact Or.inl hp⟩
    · obtain ⟨cert, hcert⟩ := (sep_iff_exists_cert x.1 x.2).1 hsep
      exact ⟨(default, cert), by
        rw [rfAnswerCheck, Bool.or_eq_true]; exact Or.inr hcert⟩

theorem primrec_rfAnswerCheck : Primrec₂ rfAnswerCheck := by
  have hsearch : Primrec fun z : SepInput × RFAnswerData =>
      WordProblemRE.searchCheck z.1 z.2.1 :=
    WordProblemRE.primrec_searchCheck.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hsep : Primrec fun z : SepInput × RFAnswerData =>
      sepCheck z.1 z.2.2 :=
    primrec_sepCheck.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (Primrec.or.comp hsearch hsep).of_eq fun _ => rfl

/-- **Answering one challenge is recursively enumerable.** -/
theorem rePred_rfAnswers :
    REPred fun x : PresentationCode × List (ℕ × Bool) => Answers x.1 x.2 :=
  (WordProblemRE.rePred_exists_eq_true primrec_rfAnswerCheck.to_comp).of_eq
    rfAnswerCheck_iff

/-! ## The arithmetical bounds -/

/-- The word named by a scale index.  Surjectivity onto all words is what makes
`∀ n` equivalent to `∀ w`. -/
def decodeWord (n : ℕ) : List (ℕ × Bool) :=
  (Encodable.decode (α := List (ℕ × Bool)) n).getD []

theorem primrec_decodeWord : Primrec decodeWord :=
  (Primrec.option_getD.comp Primrec.decode
    (Primrec.const ([] : List (ℕ × Bool)))).of_eq fun _ => rfl

theorem decodeWord_surjective (w : List (ℕ × Bool)) :
    decodeWord (Encodable.encode w) = w := by
  simp [decodeWord]

/-! Sealing the decoder keeps the arithmetical bookkeeping cheap, exactly as in
`SoficRecognitionPi02`: nothing below needs to look inside it. -/

attribute [irreducible] decodeWord

/-- The matrix of the `Π⁰₂` normal form: the scale index is decoded into a
word, and that word's challenge is searched. -/
def scaledAnswerCheck (z : PresentationCode × ℕ) (b : RFAnswerData) : Bool :=
  rfAnswerCheck (z.1, decodeWord z.2) b

theorem primrec_scaledAnswerCheck : Primrec₂ scaledAnswerCheck := by
  have h : Primrec fun z : (PresentationCode × ℕ) × RFAnswerData =>
      rfAnswerCheck (z.1.1, decodeWord z.1.2) z.2 :=
    primrec_rfAnswerCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (primrec_decodeWord.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd
  exact h.of_eq fun _ => rfl

/-- **Answering the challenge named by a scale index is recursively
enumerable.** -/
theorem rePred_scaledAnswers :
    REPred fun z : PresentationCode × ℕ => Answers z.1 (decodeWord z.2) :=
  (WordProblemRE.rePred_exists_eq_true primrec_scaledAnswerCheck.to_comp).of_eq
    fun z => rfAnswerCheck_iff (z.1, decodeWord z.2)

/-- **Recognising residual finiteness from a finite presentation code is
`Π⁰₂`.** -/
theorem pi02_residuallyFinite :
    Pi02 fun c : PresentationCode => Group.ResiduallyFinite (Carrier c) := by
  refine ⟨fun z : PresentationCode × ℕ => Answers z.1 (decodeWord z.2),
    rePred_scaledAnswers, ?_⟩
  intro c
  refine Iff.trans (residuallyFinite_iff_forall_answers c) ?_
  constructor
  · intro h n
    exact h (decodeWord n)
  · intro h w
    have hn := h (Encodable.encode w)
    rwa [decodeWord_surjective w] at hn

/-- **Recognising failure of residual finiteness from a finite presentation
code is `Σ⁰₂`.** -/
theorem sigma02_not_residuallyFinite :
    Sigma02 fun c : PresentationCode => ¬ Group.ResiduallyFinite (Carrier c) :=
  (sigma02_compl_iff _).2 pi02_residuallyFinite

/-! ## Residual finiteness is a Markov property

The three Markov clauses.  Heredity is Cayley again: a subgroup of a residually
finite group inherits the finite quotients by restriction.  Free groups are
residually finite (`freeGroup_residuallyFinite`).  The forbidden code is the
nonsofic finite presentation code, which cannot be residually finite because
residual finiteness implies soficity. -/

/-- **Residual finiteness passes to subgroups**, in the injective-homomorphism
form `AdianRabinGeneral.MarkovData` asks for. -/
theorem residuallyFinite_of_injective {H K : Type} [Group H] [Group K]
    (f : H →* K) (hf : Function.Injective f)
    (hK : Group.ResiduallyFinite K) : Group.ResiduallyFinite H := by
  haveI := hK
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hfg : f g ≠ 1 := by
    intro hcon
    exact hg (hf (by rw [hcon, map_one]))
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (f g) hfg
  refine ⟨K ⧸ N.toSubgroup, inferInstance, inferInstance,
    (QuotientGroup.mk' N.toSubgroup).comp f, ?_⟩
  intro hcon
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcon
  exact hN (FiniteIndexNormalSubgroup.mem_toSubgroup_iff.1 hcon)

/-- The trivial group is residually finite, being finite. -/
theorem residuallyFinite_trivialCode :
    Group.ResiduallyFinite (Carrier trivialCode) := by
  haveI := subsingleton_carrier_trivialCode
  haveI : Finite (Carrier trivialCode) := Finite.of_subsingleton
  infer_instance

/-- **A finite presentation code that is not residually finite**, with no
hypothesis: the nonsofic seed of `SoficRecognitionSecondLevel` cannot be
residually finite, since residual finiteness implies soficity. -/
theorem exists_non_residuallyFinite_code :
    ∃ c : PresentationCode, ¬ Group.ResiduallyFinite (Carrier c) := by
  obtain ⟨seed, hseed⟩ :=
    SoficRecognitionSecondLevel.exists_nonsofic_presentationCode
  refine ⟨seed, fun hRF => hseed ?_⟩
  haveI := hRF
  exact isSofic_of_residuallyFinite

/-- **Residual finiteness is a Markov property**, given a code for a group that
fails it. -/
noncomputable def rfMarkovData (c : PresentationCode)
    (hc : ¬ Group.ResiduallyFinite (Carrier c)) :
    MarkovData (fun (H : Type) (_ : Group H) ↦ Group.ResiduallyFinite H) where
  hereditary f hf hK := residuallyFinite_of_injective f hf hK
  free α _ := freeGroup_residuallyFinite α
  positiveCode := trivialCode
  positive := residuallyFinite_trivialCode
  forbidden := c
  forbidden_not := hc

/-- **Recognising residual finiteness from a finite presentation is
undecidable**, given undecidability of the word problem. -/
theorem rf_recognition_undecidable
    (hw : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred
      (codeProperty (fun (K : Type) (_ : Group K) ↦ Group.ResiduallyFinite K)) := by
  obtain ⟨c, hc⟩ := exists_non_residuallyFinite_code
  exact recognition_undecidable_of_wordProblem (rfMarkovData c hc) hw

/-- The non-residually-finite side is not even recursively enumerable, given
that the negative side of the word problem is not. -/
theorem rf_negative_side_not_re
    (hw : ¬ REPred fun x ↦ ¬ AdianRabinWordProblem.wordProblemPred x) :
    ¬ REPred fun c : PresentationCode ↦ ¬ Group.ResiduallyFinite (Carrier c) := by
  obtain ⟨c, hc⟩ := exists_non_residuallyFinite_code
  exact negative_side_not_re_of_wordProblem (rfMarkovData c hc) hw

/-- **No enumeration lists the non-residually-finite finite presentation
codes.**  Unconditional: the hypothesis of `rf_negative_side_not_re` is
`WordProblemRE.not_rePred_compl_wordProblemPred`, which carries none. -/
theorem non_residuallyFinite_not_re :
    ¬ REPred fun c : PresentationCode ↦ ¬ Group.ResiduallyFinite (Carrier c) :=
  rf_negative_side_not_re WordProblemRE.not_rePred_compl_wordProblemPred

/-- **The arithmetical position of residual finiteness on finite presentation
codes**: `Π⁰₂` but not `Π⁰₁`, and its complement `Σ⁰₂` but not `Σ⁰₁`.  This is
the `fp` cell of the residually-finite row of
`research/arithmetical-complexity-table-of-group-properties.md`. -/
theorem rf_fp_strict_position :
    (Pi02 (fun c : PresentationCode => Group.ResiduallyFinite (Carrier c)) ∧
        ¬ Pi01 (fun c : PresentationCode =>
          Group.ResiduallyFinite (Carrier c))) ∧
      (Sigma02 (fun c : PresentationCode =>
          ¬ Group.ResiduallyFinite (Carrier c)) ∧
        ¬ Sigma01 (fun c : PresentationCode =>
          ¬ Group.ResiduallyFinite (Carrier c))) :=
  strict_first_level_pair pi02_residuallyFinite non_residuallyFinite_not_re

/-! ## The closed form -/

/-- **The ledger cell**, as a closed proposition: `RF_fp ∈ Π⁰₂ \ Π⁰₁` and
`NONRF_fp ∈ Σ⁰₂ \ Σ⁰₁`. -/
def RFPresentationStrictPosition : Prop :=
  (Pi02 (fun c : PresentationCode => Group.ResiduallyFinite (Carrier c)) ∧
      ¬ Pi01 (fun c : PresentationCode =>
        Group.ResiduallyFinite (Carrier c))) ∧
    (Sigma02 (fun c : PresentationCode =>
        ¬ Group.ResiduallyFinite (Carrier c)) ∧
      ¬ Sigma01 (fun c : PresentationCode =>
        ¬ Group.ResiduallyFinite (Carrier c)))

/-- **The cell holds.**  No hypothesis, no construction datum. -/
theorem rfPresentationStrictPosition : RFPresentationStrictPosition :=
  rf_fp_strict_position

end RFPresentationPi02
end GroupApproximation
