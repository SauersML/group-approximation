import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Computability.PresentationCodes
import GroupApproximation.Higman.EmbeddingTheorem
import GroupApproximation.Higman.MikhailovaRankThreeWitness

/-!
# The marked output of the Higman compiler (`lem:mikhailova`, data half)

`mf_recognition_complexity.tex`, Lemma `lem:mikhailova`, asks for an algorithm
producing from `e`

* a finite presentation `⟨X_e | R_e⟩` of a group `Λ_e`;
* words `w_x, w_y, w_t ∈ F(X_e)`;
* a finite generating set of a subgroup `M_e ≤ F(X_e) × F(X_e)`;

such that `x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t` induces an embedding `Q_e → Λ_e` and
`M_e = {(u,v) : u = v in Λ_e}`.

This module fixes the *output type* of that algorithm, on top of the coding
layers the repository already has:

* the source `Q_e = F/N_e` is `PresentedGroup (rank3Relators P)` for a standard
  recursively enumerated presentation code `P` read on the three letters
  `x, y, t` (`EnumeratedPresentationCodes.rawRelator` composed with
  `Higman.rawToFree 2`), matching the printed `F = F(x,y,t)`;
* the host `Λ_e` is the repository's concrete *finite* presentation coding
  `PresentationCodes.Carrier`, so `⟨X_e | R_e⟩` is literally a code;
* `M_e` is `Higman.Mikhailova.freeSubgroup`, whose finite generating set is
  `Higman.Mikhailova.freeGenerators` --- the printed pairs `(z,z)`, `z ∈ X_e`,
  and `(r,1)`, `r ∈ R_e`.

Mihailova's clause of the printed lemma is *proved here*, not assumed: it is
`Higman.Mikhailova.mem_freeSubgroup_iff_presented_mk_eq`, together with
`Higman.Mikhailova.freeSubgroup_fg` for finiteness of the generating set.

Only the marked-embedding clause is carried as data, because only it is the
output of an algorithm this development does not contain; see
`EffectiveHigmanCompiler.lean`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler

open Higman

noncomputable section

/-! ## 1.  The source `Q_e = F/N_e` on the three letters `x, y, t` -/

/-- The manuscript's input: a standard recursively enumerated presentation
code.  A recursive presentation of `Q_e` on `x, y, t` is computable from `e`
by Lemmas `lem:switch` and `lem:bridge`; this module takes such a code as
given and is uniform in it. -/
abbrev RecPresCode : Type := EnumeratedPresentationCodes.PresentationCode

/-- The printed free group `F = F(x, y, t)`.  Letter `0` is `x`, letter `1` is
`y`, letter `2` is `t`: the numbering already used by
`Higman.BridgeEff.pi3`. -/
abbrev Source : Type := MikhailovaRankThree.Source

/-- Read a raw word on three letters in `F = F(x,y,t)`. -/
def rank3Word (v : Higman.RawWord) : Source := rawToFree 2 v

/-- The relators enumerated by a code, read in `F = F(x,y,t)`. -/
def rank3Relators (P : RecPresCode) : Set Source :=
  Set.range fun address : ℕ =>
    rank3Word (EnumeratedPresentationCodes.rawRelator P address)

/-- The printed group `Q_e = F/N_e`. -/
abbrev PresentedQ (P : RecPresCode) : Type := PresentedGroup (rank3Relators P)

/-- The printed quotient map `q_e : F → Q_e`. -/
abbrev quotientQ (P : RecPresCode) : Source →* PresentedQ P :=
  MikhailovaRankThree.quotientHom (rank3Relators P)

/-- The printed normal subgroup `N_e = ker q_e`. -/
def kernelN (P : RecPresCode) : Subgroup Source :=
  Subgroup.normalClosure (rank3Relators P)

/-- `q_e(f) = 1` exactly when `f ∈ N_e`.  This is the last link of the printed
chain of equivalences in `lem:mikhailova`. -/
theorem quotientQ_eq_one_iff (P : RecPresCode) (f : Source) :
    quotientQ P f = 1 ↔ f ∈ kernelN P := by
  show QuotientGroup.mk' (Subgroup.normalClosure (rank3Relators P)) f = 1 ↔
    f ∈ Subgroup.normalClosure (rank3Relators P)
  exact QuotientGroup.eq_one_iff f

/-! ## 2.  The host `Λ_e = ⟨X_e | R_e⟩` -/

/-- The printed finite alphabet `X_e`. -/
abbrev HostAlphabet (c : PresentationCodes.PresentationCode) : Type :=
  Fin (PresentationCodes.genCount c)

/-- The printed finite relator set `R_e`. -/
abbrev hostRelators (c : PresentationCodes.PresentationCode) :
    Set (FreeGroup (HostAlphabet c)) :=
  ↑(PresentationCodes.relatorFinset c)

/-- `R_e` is finite: it is the coercion of a `Finset`. -/
theorem hostRelators_finite (c : PresentationCodes.PresentationCode) :
    (hostRelators c).Finite :=
  (PresentationCodes.relatorFinset c).finite_toSet

/-- The printed group `Λ_e`, presented by the finite presentation code. -/
abbrev Host (c : PresentationCodes.PresentationCode) : Type :=
  PresentedGroup (hostRelators c)

/-- `Λ_e` is finitely presented: the alphabet is a `Fin` type and the relator
set is a `Finset`.  This is the printed "a finite presentation `⟨X_e | R_e⟩`
of a group `Λ_e`". -/
theorem host_isFinitelyPresented (c : PresentationCodes.PresentationCode) :
    Group.IsFinitelyPresented (Host c) :=
  inferInstance

/-- The quotient map `F(X_e) → Λ_e`. -/
abbrev hostQuotient (c : PresentationCodes.PresentationCode) :
    FreeGroup (HostAlphabet c) →* Host c :=
  MikhailovaRankThree.quotientHom (hostRelators c)

/-! ## 3.  The marked words `w_x, w_y, w_t` -/

/-- The homomorphism `F(x,y,t) → F(X_e)` determined by the three marked words:
`x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t`.  Its value at `f` is the printed `w_f`. -/
def markedHom (c : PresentationCodes.PresentationCode) (wx wy wt : Higman.RawWord) :
    Source →* FreeGroup (HostAlphabet c) :=
  FreeGroup.lift fun i : Fin 3 =>
    if i = 0 then PresentationCodes.wordOf c wx
    else if i = 1 then PresentationCodes.wordOf c wy
    else PresentationCodes.wordOf c wt

/-- The marked assignment on generators: `x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t`. -/
theorem markedHom_apply_of (c : PresentationCodes.PresentationCode)
    (wx wy wt : Higman.RawWord) (i : Fin 3) :
    markedHom c wx wy wt (FreeGroup.of i) =
      if i = 0 then PresentationCodes.wordOf c wx
      else if i = 1 then PresentationCodes.wordOf c wy
      else PresentationCodes.wordOf c wt :=
  FreeGroup.lift_apply_of

/-! ## 4.  The output of the compiler -/

/-- The finite data the compiler emits: a finite presentation code for `Λ_e`
and the three marked words `w_x, w_y, w_t`.  It is a `Primcodable` type, so
"the compiler is computable" is a statement about it. -/
abbrev RawMarkedOutput : Type :=
  PresentationCodes.PresentationCode × Higman.RawWord × Higman.RawWord × Higman.RawWord

/-- **The output of the algorithm of `lem:mikhailova`.**  The finite
presentation `⟨X_e | R_e⟩`, the three words `w_x, w_y, w_t`, and the printed
clause that they *induce an embedding* `Q_e → Λ_e`.

The Mihailova subgroup `M_e` is not a field: it is determined by `host`, and
its two printed properties --- a finite generating set, and
`M_e = {(u,v) : u = v in Λ_e}` --- are theorems below, off
`Higman.Mikhailova`. -/
structure MarkedHigmanOutput (P : RecPresCode) where
  /-- The finite presentation `⟨X_e | R_e⟩` of `Λ_e`, as a code. -/
  host : PresentationCodes.PresentationCode
  /-- The word `w_x ∈ F(X_e)`. -/
  wordX : Higman.RawWord
  /-- The word `w_y ∈ F(X_e)`. -/
  wordY : Higman.RawWord
  /-- The word `w_t ∈ F(X_e)`. -/
  wordT : Higman.RawWord
  /-- The induced map `Q_e → Λ_e`. -/
  emb : PresentedQ P →* Host host
  /-- `x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t` *induces* it. -/
  emb_comm :
    (hostQuotient host).comp (markedHom host wordX wordY wordT) =
      emb.comp (quotientQ P)
  /-- It is an *embedding*. -/
  emb_injective : Function.Injective emb

namespace MarkedHigmanOutput

variable {P : RecPresCode} (o : MarkedHigmanOutput P)

/-- The finite data, forgetting the semantic clauses. -/
def raw : RawMarkedOutput := (o.host, o.wordX, o.wordY, o.wordT)

/-- The printed `w_f`: the image of `f` under `x ↦ w_x`, `y ↦ w_y`,
`t ↦ w_t`. -/
def markedWord : Source →* FreeGroup (HostAlphabet o.host) :=
  markedHom o.host o.wordX o.wordY o.wordT

/-- The printed Mihailova subgroup `M_e ≤ F(X_e) × F(X_e)`. -/
def mihailova :
    Subgroup (FreeGroup (HostAlphabet o.host) ×
      FreeGroup (HostAlphabet o.host)) :=
  Mikhailova.freeSubgroup (hostRelators o.host)

/-- The printed generating set of `M_e`: the diagonal pairs `(z,z)` for the
generators `z ∈ X_e`, and the pairs `(r,1)` for the relators `r ∈ R_e`. -/
def mihailovaGenerators :
    Set (FreeGroup (HostAlphabet o.host) × FreeGroup (HostAlphabet o.host)) :=
  Mikhailova.freeGenerators (hostRelators o.host)

/-- The displayed generating set is finite. -/
theorem mihailovaGenerators_finite : o.mihailovaGenerators.Finite := by
  show (Mikhailova.freeGenerators (hostRelators o.host)).Finite
  exact (Set.finite_range _).union
    ((hostRelators_finite o.host).image Mikhailova.firstHom)

/-- **The printed "a finite generating set of a subgroup
`M_e ≤ F(X_e) × F(X_e)`"**, with the displayed pairs as the witness. -/
theorem exists_finite_generating_set_mihailova :
    ∃ S : Set (FreeGroup (HostAlphabet o.host) ×
        FreeGroup (HostAlphabet o.host)),
      S.Finite ∧ Subgroup.closure S = o.mihailova :=
  ⟨o.mihailovaGenerators, o.mihailovaGenerators_finite, rfl⟩

/-- `M_e` is finitely generated. -/
theorem mihailova_fg : o.mihailova.FG :=
  Mikhailova.freeSubgroup_fg (hostRelators_finite o.host)

/-- **Mihailova's lemma, at this output.**  `(u,v) ∈ M_e` exactly when `u = v`
in `Λ_e`.  Proved in the repository (`Higman.Mikhailova`), not assumed. -/
theorem mem_mihailova_iff (u v : FreeGroup (HostAlphabet o.host)) :
    (u, v) ∈ o.mihailova ↔
      PresentedGroup.mk (hostRelators o.host) u =
        PresentedGroup.mk (hostRelators o.host) v :=
  Mikhailova.mem_freeSubgroup_iff_presented_mk_eq (hostRelators o.host) u v

/-- **The printed equation `M_e = {(u,v) : u = v in Λ_e}`.** -/
theorem mihailova_coe_eq :
    (o.mihailova :
        Set (FreeGroup (HostAlphabet o.host) ×
          FreeGroup (HostAlphabet o.host))) =
      {p | PresentedGroup.mk (hostRelators o.host) p.1 =
        PresentedGroup.mk (hostRelators o.host) p.2} := by
  ext p
  obtain ⟨u, v⟩ := p
  exact o.mem_mihailova_iff u v

/-! ### The marked embedding, in kernel form -/

/-- The printed "`x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t` induces an embedding
`Q_e → Λ_e`", read off as an equation between subgroups of `F`: the words
`w_f` die in `Λ_e` exactly on `N_e`. -/
theorem markedWord_ker :
    ((hostQuotient o.host).comp o.markedWord).ker = kernelN P :=
  MikhailovaRankThree.kernel_eq_normalClosure_of_markedEmbedding
    (rank3Relators P) (hostRelators o.host) o.markedWord o.emb o.emb_injective
    o.emb_comm

/-- Pointwise form: `w_f = 1` in `Λ_e` if and only if `f ∈ N_e`. -/
theorem hostQuotient_markedWord_eq_one_iff (f : Source) :
    hostQuotient o.host (o.markedWord f) = 1 ↔ f ∈ kernelN P := by
  constructor
  · intro hf
    have hmem : f ∈ ((hostQuotient o.host).comp o.markedWord).ker :=
      MonoidHom.mem_ker.mpr hf
    rw [o.markedWord_ker] at hmem
    exact hmem
  · intro hf
    have hmem : f ∈ ((hostQuotient o.host).comp o.markedWord).ker := by
      rw [o.markedWord_ker]
      exact hf
    exact MonoidHom.mem_ker.mp hmem

/-- `w_f = 1` in `Λ_e` if and only if `q_e(f) = 1`, "because the embedding is
injective".  This is the middle link of the printed chain. -/
theorem hostQuotient_markedWord_eq_one_iff_quotientQ (f : Source) :
    hostQuotient o.host (o.markedWord f) = 1 ↔ quotientQ P f = 1 :=
  (o.hostQuotient_markedWord_eq_one_iff f).trans
    (quotientQ_eq_one_iff P f).symm

end MarkedHigmanOutput

end

end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
