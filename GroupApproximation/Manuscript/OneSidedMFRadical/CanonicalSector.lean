import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Sofic.ActualCoronaMFRadical

/-!
# Section~4 at the manuscript's own radical, and its printed assembly

`non_mf_groups_exist.tex`, `\section{The canonical Kazhdan sector and the MF
radical}`: Theorem~`thm:normal-kazhdan` and the paragraph headed
`\begin{proof}[Proof of Theorem~\ref{thm:compression-criterion}]`.

Two things in that section are not yet available in the form the print uses.

*The radical.*  `NormalKazhdan` states the normal-Kazhdan theorem with
`actualCoronaMFResidual`, the basis-free radical taken over arbitrary finite
coordinate sets.  What the manuscript writes as `Rad_MF(G)` is
`manuscriptCoronaMFResidual`: the intersection of the kernels of the
homomorphisms into the coronas with coordinates `M_{d_n}(ℂ)` for a sequence of
*natural numbers* `d`.  The two subgroups are equal
(`manuscriptCoronaMFResidual_eq_actualCoronaMFResidual`), so the transfer is a
rewrite; but the printed theorem is the one over natural dimensions, and it
should be readable as such.  `NormalKazhdanPrintedRadical` is that statement.

*The conclusion, unfolded.*  The printed proof of `thm:normal-kazhdan` ends
"Thus every corona homomorphism kills `K`".  That sentence is the membership
`K ≤ Rad_MF(G)` with the radical unfolded, and `NormalKazhdanCoronaVanishing`
records it in exactly that shape: for every dimension sequence `d` with
`d n > 0` and every `Θ : G → U(𝒬_d)`, the containment `K ≤ ker Θ`.  It is the
form in which the theorem is actually consumed, and it is not the form in
which `CoronaImageNormalKazhdan.manuscriptNormalKazhdanObstructionViaCoronaImage`
is stated: that declaration takes a `KazhdanCompressionCore` and the printed
containment `K ⊆ N_comp`, whereas the hypothesis here is the abstract one
`K ≤ D ≤ R_{∞→2}(G)` of `thm:normal-kazhdan`.

*The assembly.*  `PrintedCriterionAssembly` follows the printed proof of
Theorem~A link by link on the exact printed defect `printedDefect`: the
generators `[ucu⁻¹, ℓ]` land in `R_{∞→2}(G)` by `cor:defect-hs`; the residual
is normal; hence the normal closure `𝔇_G(L)` of those generators is inside it;
and `thm:normal-kazhdan` closes.  The third link is supplied by the shared
`printedDefect_le_opToHSShadowResidual_direct` lemma, which derives it from the
first two links along the printed route and never passes through the
development's larger `compressionCentralizerDefect`.  This assembly reuses
that lemma rather than reconstructing the same normal-closure argument.

`PrintedDefectCoronaVanishing` is the composite of the assembly with the
unfolded conclusion, and is the most concrete printed form of Theorem~A: a
normal Kazhdan subgroup of `𝔇_G(L)` is killed by every homomorphism of `G`
into every natural-dimension norm-matrix corona.

Nothing here reproves `lem:central-corona-corner` (the `CentralCoronaCorner`
module), `cor:defect-hs` (`CompressionDefectHSInvisible`, in `DefectHS`),
`eq:shadow-residual` (`ShadowResidualIsIntersectionOfHSKernels`, in
`ShadowResidual`), or the three radical clauses of
`thm:compression-criterion` (`OneSidedCompressionCriterion`, in
`PrintedCriterion`); those are used as given.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

noncomputable section

/-! ## `thm:normal-kazhdan` over the printed natural-dimension radical -/

/-- **Theorem `thm:normal-kazhdan`, with `Rad_MF(G)` as printed.**  For a
countable `G`, a subgroup `D ≤ R_{∞→2}(G)`, and a normal property-`(T)`
subgroup `K ≤ D`, the containment `K ≤ Rad_MF(G)` holds for the manuscript's
own natural-dimension radical: the intersection of the kernels of all
homomorphisms `G → U(∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ))`. -/
def NormalKazhdanPrintedRadical : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (D : Subgroup G),
    D ≤ opToHSShadowResidual G →
    ∀ (K : Subgroup G) [K.Normal],
      HasKazhdanPropertyT.{0, 0} ↥K → K ≤ D →
        K ≤ manuscriptCoronaMFResidual G

/-- Closed proof of the normal-Kazhdan theorem at the printed radical. -/
theorem manuscriptNormalKazhdanPrintedRadical : NormalKazhdanPrintedRadical := by
  intro G _ _ D hD K _ hT hK
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact manuscriptNormalKazhdanRadical G D hD K hT hK

/-- **The closing sentence of the proof of `thm:normal-kazhdan`**: under the
hypotheses of that theorem, *every* corona homomorphism kills `K`.  The
dimension sequence is an arbitrary sequence of positive natural numbers, and
the conclusion is the containment of `K` in the kernel — the membership
`K ≤ Rad_MF(G)` with the radical's definition unfolded. -/
def NormalKazhdanCoronaVanishing : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (D : Subgroup G),
    D ≤ opToHSShadowResidual G →
    ∀ (K : Subgroup G) [K.Normal],
      HasKazhdanPropertyT.{0, 0} ↥K → K ≤ D →
      ∀ (d : ℕ → ℕ), ∀ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ Theta : G →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          K ≤ Theta.ker

/-- Closed proof that a normal Kazhdan subgroup of the shadow residual is
killed by every natural-dimension corona representation. -/
theorem manuscriptNormalKazhdanCoronaVanishing : NormalKazhdanCoronaVanishing := by
  intro G _ _ D hD K _ hT hK d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro Theta k hk
  have hinv : ManuscriptCoronaMFInvisible k :=
    mem_manuscriptCoronaMFResidual_iff.mp
      (manuscriptNormalKazhdanPrintedRadical G D hD K hT hK hk)
  have hone : Theta k = 1 := hinv d hd Theta
  exact MonoidHom.mem_ker.mpr hone

/-! ## The printed proof of Theorem~A, link by link -/

/-- **The proof of `thm:compression-criterion`, as the manuscript assembles
it.**  The four printed links, in printed order:

* every displayed generator `[ucu⁻¹, ℓ]`, with `u` a one-sided compressor of
  `L`, `c` a centralizing element and `ℓ ∈ L`, lies in `R_{∞→2}(G)`
  (`cor:defect-hs`);
* `R_{∞→2}(G)` is normal;
* therefore the normal closure `𝔇_G(L)` of those generators lies in
  `R_{∞→2}(G)`;
* therefore `thm:normal-kazhdan` puts every normal property-`(T)` subgroup of
  `𝔇_G(L)` inside the printed radical `Rad_MF(G)`.

The defect is the exact printed one, `printedDefect`, whose generating set is
indexed by the compressor *set* `Comp_G(L)`. -/
def PrintedCriterionAssembly : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      (∀ u ∈ compressionSet L, ∀ c : G, (∀ x ∈ L, Commute c x) →
          ∀ ℓ ∈ L, ⁅u * c * u⁻¹, ℓ⁆ ∈ opToHSShadowResidual G) ∧
        (opToHSShadowResidual G).Normal ∧
        printedDefect L ≤ opToHSShadowResidual G ∧
        (∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
          K ≤ printedDefect L → K ≤ manuscriptCoronaMFResidual G)

/-- Closed proof of the printed assembly of Theorem~A. -/
theorem manuscriptPrintedCriterionAssembly : PrintedCriterionAssembly := by
  intro G _ _ L hL
  have hgen : ∀ u ∈ compressionSet L, ∀ c : G, (∀ x ∈ L, Commute c x) →
      ∀ ℓ ∈ L, ⁅u * c * u⁻¹, ℓ⁆ ∈ opToHSShadowResidual G := by
    intro u hu c hc ℓ hℓ
    exact manuscriptCompressionDefectHSInvisible G L hL u
      (mem_compressionSet_iff.mp hu) c hc ℓ hℓ
  have hdef : printedDefect L ≤ opToHSShadowResidual G :=
    printedDefect_le_opToHSShadowResidual_direct (G := G) L hL
  refine ⟨hgen, opToHSShadowResidual_normal, hdef, ?_⟩
  intro K _ hK hKD
  exact manuscriptNormalKazhdanPrintedRadical G (printedDefect L) hdef K hK hKD

/-- **Theorem~A in its most concrete printed form.**  A normal property-`(T)`
subgroup of the printed defect `𝔇_G(L)` of a property-`(T)` subgroup `L` is
killed by every homomorphism of `G` into the unitary group of every
natural-dimension norm-matrix corona.  This is the printed assembly followed
by the unfolded conclusion of `thm:normal-kazhdan`. -/
def PrintedDefectCoronaVanishing : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
    ∀ (K : Subgroup G) [K.Normal],
      HasKazhdanPropertyT.{0, 0} ↥K → K ≤ printedDefect L →
      ∀ (d : ℕ → ℕ), ∀ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ Theta : G →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          K ≤ Theta.ker

/-- Closed proof that the printed defect's normal Kazhdan subgroups are corona
invisible. -/
theorem manuscriptPrintedDefectCoronaVanishing : PrintedDefectCoronaVanishing := by
  intro G _ _ L hL K _ hK hKD d hd
  have hdef : printedDefect L ≤ opToHSShadowResidual G :=
    (manuscriptPrintedCriterionAssembly G L hL).2.2.1
  exact manuscriptNormalKazhdanCoronaVanishing G (printedDefect L) hdef K hK hKD d hd

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
