import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.PreusserAssembly
import GroupApproximation.Leavitt.ExchangeRefinement
import GroupApproximation.Leavitt.ExchangePrerequisite
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.PropertyTT.RingHypotheses

/-!
# Sentence-level closure of Proposition `prop:simple`'s printed proof

`RankTwelveSimplicity.manuscriptPropositionSimple` proves Proposition
`prop:simple` (`H = EL₁₂(L_{𝔽₂}(1,2))` is nontrivial and simple) by the
independent direct root-extraction route, not by literally running the
printed proof (which quotes Preusser's sandwich theorem and computes the
centre of `GL₁₂(R)`).  This file closes the census gap at sentence
granularity: one declaration per printed proof sentence of `prop:simple`,
each stated literally and proved from the modules that already carry the
printed route unconditionally --
`GroupApproximation.CongruenceSubgroups` (the relative elementary group, the
congruence subgroup, the canonical level ideal, and the two-step centre
computation) and `GroupApproximation.PreusserAssembly` (Preusser's
Proposition 21 and the resulting sandwich theorem, both discharged from the
row-annihilator and exchange-refinement calculus rather than assumed).

No sentence below needs a `sorry`.  Where the printed sentence's own
justification is a literature citation (Abrams--Aranda, Ara), the repository
already proves a stronger unconditional replacement for exactly the
consequence the rest of the proof consumes, and that replacement is wrapped
here instead of re-asserting the citation as an open leaf; see the docstring
of `sentence_53445fb2a2b7` for the precise correspondence.

## Sentence keys

The declaration names below are the eight-hex-digit row keys of the
sentence census for `prop:simple`, in printed order:
`53445fb2a2b7`, `9a336208aafb`, `037bb76b5bc8`, `043a7f66a451`,
`c4b21eeb6062`, `d08bc8e9df43`, `96a6b3084ea5`, `68d3bd1ddf86`,
`4fd7b1d5f07b`, `c74b4284484e`, `9e719f10dc89`, `4b5ccef4a04e`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

/-! ### Sentence `53445fb2a2b7`

"The ring $R$ is purely infinite simple~\cite{AbramsAranda}, and so is an
exchange ring~\cite{AraExchange}." -/

/-- **Sentence `53445fb2a2b7`** (`prop:simple`, proof, first sentence).
"The ring $R$ is purely infinite simple, and so is an exchange ring."

Both citations are literature inputs the printed proof does not itself
reprove.  The repository's own convention (see the docstring of
`HasSingleSandwichDivision` in `PropertyTT.RingHypotheses`) is to name the
*exact algebraic property used by the proof* rather than introduce a
competing formal definition of "purely infinite": for a unital simple ring,
single-sandwich division (every nonzero element $a$ admits $xay=1$) is the
standard Ara--Goodearl--Pardo operative reading of pure infiniteness, and it
is what is proved here, unconditionally, for `R`.  Likewise "exchange ring"
is formalized by Nicholson's one-element criterion
`ExchangePrerequisite.HasRightExchange`, also proved unconditionally for `R`
from the same sandwich-division witness, independently of Ara's cited
implication from pure infiniteness.  Simplicity of `R` is the further,
separately proved, consequence that the rest of the printed proof actually
consumes. -/
theorem sentence_53445fb2a2b7 :
    HasSingleSandwichDivision R ∧ IsSimpleRing R ∧
      ExchangePrerequisite.HasRightExchange R :=
  ⟨coefficientRing_hasSingleSandwichDivision, coefficientRing_isSimple,
    BinaryLeavitt.hasRightExchange (ZMod 2)⟩

/-- **Sentence `9a336208aafb`**.  "Since $H=\EL_{12}(R)$, the subgroup
$N\le\GL_{12}(R)$ is normalized by $\EL_{12}(R)$."  Stated for the image of
a normal subgroup `N ⊴ H` inside `GL₁₂(R)` under the canonical inclusion:
every element of `EL₁₂(R) = H` conjugates that image back into itself. -/
theorem sentence_9a336208aafb
    (N : Subgroup H) (hN : N.Normal) :
    ∀ g : elementaryGroup (Fin 12) R, ∀ x ∈ N.map (elementaryGroup (Fin 12) R).subtype,
      (elementaryGroup (Fin 12) R).subtype g * x *
          ((elementaryGroup (Fin 12) R).subtype g)⁻¹
        ∈ N.map (elementaryGroup (Fin 12) R).subtype := by
  rintro g x ⟨n, hn, rfl⟩
  exact ⟨g * n * g⁻¹, hN.conj_mem n hn g, by simp [map_mul, map_inv]⟩

/-- **Sentence `037bb76b5bc8`**.  "Preusser's sandwich theorem~\cite[Theorem
3]{Preusser} provides an ideal $I\trianglelefteq R$ such that
$\EL_{12}(R,I)\le N\le C_{12}(R,I)$."

This is the manuscript's single named citation to Preusser, and it is *not*
taken as a literature input here: `PreusserAssembly.preusser_sandwich`
discharges it unconditionally at the binary Leavitt algebra, from Preusser's
Proposition 20 (row-annihilator transvections) and Proposition 21 (promoted
by the finite exchange refinement), both proved in the tree. -/
theorem sentence_037bb76b5bc8
    (N : Subgroup H) (hN : N.Normal) :
    ∃ I : TwoSidedIdeal R, relativeElementary (Fin 12) I ≤ N ∧
      N.map (elementaryGroup (Fin 12) R).subtype ≤ congruenceSubgroup (Fin 12) I :=
  PreusserAssembly.preusser_sandwich (by norm_num : 3 ≤ Fintype.card (Fin 12))
    (BinaryLeavitt.hasFiniteRightExchangePartitions (ZMod 2)) N hN

/-- **Sentence `043a7f66a451`**.  "Simplicity of $R$ gives $I=0$ or $I=R$." -/
theorem sentence_043a7f66a451 (I : TwoSidedIdeal R) : I = ⊥ ∨ I = ⊤ := by
  haveI := coefficientRing_isSimple
  exact IsSimpleOrder.eq_bot_or_eq_top I

/-- **Sentence `c4b21eeb6062`**.  "If $I=R$, then $\EL_{12}(R,I)=H$, so
$N=H$." -/
theorem sentence_c4b21eeb6062
    (N : Subgroup H)
    (hIle : relativeElementary (Fin 12) (⊤ : TwoSidedIdeal R) ≤ N) :
    relativeElementary (Fin 12) (⊤ : TwoSidedIdeal R) = ⊤ ∧ N = ⊤ := by
  refine ⟨relativeElementary_top, ?_⟩
  rw [relativeElementary_top] at hIle
  exact top_le_iff.mp hIle

/-- **Sentence `d08bc8e9df43`**.  "Suppose that $I=0$."  This names the
hypothesis every remaining sentence of the proof consumes; the trivial ideal
is a legitimate instance. -/
theorem sentence_d08bc8e9df43 : ∃ I : TwoSidedIdeal R, I = ⊥ := ⟨⊥, rfl⟩

/-- **Sentence `96a6b3084ea5`**.  "Then $N\le C_{12}(R,0)=Z(\GL_{12}(R))$." -/
theorem sentence_96a6b3084ea5
    (N : Subgroup H)
    (hIcong : N.map (elementaryGroup (Fin 12) R).subtype
      ≤ congruenceSubgroup (Fin 12) (⊥ : TwoSidedIdeal R)) :
    N.map (elementaryGroup (Fin 12) R).subtype
        ≤ Subgroup.center (Matrix (Fin 12) (Fin 12) R)ˣ ∧
      congruenceSubgroup (Fin 12) (⊥ : TwoSidedIdeal R)
        = Subgroup.center (Matrix (Fin 12) (Fin 12) R)ˣ := by
  have hcb : congruenceSubgroup (Fin 12) (⊥ : TwoSidedIdeal R)
      = Subgroup.center (Matrix (Fin 12) (Fin 12) R)ˣ :=
    congruenceSubgroup_bot (ι := Fin 12) (R := R)
      (by norm_num : 1 < Fintype.card (Fin 12)) (0 : Fin 12)
  refine ⟨?_, hcb⟩
  rw [← hcb]
  exact hIcong

/-- **Sentence `68d3bd1ddf86`**.  "Fix $g\in N$." -/
theorem sentence_68d3bd1ddf86 (N : Subgroup H) :
    ∃ g : (Matrix (Fin 12) (Fin 12) R)ˣ,
      g ∈ N.map (elementaryGroup (Fin 12) R).subtype :=
  ⟨1, Subgroup.one_mem _⟩

/-- **Sentence `4fd7b1d5f07b`**.  "Since $g$ centralizes $e_{ij}(1)$ for
every $i\ne j$, comparison of entries in $gE_{ij}=E_{ij}g$ shows that
$g=\lambda I_{12}$ for some $\lambda\in R^\times$." -/
theorem sentence_4fd7b1d5f07b
    (g : (Matrix (Fin 12) (Fin 12) R)ˣ)
    (hg : ∀ (i j : Fin 12) (hij : i ≠ j),
      (g : Matrix (Fin 12) (Fin 12) R) *
          (elementaryUnit i j hij (1 : R) : Matrix (Fin 12) (Fin 12) R)
        = (elementaryUnit i j hij (1 : R) : Matrix (Fin 12) (Fin 12) R) *
            (g : Matrix (Fin 12) (Fin 12) R)) :
    ∃ u : Rˣ,
      (g : Matrix (Fin 12) (Fin 12) R) = Matrix.diagonal fun _ ↦ (u : R) := by
  have hg' : ∀ (i j : Fin 12) (hij : i ≠ j),
      (g : Matrix (Fin 12) (Fin 12) R) * Matrix.single i j (1 : R)
        = Matrix.single i j (1 : R) * (g : Matrix (Fin 12) (Fin 12) R) := by
    intro i j hij
    have h := hg i j hij
    have hval : (elementaryUnit i j hij (1 : R) : Matrix (Fin 12) (Fin 12) R)
        = 1 + Matrix.single i j (1 : R) := rfl
    rw [hval, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  have hdiag : (g : Matrix (Fin 12) (Fin 12) R)
      = Matrix.diagonal fun _ ↦ (g : Matrix (Fin 12) (Fin 12) R) 0 0 :=
    eq_diagonal_of_commute_single (ι := Fin 12)
      (by norm_num : 1 < Fintype.card (Fin 12)) 0 _ hg'
  have h1 : (g : Matrix (Fin 12) (Fin 12) R) 0 0 *
      ((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R) 0 0 = 1 := by
    have hone : Matrix.diagonal (fun _ : Fin 12 ↦ (g : Matrix (Fin 12) (Fin 12) R) 0 0) *
        ((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R) = 1 := by
      rw [← hdiag]
      exact g.mul_inv
    have h : (Matrix.diagonal (fun _ : Fin 12 ↦ (g : Matrix (Fin 12) (Fin 12) R) 0 0) *
        ((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R)) 0 0
        = (1 : Matrix (Fin 12) (Fin 12) R) 0 0 := by rw [hone]
    rwa [Matrix.diagonal_mul, Matrix.one_apply_eq] at h
  have h2 : ((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R) 0 0 *
      (g : Matrix (Fin 12) (Fin 12) R) 0 0 = 1 := by
    have htwo : ((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R) *
        Matrix.diagonal (fun _ : Fin 12 ↦ (g : Matrix (Fin 12) (Fin 12) R) 0 0) = 1 := by
      rw [← hdiag]
      exact g.inv_mul
    have h : (((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R) *
        Matrix.diagonal (fun _ : Fin 12 ↦ (g : Matrix (Fin 12) (Fin 12) R) 0 0)) 0 0
        = (1 : Matrix (Fin 12) (Fin 12) R) 0 0 := by rw [htwo]
    rwa [Matrix.mul_diagonal, Matrix.one_apply_eq] at h
  exact ⟨⟨(g : Matrix (Fin 12) (Fin 12) R) 0 0,
      ((g⁻¹ : (Matrix (Fin 12) (Fin 12) R)ˣ) : Matrix (Fin 12) (Fin 12) R) 0 0, h1, h2⟩,
    hdiag⟩

/-- **Sentence `c74b4284484e`**.  "Centralizing $e_{ij}(a)$ now gives
$\lambda a=a\lambda$ for every $a\in R$, and so $\lambda\in Z(R)^\times$." -/
theorem sentence_c74b4284484e
    (u : Rˣ)
    (hg : ∀ (i j : Fin 12) (hij : i ≠ j) (a : R),
      (Matrix.diagonal fun _ : Fin 12 ↦ (u : R)) *
          (elementaryUnit i j hij a : Matrix (Fin 12) (Fin 12) R)
        = (elementaryUnit i j hij a : Matrix (Fin 12) (Fin 12) R) *
            (Matrix.diagonal fun _ : Fin 12 ↦ (u : R))) :
    (∀ x : R, (u : R) * x = x * (u : R)) := by
  have hg' : ∀ (i j : Fin 12) (a : R), i ≠ j →
      (Matrix.diagonal fun _ : Fin 12 ↦ (u : R)) * Matrix.single i j a
        = Matrix.single i j a * (Matrix.diagonal fun _ : Fin 12 ↦ (u : R)) := by
    intro i j a hij
    have h := hg i j hij a
    have hval : (elementaryUnit i j hij a : Matrix (Fin 12) (Fin 12) R)
        = 1 + Matrix.single i j a := rfl
    rw [hval, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  exact commute_of_commute_single (ι := Fin 12)
    (by norm_num : 1 < Fintype.card (Fin 12)) (u : R) hg'

/-- **Sentence `9e719f10dc89`**.  "Since $Z(R)=\F_2$~\cite[Corollary
4.3]{ArandaCrow}, we have $g=1$."

`Z(R)=\F_2` is the literature citation; the operative consequence the proof
uses is that every central unit of `R` is trivial
(`BinaryLeavitt.central_units_trivial`), which is proved unconditionally in
the tree from the same centre computation. -/
theorem sentence_9e719f10dc89
    (g : (Matrix (Fin 12) (Fin 12) R)ˣ) (u : Rˣ)
    (hdiag : (g : Matrix (Fin 12) (Fin 12) R) = Matrix.diagonal fun _ ↦ (u : R))
    (hcentral : ∀ x : R, (u : R) * x = x * (u : R)) :
    g = 1 := by
  have hu1 : u = 1 := BinaryLeavitt.central_units_trivial u hcentral
  simp only [hu1, Units.val_one] at hdiag
  apply Units.ext
  rw [hdiag, Matrix.diagonal_one, Units.val_one]

/-- **Sentence `4b5ccef4a04e`**.  "Thus $N=1$." -/
theorem sentence_4b5ccef4a04e
    (N : Subgroup H)
    (hall : ∀ g ∈ N.map (elementaryGroup (Fin 12) R).subtype, g = 1) :
    N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxmap : (elementaryGroup (Fin 12) R).subtype x
      ∈ N.map (elementaryGroup (Fin 12) R).subtype := ⟨x, hx, rfl⟩
  have hxone : (elementaryGroup (Fin 12) R).subtype x = 1 := hall _ hxmap
  exact (elementaryGroup (Fin 12) R).subtype_injective hxone

end OneSidedMFRadical
end Manuscript
end GroupApproximation
