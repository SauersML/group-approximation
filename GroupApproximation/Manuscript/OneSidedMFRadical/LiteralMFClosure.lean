import GroupApproximation.Sofic.MFRelationClosure
import GroupApproximation.Sofic.RadicalFunctoriality

/-!
# The literal MF closure of a normal subgroup

`non_mf_groups_exist.tex`, Introduction: the paragraph beginning "More
generally, for `N ⊴ G` define its *MF closure* by", together with
Proposition `prop:mf-residual-calculus`.

The manuscript defines the MF closure of `N ⊴ G` as a literal intersection of
kernels,

`cl_MF^G(N) = ⋂ {ker f : N ≤ ker f, f : G → M, M MF}`,

the intersection ranging over *all* homomorphisms from `G` into *all* MF
groups.  The development, by contrast, defines the closure operator
`actualCoronaMFClosure` as the pullback `q_N⁻¹(Rad_MF(G/N))` of the radical of
the quotient.  This file supplies the printed object and reconciles the two.

The class of all MF groups is a proper class, so the intersection is taken
here over targets `M : Type` — that is, over MF groups in the *same* universe
as `G`.  This is exactly the manuscript's own reading, and it costs nothing:
the printed sentence immediately after the display is "The image of a corona
homomorphism from `G` is countable and is itself MF; conversely, every MF
target embeds in a norm matrix corona", so the intersection is already
realized on the countable images, and the countability and MF-ness of a corona
image are `CoronaImageNormalKazhdan.nk_02_countable_mf_image`.  Concretely, the
one target that computes the intersection is the quotient of `G` itself
(`literalMFClosure_bot`, `literalMFClosure_eq_actualCoronaMFClosure`), and the
argument for the reverse inclusion — compose an MF target's injective corona
representation with `f` — uses nothing about the size of the target, so it
applies verbatim to targets in any universe.  Enlarging the class of targets
therefore cannot shrink the intersection further.

Contents:

* `literalMFClosure` — the printed intersection;
* `mem_literalMFClosure_iff` and `literalMFClosure_normal` — the reusable
  membership/elimination API and normality instance for that intersection;
* `literalMFClosure_bot` — the printed identity `Rad_MF(G) = cl_MF^G(1)`;
* `literalMFClosure_eq_actualCoronaMFClosure` — the printed closure and the
  development's pullback closure are the same subgroup;
* `isCDEOperatorMF_quotient_iff_literalMFClosure_eq` — the printed criterion
  "`G/N` is MF precisely when `cl_MF^G(N) = N`";
* `manuscriptMFResidualCalculusLiteral` — `prop:mf-residual-calculus` as one
  closed `Prop`, with its closure clause read through the printed
  intersection.  It is the literal-closure strengthening of
  `manuscriptMFResidualCalculus`, which states the same proposition with the
  development's pullback closure.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

noncomputable section

/-- Quotients of countable groups are countable. -/
local instance literalQuotientCountable {G : Type} [Group G]
    (N : Subgroup G) [hN : N.Normal] [Countable G] : Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- The kernels intersected by the manuscript's MF closure of `N`: the kernels
of the homomorphisms from `G` into MF groups that kill `N`. -/
def LiteralMFKernels (G : Type) [Group G] (N : Subgroup G) : Set (Subgroup G) :=
  {K : Subgroup G | ∃ (M : Type) (_ : Group M) (_ : Countable M) (f : G →* M),
    IsCDEOperatorMF M ∧ N ≤ f.ker ∧ K = f.ker}

/-- **The manuscript's MF closure**, literally:
`cl_MF^G(N) = ⋂ {ker f : N ≤ ker f, f : G → M, M MF}`. -/
def literalMFClosure (G : Type) [Group G] (N : Subgroup G) : Subgroup G :=
  sInf (LiteralMFKernels G N)

variable {G : Type} [Group G]

theorem mem_literalMFKernels {N K : Subgroup G} :
    K ∈ LiteralMFKernels G N ↔
      ∃ (M : Type) (_ : Group M) (_ : Countable M) (f : G →* M),
        IsCDEOperatorMF M ∧ N ≤ f.ker ∧ K = f.ker :=
  Iff.rfl

/-- The closure is contained in each kernel it intersects. -/
theorem literalMFClosure_le {N K : Subgroup G} (h : K ∈ LiteralMFKernels G N) :
    literalMFClosure G N ≤ K :=
  sInf_le h

/-- To lie inside the closure it suffices to lie inside every kernel of an
MF-target homomorphism killing `N`. -/
theorem le_literalMFClosure {N A : Subgroup G}
    (h : ∀ K ∈ LiteralMFKernels G N, A ≤ K) :
    A ≤ literalMFClosure G N :=
  le_sInf h

/-- Semantic membership in the printed closure: `x` lies in `cl_MF^G(N)`
exactly when every homomorphism into an MF group that kills `N` kills `x`. -/
theorem mem_literalMFClosure_iff {N : Subgroup G} {x : G} :
    x ∈ literalMFClosure G N ↔
      ∀ (M : Type) (_ : Group M) (_ : Countable M) (f : G →* M),
        IsCDEOperatorMF M → N ≤ f.ker → f x = 1 := by
  constructor
  · intro hx M instM instC f hMF hNf
    have hmem : f.ker ∈ LiteralMFKernels G N :=
      mem_literalMFKernels.mpr ⟨M, instM, instC, f, hMF, hNf, rfl⟩
    exact MonoidHom.mem_ker.mp (literalMFClosure_le hmem hx)
  · intro h
    show x ∈ sInf (LiteralMFKernels G N)
    refine Subgroup.mem_sInf.mpr ?_
    intro K hK
    obtain ⟨M, instM, instC, f, hMF, hNf, rfl⟩ := mem_literalMFKernels.mp hK
    exact MonoidHom.mem_ker.mpr (h M instM instC f hMF hNf)

/-- An intersection of kernels is normal. -/
instance literalMFClosure_normal (N : Subgroup G) :
    (literalMFClosure G N).Normal := by
  constructor
  intro x hx g
  show g * x * g⁻¹ ∈ sInf (LiteralMFKernels G N)
  refine Subgroup.mem_sInf.mpr ?_
  intro K hK
  have hxK : x ∈ K := literalMFClosure_le hK hx
  obtain ⟨M, instM, _instC, f, _hMF, _hNf, rfl⟩ := mem_literalMFKernels.mp hK
  exact (MonoidHom.normal_ker f).conj_mem x hxK g

/-- **Every MF target kills the radical.**  The radical is therefore contained
in the printed closure of every normal subgroup. -/
theorem manuscriptCoronaMFResidual_le_of_mem_literalMFKernels
    {N K : Subgroup G} (h : K ∈ LiteralMFKernels G N) :
    manuscriptCoronaMFResidual G ≤ K := by
  obtain ⟨M, instM, instC, f, hMF, _hNf, rfl⟩ := mem_literalMFKernels.mp h
  intro x hx
  have hbot : manuscriptCoronaMFResidual M = ⊥ :=
    isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hMF
  have hmem : f x ∈ (manuscriptCoronaMFResidual G).map f :=
    Subgroup.mem_map_of_mem f hx
  have himg := map_manuscriptCoronaMFResidual_le f hmem
  rw [hbot] at himg
  exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp himg)

/-- The MF radical is contained in the printed closure of every subgroup. -/
theorem manuscriptCoronaMFResidual_le_literalMFClosure (N : Subgroup G) :
    manuscriptCoronaMFResidual G ≤ literalMFClosure G N :=
  le_literalMFClosure fun _ hK ↦
    manuscriptCoronaMFResidual_le_of_mem_literalMFKernels hK

/-- **The printed identity `Rad_MF(G) = cl_MF^G(1)`.**  One inclusion is that
every MF target kills the radical; the other is that the quotient of `G` by
its radical is itself a countable MF group whose quotient map has kernel
exactly the radical, so it is one of the targets being intersected. -/
theorem literalMFClosure_bot [Countable G] :
    literalMFClosure G ⊥ = manuscriptCoronaMFResidual G := by
  refine le_antisymm ?_ (manuscriptCoronaMFResidual_le_literalMFClosure ⊥)
  have hmem : manuscriptCoronaMFResidual G ∈ LiteralMFKernels G ⊥ :=
    mem_literalMFKernels.mpr
      ⟨G ⧸ manuscriptCoronaMFResidual G, inferInstance, inferInstance,
        QuotientGroup.mk' (manuscriptCoronaMFResidual G),
        manuscriptCoronaMFQuotient_isCDEOperatorMF, bot_le,
        (QuotientGroup.ker_mk' (manuscriptCoronaMFResidual G)).symm⟩
  exact literalMFClosure_le hmem

/-- **The printed closure is the development's closure.**  `≤` holds because
`G ⧸ cl(N)` is a countable MF group whose quotient map kills `N` and has
kernel `cl(N)`; `≥` holds because an injective corona representation of an MF
target `M` turns a homomorphism `G → M` killing `N` into a corona
representation of `G` killing `N`, and the development's closure is exactly
the set of elements killed by all such. -/
theorem literalMFClosure_eq_actualCoronaMFClosure [Countable G]
    (N : Subgroup G) [N.Normal] :
    literalMFClosure G N = actualCoronaMFClosure N := by
  refine le_antisymm ?_ ?_
  · have hker : N ≤ (QuotientGroup.mk' (actualCoronaMFClosure N)).ker := by
      rw [QuotientGroup.ker_mk']
      exact le_actualCoronaMFClosure N
    have hmem : actualCoronaMFClosure N ∈ LiteralMFKernels G N :=
      mem_literalMFKernels.mpr
        ⟨G ⧸ actualCoronaMFClosure N, inferInstance, inferInstance,
          QuotientGroup.mk' (actualCoronaMFClosure N),
          isCDEOperatorMF_quotient_actualCoronaMFClosure N, hker,
          (QuotientGroup.ker_mk' (actualCoronaMFClosure N)).symm⟩
    exact literalMFClosure_le hmem
  · refine le_literalMFClosure ?_
    intro K hK
    obtain ⟨M, instM, instC, f, hMF, hNf, rfl⟩ := mem_literalMFKernels.mp hK
    intro x hx
    rw [mem_actualCoronaMFClosure_iff] at hx
    obtain ⟨d, hd, -, rho, hrho⟩ := hMF
    have hX : ∀ n, 0 < Fintype.card (naturalFiniteModel (d n)) := by
      simpa using hd
    have hkill : ∀ y ∈ N, (rho.comp f) y = 1 := by
      intro y hy
      have hy1 : f y = 1 := MonoidHom.mem_ker.mp (hNf hy)
      rw [MonoidHom.comp_apply, hy1, map_one]
    have hone := hx (fun n ↦ naturalFiniteModel (d n)) hX (rho.comp f) hkill
    rw [MonoidHom.comp_apply] at hone
    exact MonoidHom.mem_ker.mpr (hrho (hone.trans (map_one rho).symm))

/-- The printed closure is the pullback of the printed radical of the
quotient. -/
theorem literalMFClosure_eq_comap [Countable G] (N : Subgroup G) [N.Normal] :
    literalMFClosure G N =
      (manuscriptCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  rw [literalMFClosure_eq_actualCoronaMFClosure N]
  show (actualCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N) =
    (manuscriptCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N)
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]

/-- **The printed closure criterion.**  "`G/N` is MF precisely when
`cl_MF^G(N) = N`." -/
theorem isCDEOperatorMF_quotient_iff_literalMFClosure_eq [Countable G]
    (N : Subgroup G) [N.Normal] :
    IsCDEOperatorMF (G ⧸ N) ↔ literalMFClosure G N = N := by
  rw [literalMFClosure_eq_actualCoronaMFClosure N]
  exact (actualCoronaMFClosure_eq_self_iff N).symm

/-! ## Manuscript wrappers -/

/-- Closed form of the Introduction's identity `Rad_MF(G) = cl_MF^G(1)`, with
`cl_MF^G` the printed intersection of kernels. -/
def LiteralMFRadicalIsClosureOfTrivial : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    manuscriptCoronaMFResidual G = literalMFClosure G ⊥

theorem manuscriptMFRadicalIsLiteralClosureOfTrivial :
    LiteralMFRadicalIsClosureOfTrivial := by
  intro G _ _
  exact (literalMFClosure_bot (G := G)).symm

/-- Closed form of the reconciliation: the manuscript's literal intersection of
MF-target kernels and the development's pullback closure operator are the same
subgroup, for every normal subgroup of every countable group. -/
def LiteralMFClosureIsQuotientPullback : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (N : Subgroup G) [N.Normal],
    literalMFClosure G N = actualCoronaMFClosure N ∧
      literalMFClosure G N =
        (manuscriptCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N)

theorem manuscriptLiteralMFClosureIsQuotientPullback :
    LiteralMFClosureIsQuotientPullback := by
  intro G _ _ N _
  exact ⟨literalMFClosure_eq_actualCoronaMFClosure N,
    literalMFClosure_eq_comap N⟩

/-- **Proposition `prop:mf-residual-calculus`, over the printed MF closure.**
The four printed clauses, in the printed order: `Rad_MF(G)` is fully
invariant — every endomorphism of `G` maps it into itself; the quotient
`G/Rad_MF(G)` is MF; `G/N` is MF exactly when `cl_MF^G(N) = N`, with
`cl_MF^G(N)` the printed intersection `⋂ {ker f : N ≤ ker f, f : G → M, M MF}`;
and `G` is MF exactly when its MF radical is trivial.

This is the literal-closure strengthening of
`OneSidedMFRadical.manuscriptMFResidualCalculus`, whose third clause is stated
with the development's pullback closure operator `actualCoronaMFClosure`; the
two closures agree by `literalMFClosure_eq_actualCoronaMFClosure`. -/
def LiteralMFResidualCalculus : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    RadicalFunctoriality.IsFullyInvariant (manuscriptCoronaMFResidual G) ∧
      IsCDEOperatorMF (G ⧸ manuscriptCoronaMFResidual G) ∧
      (∀ (N : Subgroup G) [N.Normal],
        (IsCDEOperatorMF (G ⧸ N) ↔ literalMFClosure G N = N)) ∧
      (IsCDEOperatorMF G ↔ manuscriptCoronaMFResidual G = ⊥)

/-- Closed proof of the manuscript's MF residual calculus, with its closure
clause read through the printed intersection of MF-target kernels. -/
theorem manuscriptMFResidualCalculusLiteral : LiteralMFResidualCalculus := by
  intro G _ _
  refine ⟨fun f ↦ map_manuscriptCoronaMFResidual_le f,
    manuscriptCoronaMFQuotient_isCDEOperatorMF, ?_,
    isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot⟩
  intro N _
  exact isCDEOperatorMF_quotient_iff_literalMFClosure_eq N

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
