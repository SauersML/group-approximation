import GroupApproximation.BooneHigman.Products.FinitePi
import GroupApproximation.BooneHigman.Products.ProductTree
import GroupApproximation.BooneHigman.Statement.API

/-!
# The product step of the Boone–Higman assembly

A group *embeds in a finitely presented self-similar group* when it embeds in a finitely presented
self-similar subgroup of `Aut(T_X)` for some finite alphabet `X` with at least two letters.  This
class is closed under embeddings, isomorphisms and finite direct products: the product of two
finitely presented self-similar groups acts self-similarly and faithfully on the product alphabet
(`Products.ProductTree`), and it is finitely presented (`Algebra.ProductFinitePresentation`).

Zaremsky (arXiv:2405.09722, Theorem 1.1) embeds every finitely presented self-similar group in a
finitely presented simple group.  The finitely generated metabelian case of the Boone–Higman
conjecture therefore follows from two named inputs:

* `FPSelfSimilarEnvelopeStatement`, Zaremsky's theorem;
* `MetabelianPiecesStatement`, the reduction of a finitely generated metabelian group to finitely
  many pieces, each embedding in a finitely presented self-similar group.

`finitelyGeneratedMetabelianStatement_of_pieces` combines them into T2, and
`finitelyPresentedMetabelianStatement_of_pieces` gives T1 (BBMZ, arXiv:2306.16356v3, Problem 5.3(7)).
Both endpoints are conditional on the two named inputs until the peer blocks discharge them.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Products

open Trees

/-- `G` embeds in a finitely presented self-similar subgroup of `Aut(T_X)`, for a finite alphabet
`X` with at least two letters. -/
def EmbedsInFPSelfSimilarGroup (G : Type*) [Group G] : Prop :=
  ∃ (X : Type) (_ : Finite X) (_ : Nontrivial X) (H : Subgroup (TreeAut X)),
    IsSelfSimilar H ∧ Group.IsFinitelyPresented H ∧ ∃ f : G →* H, Function.Injective f

variable {G K : Type*} [Group G] [Group K]

theorem EmbedsInFPSelfSimilarGroup.of_injective {f : K →* G} (hf : Function.Injective f)
    (h : EmbedsInFPSelfSimilarGroup G) : EmbedsInFPSelfSimilarGroup K := by
  obtain ⟨X, hX, hXn, H, hH, hHfp, g, hg⟩ := h
  exact ⟨X, hX, hXn, H, hH, hHfp, g.comp f, hg.comp hf⟩

theorem EmbedsInFPSelfSimilarGroup.of_mulEquiv (e : K ≃* G) (h : EmbedsInFPSelfSimilarGroup G) :
    EmbedsInFPSelfSimilarGroup K :=
  h.of_injective (f := e.toMonoidHom) e.injective

/-- A subsingleton group embeds in the trivial self-similar group of the binary tree. -/
theorem embedsInFPSelfSimilarGroup_of_subsingleton [Subsingleton G] :
    EmbedsInFPSelfSimilarGroup G := by
  haveI : Subsingleton (⊥ : Subgroup (TreeAut Bool)) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  haveI : Finite (⊥ : Subgroup (TreeAut Bool)) := Finite.of_subsingleton
  exact ⟨Bool, inferInstance, inferInstance, ⊥, isSelfSimilar_bot, inferInstance, 1,
    fun a b _ => Subsingleton.elim a b⟩

/-- **Finitely presented self-similar hosts are closed under direct products.** -/
theorem EmbedsInFPSelfSimilarGroup.prod (hG : EmbedsInFPSelfSimilarGroup G)
    (hK : EmbedsInFPSelfSimilarGroup K) : EmbedsInFPSelfSimilarGroup (G × K) := by
  obtain ⟨X, hX, hXn, H, hH, hHfp, f, hf⟩ := hG
  obtain ⟨Y, hY, hYn, L, hL, hLfp, g, hg⟩ := hK
  haveI : Group.IsFinitelyPresented ((H.prod L).map prodHom) :=
    Group.IsFinitelyPresented.equiv (mapProdHomEquiv H L)
  refine ⟨X × Y, inferInstance, nontrivial_prod_left, (H.prod L).map prodHom,
    isSelfSimilar_map_prodHom hH hL, inferInstance,
    (mapProdHomEquiv H L).toMonoidHom.comp (f.prodMap g), ?_⟩
  exact (mapProdHomEquiv H L).injective.comp (hf.prodMap hg)

/-- **Finitely presented self-similar hosts are closed under finite direct products.** -/
theorem embedsInFPSelfSimilarGroup_pi_fin (n : ℕ) (P : Fin n → Type*) [∀ i, Group (P i)]
    (hP : ∀ i, EmbedsInFPSelfSimilarGroup (P i)) : EmbedsInFPSelfSimilarGroup (∀ i, P i) := by
  induction n with
  | zero =>
    haveI : Unique (∀ i : Fin 0, P i) := Pi.uniqueOfIsEmpty P
    exact embedsInFPSelfSimilarGroup_of_subsingleton
  | succ n ih =>
    exact ((hP 0).prod (ih (fun i => P i.succ) fun i => hP i.succ)).of_mulEquiv
      (piFinSuccMulEquiv P)

/-- **Zaremsky's envelope theorem** (arXiv:2405.09722, Theorem 1.1) as a named statement: every
finitely presented self-similar group embeds in a finitely presented simple group. -/
def FPSelfSimilarEnvelopeStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H → EmbedsInFinitelyPresentedSimpleGroup H

/-- **The metabelian reduction** as a named statement: every finitely generated metabelian group
embeds in a finite direct product of groups, each embedding in a finitely presented self-similar
group. -/
def MetabelianPiecesStatement : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
    ∃ (n : ℕ) (P : Fin n → Type) (_ : ∀ i, Group (P i)),
      (∀ i, EmbedsInFPSelfSimilarGroup (P i)) ∧ ∃ f : G →* ∀ i, P i, Function.Injective f

theorem EmbedsInFPSelfSimilarGroup.embedsInFinitelyPresentedSimpleGroup
    (henv : FPSelfSimilarEnvelopeStatement) (h : EmbedsInFPSelfSimilarGroup G) :
    EmbedsInFinitelyPresentedSimpleGroup G := by
  obtain ⟨X, hX, hXn, H, hH, hHfp, f, hf⟩ := h
  exact (henv X H hH hHfp).of_injective hf

/-- **T2 from the two named inputs**: every finitely generated metabelian group embeds in a finitely
presented simple group. -/
theorem finitelyGeneratedMetabelianStatement_of_pieces (hpieces : MetabelianPiecesStatement)
    (henv : FPSelfSimilarEnvelopeStatement) : FinitelyGeneratedMetabelianStatement := by
  intro G _ hfg hmeta
  obtain ⟨n, P, _, hP, f, hf⟩ := hpieces G hfg hmeta
  exact ((embedsInFPSelfSimilarGroup_pi_fin n P hP).embedsInFinitelyPresentedSimpleGroup
    henv).of_injective hf

/-- **T1 from the two named inputs** (BBMZ, arXiv:2306.16356v3, Problem 5.3(7)). -/
theorem finitelyPresentedMetabelianStatement_of_pieces (hpieces : MetabelianPiecesStatement)
    (henv : FPSelfSimilarEnvelopeStatement) : FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_of_finitelyGenerated
    (finitelyGeneratedMetabelianStatement_of_pieces hpieces henv)

end Products
end BooneHigman
end GroupApproximation
