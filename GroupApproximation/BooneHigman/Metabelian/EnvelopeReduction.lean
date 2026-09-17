import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreath
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import GroupApproximation.BooneHigman.Products.Assembly
import GroupApproximation.Algebra.FreeGroupFiniteRank
import Mathlib.GroupTheory.Index
import GroupApproximation.Meta.AxiomGuard

/-!
# Zaremsky's envelope, reduced to four facts about Röver–Nekrashevych groups

`Products.FPSelfSimilarEnvelopeStatement` is Zaremsky's theorem (arXiv:2405.09722, Theorem 1.1):
a finitely presented self-similar group `H ≤ Aut(T_X)` embeds in a finitely presented simple
group.  Zaremsky's simple group is `S = [V, V]` for the Röver–Nekrashevych group
`V = V_Y(K)` of a regrouped copy `K ≅ H` acting on the alphabet `Y = Fin m × X`, `m` even.

Route of Zaremsky's proof, and what this lane proves.

1. `H ↪ K ↪ V_Y(K)`.  The second map is `rnEmbedding`, proved here (faithfulness of the action of
   a tree automorphism on the Cantor set, `cantorHom_injective`).
2. `V_Y(K)` is finitely presented (Scott; Skipper–Witzel–Zaremsky), `[V, V]` has finite index
   (the abelianisation is finite after regrouping), and `[V, V]` is simple (Nekrashevych,
   Theorem 4.7).  NOT proved here.
3. `S = [V, V]` is finitely presented: a finite-index subgroup of a finitely presented group.
   Proved here from `FiniteIndex.isFinitelyPresented_subgroup_of_finiteIndex'`.
4. `V ↪ S ≀ (V ⧸ S)` (Kaloujnine–Krasner).  Proved here, `exists_injective_regularWreath`.
5. `S ≀ (V ⧸ S) ↪ S` (Zaremsky, Proposition 2.5).  NOT proved here.

`RoverNekrashevychEnvelopeStatement` packages exactly the unproved facts (2) and (5) about the
concrete group `roverNekrashevych Y K`, and
`fpSelfSimilarEnvelope_of_rnEnvelope` assembles (1)–(5).

*Strictly smaller proof content.*  The statement fixes the envelope to be the concrete
commutator subgroup of the concrete group `roverNekrashevych Y K`, so the remaining work
contains none of steps (1), (3), (4): the faithful Cantor action and `H ↪ V`, finite
presentability of `S`, and the wreath embedding `V ↪ S ≀ (V ⧸ S)` are discharged.  It also asks
for an embedding of one regular wreath product into `S`, not for simplicity or finite
presentation of any group other than `V_Y(K)` and `[V_Y(K), V_Y(K)]`.

*Truth.*  Take `Y = Fin m × X` with `m ≥ 2` even and let `K` be `H` acting on the `X`-coordinates
of words over `Y`; `K` is self-similar and finitely presented, and `e : H ≅ K`.  For
self-similar `K` the group `roverNekrashevych Y K` is the Röver–Nekrashevych group `V_Y(K)`,
which is finitely presented when `K` is (Zaremsky, Section 3).  Nekrashevych's theorem gives
simplicity of `[V, V]`.  Every localised `k` splits over the `m · |X|` children of its cone
into localised states, each state repeated `m` times, so the abelianisation `A` of `V` satisfies
`A = m A + (image of V_Y^ab)`; `A` is finitely generated and `V_Y^ab` is finite, hence `A` is
finite.  Proposition 2.5 embeds `S^F ⋊ F` in `S` for any finite `F`: choose `2 |F|` disjoint
cones, put the `F`-coordinates on the first `|F|` of them, and let `F` permute the cones by its
regular action doubled on both halves, which is an even permutation of cones and hence lies
in `[V, V]`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **The Röver–Nekrashevych input to Zaremsky's envelope.**  Every finitely presented
self-similar `H ≤ TreeAut X` embeds in some `K ≤ TreeAut Y` whose Röver–Nekrashevych group
`V = roverNekrashevych Y K` is finitely presented, with `[V, V]` simple and of finite index, and
with `[V, V] ≀ (V ⧸ [V, V])` embedding in `[V, V]`. -/
def RoverNekrashevychEnvelopeStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H →
      ∃ (Y : Type) (_ : Finite Y) (_ : Nontrivial Y) (K : Subgroup (TreeAut Y))
        (e : ↥H →* ↥K), Function.Injective e ∧
        Group.IsFinitelyPresented ↥(roverNekrashevych Y K) ∧
        (commutator ↥(roverNekrashevych Y K)).FiniteIndex ∧
        IsSimpleGroup ↥(commutator ↥(roverNekrashevych Y K)) ∧
        ∃ j : RegularWreath ↥(commutator ↥(roverNekrashevych Y K))
            (↥(roverNekrashevych Y K) ⧸ commutator ↥(roverNekrashevych Y K)) →*
              ↥(commutator ↥(roverNekrashevych Y K)),
          Function.Injective j

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RoverNekrashevychEnvelopeStatement

/-- Zaremsky's envelope from the Röver–Nekrashevych input: the finitely presented simple group
is `[V, V]`, and `H ↪ K ↪ V ↪ [V, V] ≀ (V ⧸ [V, V]) ↪ [V, V]`. -/
theorem fpSelfSimilarEnvelope_of_rnEnvelope
    (hRN : RoverNekrashevychEnvelopeStatement) : Products.FPSelfSimilarEnvelopeStatement := by
  intro X _ _ H hH hfp
  obtain ⟨Y, _, _, K, e, he, hV, _, hsimple, j, hj⟩ := hRN X H hH hfp
  obtain ⟨φ, hφ⟩ := exists_injective_regularWreath (commutator ↥(roverNekrashevych Y K))
  have hS : Group.IsFinitelyPresented ↥(commutator ↥(roverNekrashevych Y K)) :=
    GroupApproximation.FiniteIndex.isFinitelyPresented_subgroup_of_finiteIndex'
      (commutator ↥(roverNekrashevych Y K)) hV
  refine ⟨↥(commutator ↥(roverNekrashevych Y K)), inferInstance, hS, hsimple,
    j.comp (φ.comp ((rnEmbedding K).comp e)), ?_⟩
  exact hj.comp (hφ.comp ((rnEmbedding_injective K).comp he))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.fpSelfSimilarEnvelope_of_rnEnvelope

end GroupApproximation.BooneHigman.Metabelian.Envelope
