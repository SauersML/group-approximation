import GroupApproximation.Higman.RopeTrick
import GroupApproximation.Higman.Program

/-!
# Higman's embedding theorem, assembled

With the rope trick proved (`Higman.fpOvergroup_of_benign`), Higman's
embedding theorem for finitely generated groups is exactly one statement away:
that a normal subgroup of a free group of finite rank whose set of words is
recursively enumerable is benign.  That statement is Higman's Sections 2--4 --
the sequence space `E`, the Higman operations, and the closure of the benign
family under them -- and it is carried here as the single input
`REBenign`.

    Higman's embedding theorem  =  REBenign  +  the rope trick.

Everything on the right except `REBenign` is proved in this repository.

## The shape of the input

`REBenign` is stated for the free group on `Fin (n+1)` and a normal subgroup
`N`, with "recursively enumerable" spelled through the same raw words the
repository's computability layer uses: a raw word is a list of signed
generator indices, indices are read modulo the alphabet size, and the
hypothesis is that the set of raw words landing in `N` is `REPred`.

That is the exact hypothesis Higman's Theorem 4 discharges, and it is the
only thing between this repository and the theorem.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes

/-! ## 1.  Raw words in a free group of finite rank -/

/-- Reading a raw word in the free group on `Fin (n+1)`: indices are taken
modulo the alphabet size, exactly as `Computability.PresentationCodes.wordOf`
does. -/
def rawToFree (n : ℕ) (v : RawWord) : FreeGroup (Fin (n + 1)) :=
  FreeGroup.mk (v.map fun p => (⟨p.1 % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩, p.2))

/-- A finitely generated group with a recursive presentation, in the form
Higman's theorem consumes: a surjection from a free group of finite rank
whose kernel is recursively enumerable as a set of raw words. -/
structure FGRecursive (G : Type) [Group G] where
  /-- The number of generators, offset by one so the alphabet is nonempty. -/
  rank : ℕ
  /-- The presentation map. -/
  π : FreeGroup (Fin (rank + 1)) →* G
  /-- It is onto. -/
  π_surjective : Function.Surjective π
  /-- Its kernel is recursively enumerable. -/
  re : REPred (fun v : RawWord => π (rawToFree rank v) = 1)

/-! ## 2.  The input -/

/-- **Higman's Sections 2--4, as one statement.**  A normal subgroup of a
finitely generated free group whose word set is recursively enumerable is
benign.

**Nothing inhabits this structure.**  Its content is Higman's characterization
of recursively enumerable sets by the operations `(H)` together with the
closure of the benign family under them.  What the repository has of that
argument:

* Lemma 3.2 and half of Lemma 3.3 (`Higman.Benign`, `Higman.BenignJoin`,
  `Higman.BenignClosure`, `Higman.BenignAmbient`);
* the first concrete benign subgroup, and that its generators are a free basis
  (`Higman.Row.benign_row`, `Higman.Row.basisHom_injective`);
* the coding of the sequence space and that it is faithful
  (`Higman.Seq.aElt_injective`, through `Higman.Conj.cbHom_injective`);
* three of the nine Higman operations: `ι` and `υ`
  (`Higman.Seq.benign_ASub_inter`, `benign_ASub_union`) and `σ`
  (`Higman.Seq.benign_ASub_sigmaOp`).

What is missing is the other six operations --- `ρ, τ, θ, ζ, π, ωₘ` --- and
Higman's Section 2, that a set of sequences is recursively enumerable exactly
when it is built from `Z` and `S` by them. -/
structure REBenign where
  /-- Recursively enumerable normal subgroups of free groups of finite rank
  are benign. -/
  benign : ∀ (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))), N.Normal →
    REPred (fun v : RawWord => rawToFree n v ∈ N) → Benign N

/-! ## 3.  Transport of finitely presented overgroups -/

/-- A finitely presented overgroup transports along an isomorphism. -/
def FPOvergroup.congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (u : FPOvergroup G) : FPOvergroup H where
  K := u.K
  emb := u.emb.comp e.symm.toMonoidHom
  emb_injective := u.emb_injective.comp e.symm.injective

/-! ## 4.  The theorem -/

/-- **Higman's embedding theorem, from its one remaining input.**  A finitely
generated group with a recursive presentation embeds in a finitely presented
group.

The proof is: the kernel of the presentation map is recursively enumerable, so
benign by the input; the rope trick turns a benign normal subgroup into an
embedding of the quotient; and the quotient is the group. -/
theorem fpOvergroup_of_fgRecursive (h : REBenign) {G : Type} [Group G]
    (p : FGRecursive G) : Nonempty (FPOvergroup G) := by
  classical
  set F := FreeGroup (Fin (p.rank + 1)) with hF
  set N : Subgroup F := MonoidHom.ker p.π with hN
  have hre : REPred (fun v : RawWord => rawToFree p.rank v ∈ N) := by
    have hiff : (fun v : RawWord => rawToFree p.rank v ∈ N)
        = (fun v : RawWord => p.π (rawToFree p.rank v) = 1) := by
      funext v
      exact propext ⟨fun hv => MonoidHom.mem_ker.mp hv,
        fun hv => MonoidHom.mem_ker.mpr hv⟩
    rw [hiff]
    exact p.re
  have hben : Benign N := h.benign p.rank N (MonoidHom.normal_ker p.π) hre
  letI : Group.FG F := ProductFinitePresentation.fg_of_isFinitelyPresented F
  obtain ⟨u⟩ := fpOvergroup_of_benign hben
  exact ⟨FPOvergroup.congr
    (QuotientGroup.quotientKerEquivOfSurjective p.π p.π_surjective) u⟩

end Higman
end GroupApproximation
