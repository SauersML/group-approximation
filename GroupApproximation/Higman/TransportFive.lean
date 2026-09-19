import GroupApproximation.Higman.TransportFiveCoding
import GroupApproximation.Higman.TransportFivePeriodicKernel

/-!
# Higman's Section 5: transport assembly

The coding and exact decoder-kernel completion live in
`TransportFiveCoding.lean`; benignness of the fixed periodic row kernel lives
in `TransportFivePeriodicKernel.lean`.  This module names the two independent
leaves and assembles them into `Higman.TransportSectionFive`.
-/

namespace GroupApproximation
namespace Higman
namespace Transport

/-- **Leaf 1 (computability).**  The code set of a recursively enumerable normal
subgroup is recursively enumerable.

The code of a raw word is a primitive-recursive function of it ---
`Transport.codeSeq` is a fold --- and membership in the code set is the
projection of "some raw word in `N` codes to this sequence".  The work is the
normalization of a code list to the sequence it names, since a sequence has many
list representations.  `Higman.exists_primrec_of_rePred` and
`Computability.WordProblemRE.rePred_exists_eq_true` are the two ends of it.

**Nothing inhabits this structure.** -/
structure CodeRE where
  /-- Code sets of recursively enumerable subgroups are recursively enumerable. -/
  code_re : ∀ (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))),
    REPred (fun v : RawWord => rawToFree n v ∈ N) → REset (codeSet n N)

/-- **Leaf 2, the content of Section 5: un-conjugation.**  Higman's Theorem 4
delivers benignness of `⟨a^{b_f} : f ∈ B⟩`; the transport needs
`⟨b_f : f ∈ B⟩` to be benign.

Nothing in the proved calculus relates the two.  The map `a^{b_f} ↦ b_f` is not
injective, so `BenignWitness.mapEmb` does not apply, and it is not the
restriction of an endomorphism of `F₃`: an endomorphism fixing `b` and `c` sends
`a^{b_f}` to `(b_f)⁻¹ φ(a) (b_f)`, and no single `φ(a)` gives `b_f` for every
`f`.  See the memo for the four refuted routes and the two that survive.

**Nothing inhabits this structure.** -/
structure UnConjugation where
  /-- Benignness passes from the conjugated code family to the code family. -/
  unconj : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
    BenignTF (Subgroup.closure (Seq.bElt '' B))

/-- A free group of finite rank is a torsion-free finitely presented overgroup of
itself. -/
def freeTFOvergroup (n : ℕ) : TorsionFreeFPOvergroup (FreeGroup (Fin (n + 1))) where
  K := FreeGroup (Fin (n + 1))
  torsionFree := isPowerTorsionFree_freeGroup
  emb := MonoidHom.id _
  emb_injective := Function.injective_id

/-- The homomorphism the final `comap` runs along: read a word back at its own
positions, then spell those positions as rows of `F₃`. -/
def rowSection (n : ℕ) : FreeGroup (Fin (n + 1)) →* Conj.F₃ :=
  Seq.rowHom.comp (sectionHom n)

/-- **The preimage of the completed row subgroup is `N` exactly.** -/
theorem comap_completedRowSection_eq (n : ℕ)
    (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    (Subgroup.closure (Seq.bElt '' codeSet n N) ⊔ periodicRowKernel n).comap
      (rowSection n) = N := by
  refine Subgroup.ext fun w => ?_
  rw [← map_rowHom_completedCodeSub n N]
  constructor
  · intro hw
    have hmem : Seq.rowHom (sectionHom n w) ∈
        (completedCodeSub n N).map Seq.rowHom :=
      Subgroup.mem_comap.mp hw
    rw [Subgroup.mem_map] at hmem
    obtain ⟨u, hu, hu'⟩ := hmem
    have hus : u = sectionHom n w := Seq.rowHom_injective hu'
    have hsec : sectionHom n w ∈ completedCodeSub n N := by
      rw [← hus]
      exact hu
    exact (sectionHom_mem_completedCodeSub_iff n N w).mp hsec
  · intro hw
    refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ?_)
    exact ⟨sectionHom n w,
      (sectionHom_mem_completedCodeSub_iff n N w).mpr hw, rfl⟩

/-- **Higman's Section 5, from its two leaves.**  Everything between them ---
the block coding, the decoding homomorphism and its section, the code set with
its soundness and completeness, and the final preimage --- is proved in the
two dependency modules. -/
theorem transportSectionFive_of_parts (hcode : CodeRE)
    (hunc : UnConjugation) : TransportSectionFive where
  transport := by
    intro h
    refine ⟨?_⟩
    intro n N _hN hre
    have hB : REset (codeSet n N) := hcode.code_re n N hre
    have h₁ : BenignTF (Seq.ASub (codeSet n N)) := h (codeSet n N) hB
    have h₂ : BenignTF (Subgroup.closure (Seq.bElt '' codeSet n N)) :=
      hunc.unconj (codeSet n N) h₁
    have h₃ : BenignTF
        (Subgroup.closure (Seq.bElt '' codeSet n N) ⊔ periodicRowKernel n) :=
      BenignTF.sup h₂ (benignTF_periodicRowKernel n)
    have h₄ : BenignTF ((Subgroup.closure (Seq.bElt '' codeSet n N) ⊔
        periodicRowKernel n).comap
        (rowSection n)) :=
      BenignTF.comap (freeTFOvergroup n) (rowSection n) h₃
    rw [comap_completedRowSection_eq n N] at h₄
    exact h₄

end Transport
end Higman
end GroupApproximation
