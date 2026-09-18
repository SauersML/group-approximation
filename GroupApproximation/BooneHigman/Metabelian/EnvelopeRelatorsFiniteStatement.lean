import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsFiniteCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite normal-form relators: the isolated core statement

`RNRelatorsFiniteCoreStatement` is the gap left by this lane, and
`rnNormalFormRelators_of_finiteCore` reduces `RNNormalFormRelatorsStatement` to it.

**Truth.** The core is implied by the target: take `R₀ := R` and `F = E = ∅`, then use
monotonicity of `Subgroup.normalClosure`. The target is true (Rover–Nekrashevych normal form
plus Higman's finite generation of the pointwise cone stabilizer), so the core is true too.
A non-circular proof of the core follows the same route:
1. `(rnFreeHom H x₀).ker ≤ ⟨⟨nfRelators H x₀⟩⟩`. Using the four families, every word reduces
   to `nfV v * ∏ L_w(h_w)` over a complete prefix code. In the kernel all `h_w` and `v` are
   trivial.
2. The commutation family is needed only for `f` in the pointwise stabilizer of `cone [x₀]`
   in `V_X`. That stabilizer is finitely generated (it is isomorphic to `V_{d,d-1}`), which
   gives `F`.
3. Disjoint-cone relators reduce, modulo commutation relators, to finitely many pairs
   `(e, w)`, using the transitivity of `V_X` on incomparable pairs. This gives `E`.
4. Split and root relators reduce to generators of `H` via multiplicativity. They go into `R₀`.

**Strictly smaller in proof content.** The core keeps the `H`-side quantifiers of both
commutation families unrestricted: every `h, k ∈ H`, and every `f ∈ closure F`. Everything
that turns these infinite families into a finite `R` is proved here:
* extracting a finite generating set of `H` from `Group.IsFinitelyPresented ↥H`;
* passing commutation from generators to generated subgroups, on both sides, in
  `RNFree X H ⧸ ⟨⟨R⟩⟩` (`nfCommRelatorsOn_subset`, `nfDisjRelatorsOn_subset`);
* checking that the finite generator relators are normal-form relators, and the finiteness
  bookkeeping.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **Core statement.** A finite set `R₀` of normal-form relators, a finite set `F` of
elements of `V_X` fixing `cone [x₀]`, and a finite set `E` of valid disjoint-cone data. Together
with the full commutation families over `H` they normally generate the kernel of
`rnFreeHom H x₀`. -/
def RNRelatorsFiniteCoreStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented ↥H → Group.IsFinitelyPresented ↥(higmanThompsonV X) →
      ∃ (x₀ : X) (R₀ : Set (RNFree X H)) (F : Set ↥(higmanThompsonV X))
        (E : Set (↥(higmanThompsonV X) × List X)),
        R₀.Finite ∧ R₀ ⊆ nfRelators H x₀ ∧ F.Finite ∧
        (∀ f ∈ F, ∀ y : Cantor X,
          (f : Equiv.Perm (Cantor X)) (prepend [x₀] y) = prepend [x₀] y) ∧
        E.Finite ∧
        (∀ p ∈ E, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2 ∧ ¬ [x₀] <+: p.2 ∧
          ¬ p.2 <+: [x₀]) ∧
        (rnFreeHom H x₀).ker ≤
          Subgroup.normalClosure
            (R₀ ∪ nfCommRelatorsOn H (Subgroup.closure F) ∪ nfDisjRelatorsOn H E)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNRelatorsFiniteCoreStatement

/-- **Endpoint.** The core statement gives the finite normal-form relator statement. -/
theorem rnNormalFormRelators_of_finiteCore (hcore : RNRelatorsFiniteCoreStatement) :
    RNNormalFormRelatorsStatement := by
  intro X _ _ H hH hfp hV
  obtain ⟨x₀, R₀, F, E, hR₀, hR₀nf, hF, hFfix, hE, hEcone, hker⟩ := hcore X H hH hfp hV
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (rf_fg_of_isFinitelyPresented hfp)
  refine ⟨x₀, R₀ ∪ nfCommGen H S F ∪ nfDisjGen H S E,
    (hR₀.union (nfCommGen_finite H hSfin hF)).union (nfDisjGen_finite H hSfin hE),
    nfFiniteRelators_subset H x₀ hR₀nf hFfix hEcone, hker.trans ?_⟩
  have hR := Subgroup.subset_normalClosure (s := R₀ ∪ nfCommGen H S F ∪ nfDisjGen H S E)
  refine Subgroup.normalClosure_le_normal (Set.union_subset (Set.union_subset
    (fun r hr => hR (Set.mem_union_left _ (Set.mem_union_left _ hr))) ?_) ?_)
  · exact nfCommRelatorsOn_subset H hS
      (Subgroup.normalClosure (R₀ ∪ nfCommGen H S F ∪ nfDisjGen H S E))
      (fun s hs f hf => hR (Set.mem_union_left _ (Set.mem_union_right _ ⟨(s, f), ⟨hs, hf⟩, rfl⟩)))
  · exact nfDisjRelatorsOn_subset H hS E
      (Subgroup.normalClosure (R₀ ∪ nfCommGen H S F ∪ nfDisjGen H S E))
      (fun p hp s hs t ht => hR (Set.mem_union_right _ ⟨((s, t), p), ⟨⟨hs, ht⟩, hp⟩, rfl⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNormalFormRelators_of_finiteCore

end GroupApproximation.BooneHigman.Metabelian.Envelope
