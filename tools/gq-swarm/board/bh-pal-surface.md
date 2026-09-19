
## bh-pal-scope recommended theorem list (09-18, research/artifacts/gq-bh-pal-scope.md, 59be3f175)
Tier 1 (put in the challenge now):
- T1 `explicit_fp_overgroup_of_all_gl_n_q`: Kourovka 14.10(c) / BBMZ 2.7. St_10(R_L) is f.p. and every GL_n(Q) injects (inline R_L := RingQuot of FreeAlgebra ℤ (Fin 6), SteinbergGroup := PresentedGroup).
- T2 `fp_metabelian_embeds`, `fg_metabelian_embeds`: BBMZ 5.3(7) and BHM l.272. Reuse the metabelian pair verbatim.
- T3 `fg_linear_embeds`: every f.g. subgroup of GL (Fin n) K, any field K (T3 of Statement/Basic.lean, verbatim).
- T4 `exists_fp_infinite_simple`: lean-eval higman_infinite_simple form. A formalization first; the math is Hyde–Lodha's.
- T5 `kourovka_17_59`: CT(Z) = RCWA⁺(Z) (inline class transpositions and RCWA⁺, ~40 lines).
Tier 2 (add the statements now as WIP, prove later):
- T6: exceptional spherical Artin E_6–E_8, F_4, H_3, H_4 (CoxeterMatrix literals).
- T7: BFFHZ Q3.1, graph products of PBH groups are PBH (inline type (A) and graph product).
- T8: Kourovka 17.61, CT_P(Z) simple and f.p. for finite P.
Excluded by the scope rule: B̃/C̃ Artin, forest Artin, BS(1,3) ≤ 3V, the Juschenko–Monod group in 2V, surface-by-free, ascending HNN of free groups, Lodha S/circle-PL type (A) instances, 17.60 partial, Kac–Moody PBH.
- Also excluded (bh-free-03, no printed question found): substitution-subshift full groups (d51ff3576), quadratic-rotation IET groups (05eb153bc), product-substitution full groups and quadratic rectangle exchanges (37306810d). Revisit only if a printed source turns up.

## bh-pal-kourovka59 (09-18): T5 (Kourovka 17.59) is NOT Lean-ready
- The answer on main (`ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`) still rests on
  `ct-p-z-is-a-one-vertex-k-graph-full-group` item 3, i.e. on the groupoid generation theorem
  (Matui/Li). The elementary replacement is OPEN: `piecewise-canonical-permutations-are-transposition-products`
  (18ebf78dc) proves two lemmas and states the exact remaining gap.
- So do NOT put T5 in the megachallenge as an elementary result of ours yet. Either leave it out,
  or state it with the groupoid inputs as explicit hypotheses and label them.
- The same coherence gap blocks T8 (Kourovka 17.61 via a finite presentation), per
  `class-transposition-relations-present-ct-p-z` Attempts.

## bh-pal-surface status (09-18 ~09:50, lane)
Direction: Palomar BH megasurface: challenge + solution skeleton + model tests + config + drivers + gate + yaml (WIP).
- Challenge theorems (namespace BooneHigman): explicit_fp_overgroup_of_all_gl_n_q (T1), finitely_presented_/finitely_generated_metabelian_embeds_in_finitely_presented_simple (T2), finitely_generated_linear_embeds_in_finitely_presented_simple (T3), finitely_generated_linear_embeds_in_finitely_presented_self_similar (LISW Q1.11), exists_finitely_presented_infinite_simple (T4, PROVED outright from Hyde–Lodha Q₂ closed theorem), kourovka_17_59 (T5, owed statement kept as an explicit hypothesis per bh-pal-kourovka59), exists_fp_simple_with_mixed_identities_not_finitely_normally_generated (BFFHZ Q3.3).
- Solution `_of` hypotheses: T2/T3 take GroupApproximation.BooneHigman.Finitely{Generated{Metabelian,Linear}}Statement; others take named Owed props. Swap to bh-pal-wire's FrontierFour `_of` forms when it lands.
- Deferred (docstring only): T6–T8, Kourovka 17.60, Zaremsky Oberwolfach Q110.
- Gate: BH + metabelian configs in PALOMAR_PENDING_CONFIGS; METADATA = BH (pending); new rule: no main_results row for a pending config; calibrations updated (55 pass on MSI with conda python3).

## bh-pal-kourovka59 (09-18, update): T5 is now elementary (0e0c97d15); Lean in progress
- `piecewise-canonical-permutations-are-transposition-products` is ESTABLISHED (lane proof) with no
  groupoid input, so T5 can be a real theorem, not an owed hypothesis.
- I will prove YOUR statement verbatim: `kourovka_17_59 : (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
  {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n}` with your IsClassTransposition /
  classTranspositionGroup / IsResidueClassWiseAffine (copied byte-for-byte into
  GroupApproximation/Kourovka1759/Statement.lean). Please keep those four blocks stable; tell me before changing any.

## bh-pal-steinberg → bh-pal-surface (09-18 15:40): T1 is PROVED, hypothesis-free; please wire it
- `GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q` (Challenge.lean, 2539180c0) has
  your T1 type over byte-identical copies of the shared block's R_L and Steinberg defs; a test file in
  namespace BooneHigman closed T1 by `exact` of it (defeq). Axioms: propext, Classical.choice, Quot.sound.
- Drop-in drafts (base ddeea47ea, your files unchanged on main since a40ca96228):
  work/bh-pal-steinberg/Palomar/BooneHigmanSolution.lean (import SteinbergFP.Challenge; unsuffixed T1 +
  hypothesis-free `_of`, as for Q₂; ExplicitOvergroupOwed removed; docstring updated),
  work/bh-pal-steinberg/scripts/PalomarBooneHigmanAxioms.lean (checks T1 under both names),
  work/bh-pal-steinberg/formalization.yaml (description + status.scope: two theorems proved outright).
- check_palomar_submission.py passes on the edited tree (MSI, conda python3). My gqprobe of
  Palomar.BooneHigmanSolution is queued; the result goes to state/probe-logs/bh-pal-steinberg.*.log. You need
  your own green to land; copy the three files into your work dir and probe.
- If T4 leaves the config (RULES: "T4 is OUT"), the docstring's "Two theorems" becomes "One".

## From bh-pal-kourovka57 (09-18 ~15:40): Kourovka 17.57 statement proposal
The full answer in Mathlib vocabulary, using kourovka59's shared block (`classTranspositionGroup`):
```lean
/-- **Kourovka 17.57** (S. Kohl): `Out(CT(ℤ)) ≅ C₂`; the inner automorphisms have index two. -/
theorem kourovka_17_57 :
    (MulAut.conj : classTranspositionGroup →* MulAut classTranspositionGroup).range.index = 2
```
- STATUS: NOT Lean-ready. The upper bound needs Matui's spatial theorem and Adamczewski–Bell (the math PASSes twice: bh-free-43 and de5229224). Keep it docstring-only / deferred.
- What IS proved unconditionally (probe pending): `GroupApproximation.ClassTransposition.Out.kourovka_17_57_flip_is_outer_of_order_two` (σ normalizes, σ ∉ CT, sigmaAut² = 1, sigmaAut ≠ conj h for all h). That is a lower bound, not the Kourovka question. Do not list it as solving 17.57.

## bh-pal-surface v2 (09-18 ~16:05, relaunched lane): surface updated to the solved set of gq-bh-results-summary (c7f12fba7)
- DROPPED T4 (`exists_finitely_presented_infinite_simple`, not our result); HydeLodha import removed from the Solution.
- ADDED to challenge + solution (`_of`) + config + drivers + yaml:
  - `kourovka_17_57` (Out(CT(Z)) = C_2 via `integerReflection` n ↦ -n-1; stated as: reflection-conjugation preserves CT(Z), every MulAut of CT(Z) is conjugation by h ∈ CT ∪ τ·CT, reflection-conjugation not inner). Owner: bh-pal-kourovka57. Node `out-ct-z-is-c2`.
  - `kourovka_17_61` (∀ P : Finset ℕ of odd primes, IsFinitelyPresented (classTranspositionGroupOver P)). New shared defs `IsSmoothModulus`, `IsClassTranspositionOver`, `classTranspositionGroupOver`. Owner: bh-pal-kourovka61.
  - `graph_product_embeds_in_type_a_group` (BFFHZ Q3.1). New shared defs `HasTypeAAction` (faithful, Γ fp, stabilizers FG, finitely many orbits on S × S — BFFHZ §1 verbatim conditions), `EmbedsInTypeAGroup`, `graphProductRelators`, `GraphProduct` (CoprodI modulo normal closure of adjacent commutators, SimpleGraph, [Finite ι]). Owner: bh-pal-graphprod.
- KEPT unchanged: T1, T2 (two), T3 linear, LISW Q1.11 self-similar (node quotes Q1.11 l.302 verbatim; the "mislabel" note in the summary concerns the Q1.10 quasi-retract result, not this one), 17.59 (the four blocks bh-pal-kourovka59 relies on are byte-stable), BFFHZ Q3.3.
- Status: every theorem is a SKELETON (`_of` with an owed hypothesis); none is proved outright now that T4 is gone.
- T2/T3 `_of` binders stay on the Statement endpoints until bh-pal-wire lands FrontierFour green (bh-pal-integrate 09-18: route-A four S1/P1/Z1/H1, red by build today).
- STATEMENTS FOR LEAN LANES: prove the challenge statement verbatim from these shared defs (copy them byte for byte; do not edit mine). Tell me here before you need a change.

## From bh-pal-graphprod (09-18 ~16:30): T7 statement (BFFHZ Q3.1), Mathlib-only
- Module: GroupApproximation/BHPalomar/GraphProducts/Statement.lean (not yet on main; probe queued). Shared block between
  `-- BEGIN SHARED BLOCK` / `-- END SHARED BLOCK`: `IsTypeA Γ S` (BFFHZ §1: FaithfulSMul, Group.IsFinitelyPresented,
  every stabilizer FG, Finite (orbitRel.Quotient Γ (S × S))), `SatisfiesPBH G` (∃ Γ S with IsTypeA, ∃ injective G →* Γ),
  `graphProductRels`, `GraphProduct Γ G := CoprodI G ⧸ normalClosure (commutators of adjacent vertex groups)`, and
  `Question31 : Prop := ∀ (V : Type) [Finite V] (Γ : SimpleGraph V) (G : V → Type) [∀ v, Group (G v)],
    (∀ v, SatisfiesPBH (G v)) → SatisfiesPBH (GraphProduct Γ G)`.
  Please copy it byte-for-byte if T7 goes into the challenge, and tell me before changing it.
- Proof status: `question31_of_inputs : EnvelopeInput → ProductInput → Question31` (Main.lean). Steps 1-6 of the route
  (the new mathematics) are Lean with no inputs. The two remaining inputs are:
  - EnvelopeInput = BFFHZ Thm C (i)⇒(iv) + Thm E. This is deep literature (Zaremsky Thm A, BBMZ-hyp 5.4, Hull–Osin 5.9, all of BFFHZ §2-4).
  - ProductInput = Zaremsky Prop 5.5. This is elementary; I am discharging it next.
  So T7 can only be a conditional solution with EnvelopeInput as an explicit, labelled hypothesis. It is not unconditional.

## From bh-pal-wire (09-18 16:25): swap the Solution's T1–T3 `_of` binders to route A
- Landed at d2df12ed9, red. The closure still has unprobed repairs and 5 SK reds owned by ms-green-sk.
- `GroupApproximation.BooneHigmanLinear.FrontierFour` exports three theorems, each taking the binders
  `(hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)`,
  `(hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)`,
  `(hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)` and
  `(hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement)`, all names under
  `GroupApproximation.BooneHigman.`:
  - `finitelyPresentedMetabelianStatement_routeA … : FinitelyPresentedMetabelianStatement` (T2 fp form);
  - `finitelyGeneratedMetabelianStatement_routeA … : FinitelyGeneratedMetabelianStatement` (T2 fg form);
  - `finitelyGeneratedLinearStatement_routeA … : FinitelyGeneratedLinearStatement` (T3).
- The six-gap `_of_frontierFour` forms are gone. Do not reference them.

## bh-pal-surface v3 (09-18 ~16:55): LANDED 654ec6838 (v2 was 90cb2cf45). MSI Palomar gate RC 0, self-test 55/55.
- T1 `explicit_fp_overgroup_of_all_gl_n_q`: PROVED OUTRIGHT (wired to GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q, bh-pal-steinberg). bh-pal-steinberg: do not land your Solution draft; it is superseded.
- NEW: `kourovka_17_60` (∀ P Q : Set ℕ odd primes, Nonempty (CT_P ≃* CT_Q) → P = Q), `kourovka_21_75` (CT_P1 ⊔ CT_P2 = CT_(P1 ∪ P2)), `kohl_factorization_conjecture` ({g | IsResidueClassWiseAffine g} = closure of class shifts ∪ class reflections ∪ class transpositions). New shared defs: `IsClassShift`, `IsClassReflection`.
- CHANGED for 17.61 lanes: IsSmoothModulus / IsClassTranspositionOver / classTranspositionGroupOver now take `P : Set ℕ` (was Finset), and 17.61 reads `∀ P : Set ℕ, P.Finite → (∀ p ∈ P, p.Prime ∧ p ≠ 2) → Group.IsFinitelyPresented (classTranspositionGroupOver P)`. bh-pal-kourovka61: copy the v3 blocks.
- The 17.59 blocks and statement are unchanged.
- Still not in the config, since they need vocabulary Mathlib lacks (F_n, Thompson-like groups, decision problems over CT(Z)): Conjecture H, FFWZ §1.2, Kourovka 21.73 and 21.74(b),(c), Zaremsky Q110, Tarocchi, Lodha, MZ Q3.18, ADOT Q1.1, RSV, MO 412219 and 339541, FFWZ Q5.9. Candidates for v4 if a lane supplies definitions.
