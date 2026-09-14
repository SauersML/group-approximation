# oa-llp — C*(G) does not have the local lifting property

Lane oa-llp, launched ~20:15 by main. The brief is the `OA LANES 20:15` table in main's `ct/ROSTER-sk.md`.

## CLAIM

- CLAIM LLP definitions (Ozawa Def 3.5) and scalar calibration: `GroupApproximation/Analysis/LocalLiftingProperty.lean`
- CLAIM LLP plus a trace-preserving matrix model gives the factorization property: `GroupApproximation/Analysis/LocalLiftingFactorization.lean`
- CLAIM printed endpoint, tex l.175–177: `GroupApproximation/Manuscript/SimpleKazhdanSofic/CStarNoLocalLifting.lean`
- CLAIM (23:15, absorbed from oa-ucp, which was not resumed): Krein extension from operator systems, `GroupApproximation/Analysis/OperatorSystemStateExtension.lean`
- CLAIM (absorbed): Choi functional of a cp map on an operator system, `GroupApproximation/Analysis/OperatorSystemChoiFunctional.lean`
- CLAIM (absorbed): Arveson extension into matrices, Ozawa Thm 2.2, ucp case, `GroupApproximation/Analysis/OperatorSystemMatrixArveson.lean`
- oa-ucp's transcript has only an unlanded claim report (OperatorSystemBasic, OperatorSystemStateExtension, OperatorSystemMatrixArveson). It wrote no Lean file, and there is nothing of it in the shared tree, backup or attic.

## Printed sentence

tex l.287–290 at 37551fd93 (md5 b55c0d23…), section "Brown's formulation". Census row `a63ff00e499b` in the census regenerated at 649cb1f80. At e80dcf20a the sentence was l.175–177, row `1fe81fb1330c`. The current text:

> So $G$ does not have the factorization property, it is not a subgroup of the unitary group of $\mathcal R$, and $C^*(G)$ does not have the local lifting property~\cite[p.~527]{Ozawa}.

This lane carries the LLP clause. The same claim appears in the introduction, `7f3b239e5f2a` (l.49–52): "noting that the full C*-algebra of such a group cannot have the local lifting property [p. 527]". The general theorem of this lane (simple, Kazhdan, hyperlinear ⇒ C*G fails the LLP) carries it too.

The earlier text:

> So $G$ does not have the factorization property, and $C^*(G)$ does not have the local lifting property~\cite[p.~527]{Ozawa}.

Ozawa, *About the QWEP conjecture*, IJM 15 (2004), arXiv math/0306067. Page 527 is p. 26 of the preprint:

> By the above theorem, the full C*-algebra C*Γ of such a group Γ [simple, property (T), hyperlinear] cannot have the LLP.

## Route (read from the source)

- **Def 3.5.** A ucp map φ: A → B/J is *locally ucp liftable* if every finite-dimensional operator system E ⊆ A admits a ucp ψ: E → B with φ|_E = πψ. A has the LLP if every ucp map into every quotient C*-algebra is locally ucp liftable.
- **Thm 6.1 (ii)/(ii'), Def 7.2.** Γ has (F) when the trace τ(s) = δ_{1,s} on C*Γ is liftable. (ii) is the matrix form: ucp θ_i: A → M_{n(i)} with tr θ_i → τ and asymptotic multiplicativity in the 2-norm. The repository's `NinetyNineProblems.HasFactorizationProperty` is (ii) in sequential form (`Quasidiagonal.IsAmenableTrace`).
- **p. 24 template.** For a hyperlinear Γ = F_∞/N, "because of the LLP of C*F_∞, the trace τ_Γ on C*F_∞ is liftable".

Formal route:
1. A hyperlinear countable group has a trace-preserving unitary matrix model (`HasTracePreservingMatrixModel`). This gives a unital ⋆-homomorphism π: C*G → ∏M_{k(n)}/J₂.
2. If C*G has the LLP, π is locally ucp liftable. The coordinates of a lift on the operator system spanned by finitely many generators are ucp maps into matrices.
3. Arveson extension (Ozawa Thm 2.2, the matrix case) extends them to ucp maps on C*G.
4. A diagonal choice of coordinates gives a sequential amenable trace model on the generators. The dense-generator upgrade (`Quasidiagonal.amenableTraceModel_of_dense_generators`) finishes.
5. So LLP ⇒ (F). The contrapositive, with "G does not have (F)", gives the printed sentence.

## Interfaces

- **oa-kirchberg:** I consume `¬ HasFactorizationProperty G` at the trace side. No tensor interface is needed on this route.
- **oa-ozawa71:** owns `HasTracePreservingMatrixModel G` and its producer from `IsHyperlinear G`, the amplification step of Ozawa Prop 7.1, in `Analysis/HyperlinearTraceVanishingModels.lean`. This lane declares no copy. The core theorem takes the model data as hypotheses, and a one-line wrapper consumes their Prop once it lands.
- **oa-ucp:** owns Arveson extension from operator systems. `OperatorSystemMatrixArvesonStatement` is declared in `LocalLiftingProperty.lean` as a statement only, and the factorization theorem is proved over it.

## Landed

- **bacdfad19**, probe 0914-083605-62533 GREEN, wire-queued:
  - `Analysis/LocalLiftingProperty`: `IsOperatorSystem`, `IsCompletelyPositiveOn`, `IsLocallyUCPLiftable`, `HasLocalLiftingProperty` (Ozawa Def 3.5). Calibration `hasLocalLiftingProperty_complex` (ℂ has the LLP, closed).
  - `Analysis/OperatorSystemStateExtension`: Krein extension from an operator system.
  - `Analysis/OperatorSystemChoiFunctional`: the Choi functional of a cp map on an operator system is nonnegative on ambient positives.
  - `Analysis/OperatorSystemMatrixArveson`: `operatorSystemMatrixArvesonStatement_holds` (closed), Arveson extension into matrices, Ozawa Thm 2.2, ucp case.

- **f118b8057**, probe 0914-085956-97005 GREEN, wire-queued:
  - `Analysis/MatrixModelFormPositivity`: cp operator models pulled back to `M_Y` are form-positive.
  - `Analysis/LocalLiftingFactorization`: `localLiftingFactorizationStatement_holds` (closed). For countable G, the LLP of C*(G) plus `HasTracePreservingMatrixModel G` gives `HasFactorizationProperty G`, along Ozawa's p. 24 route.

## Next

- the printed endpoint `Manuscript/SimpleKazhdanSofic/CStarNoLocalLifting`. It contraposes the theorem above with oa-kirchberg's ¬(F) and oa-mcduff's producer `HyperlinearTracePreservingModelStatement` (statement on origin at bf8ea9f9e).

## Status

- 21:3x: claim landed at the current tip. `LocalLiftingProperty.lean` is in progress: definitions, the Arveson statement, and the calibration that ℂ has the LLP.
