# oa-llp — C*(G) does not have the local lifting property

Lane oa-llp, launched ~20:15 by main. The brief is the `OA LANES 20:15` table in main's `ct/ROSTER-sk.md`.

## CLAIM

- CLAIM LLP definitions (Ozawa Def 3.5) and scalar calibration: `GroupApproximation/Analysis/LocalLiftingProperty.lean`
- CLAIM LLP plus a trace-preserving matrix model gives the factorization property: `GroupApproximation/Analysis/LocalLiftingFactorization.lean`
- CLAIM printed endpoint, tex l.175–177: `GroupApproximation/Manuscript/SimpleKazhdanSofic/CStarNoLocalLifting.lean`
- Not mine: Arveson extension from operator systems into matrices, owned by oa-ucp (roster 20:35). I consume it through a named statement.

## Printed sentence

tex l.263–265 at 9047d0d3c (md5 274f1936…), section "Brown's formulation". Census row `1fe81fb1330c` in the census regenerated at d11e91f6e. At e80dcf20a the sentence was l.175–177:

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

## Status

- 21:3x: claim landed at the current tip. `LocalLiftingProperty.lean` is in progress: definitions, the Arveson statement, and the calibration that ℂ has the LLP.
