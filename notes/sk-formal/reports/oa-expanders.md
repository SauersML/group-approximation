# oa-expanders ledger

Lane oa-expanders (launched ~20:15 by main). Target: `simple_kazhdan_sofic_group.tex` at e80dcf20a
(386 lines, md5 4ad4921253626a4f858866c716a13385), section "Finite models", l.163–164:

> Since $\EL_3(F)$ has property~\textup{(T)}, their Cayley graphs form a family of expanders~\cite{Kassabov}.

"their" = the finite simple groups $\SL_{3N_\ell}(\F_2)=\EL_3(M_{N_\ell}(\F_2))$, quotients of $\EL_3(F)$
with compatible generators (l.151–160).

## Claims

CLAIM Cayley-graph expander families and the Kazhdan quotient theorem GroupApproximation/Analysis/KazhdanQuotientExpanders.lean
CLAIM printed endpoint for tex l.163–164 GroupApproximation/Manuscript/SimpleKazhdanSofic/FiniteModelsExpanders.lean

Ownership check (20:2x): no expander-family carrier on origin, in the shared tree or in `lanes/*.files`.
Kun's `ExpanderDecomposition` concerns sofic models, and Matching's `HasCheegerLowerBound` concerns
multigraphs and permutation models; neither states the Cayley graphs of finite quotients. landed.log
has no expander landing.

## Route (the printed one: property (T) of EL_3(F) gives expanders for its finite quotients)

1. Definitions: the right Cayley-graph edge boundary `#{(a,t) ∈ A × T : a t ∉ A}`, and
   `IsExpanderFamily`: generating sets of bounded size, vertex counts tending to infinity, and one
   positive Cheeger constant for every set of at most half the vertices.
2. Every finite generating set of a group with a Kazhdan pair carries a Kazhdan constant
   (word-length transfer through `Subgroup.closure_induction`).
3. For a surjection π : Γ → Q onto a finite group, right translation on real ℓ²(Q):
   - invariant vectors are constant, so the centred indicator v = 1_A − (|A|/|Q|)·1 is orthogonal to them;
   - ‖v‖² = |A|(1 − |A|/|Q|) ≥ |A|/2 when 2|A| ≤ |Q|;
   - ‖ρ(s)v − v‖² = 2·#{a ∈ A : a π(s) ∉ A};
   - `exists_moved_mul_norm_of_mem_orthogonal` gives boundary ≥ (δ²/4)|A|.
4. Printed endpoint: consume ms-core-3's L1 (EL_3(M_N(F₂)) = SL_{3N}(F₂)) and L2 ((T) for EL_3(F)) by name
   once they land.

## Status

- 20:2x: claim landed; general module in progress.
