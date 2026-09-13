# Idea lane nh-spectral: spectral gap, strong convergence and the multiplicity wall

Date: 2026-09-13. Target `non-hyperlinear-group`. Lens: spectral mechanisms that control
multiplicity, carrying the Kun–Thom expander-centralizer step over from permutation to
unitary (normalized Hilbert–Schmidt) approximations. Nothing here is claimed as proved,
and no Cairn node was edited.

## Where the wall sits

The non-sofic mechanism (`c1168433:official/counterexample.tex`, §2):
- Kun's theorem splits a sofic approximation of a (T) group into expanders.
- The compressors `t_i Γ t_i^(-1) ≤ Γ` match components through a monotone component-size
  function `f = M/(M+m_A)`. It is conserved because permutations preserve counting measure.
- The Kun–Thom expander-centralizer theorem then forces `J` to be LEF.

In the Hilbert–Schmidt row the same endgame is `kt-centralizer-normalization-hs`, whose one
remaining wall is `approximate-collapse-for-kt-compressor`. Its `distinct_from` already records
that no spectral-gap property supplies the collapse (the robust gap is closed by citation in
`el-r-polynomial-robust-spectral-gap`). The localization face is
`actor-commutant-has-liftable-masa-in-every-model`. The multiplicity examples are
`all-representation-expansion-keeps-macroscopic-multiplicity-swap` and
`normalizer-multiplicity-twist-breaks-prefix-expander-rounding`.

Throughout, `M = prod_U M_(d_n)`, `σ : G -> U(M)` is trace-preserving, `Λ = tΓt^(-1) < Γ`,
`Q = σ(Γ)' ∩ M` and `Q' = σ(Λ)' ∩ M`. So `Q ⊆ Q'` and `Ad σ(t)` maps `Q` onto `Q'`. The (CCR)
statement is `Q = Q'`.

## 1. Popa's w-spectral gap at the matrix-ultraproduct level — killed

- **Idea.** A property (T) subfactor `N ⊆ M` has w-spectral gap: `N' ∩ M^V = (N' ∩ M)^V`.
  Apply this to `N = σ(Γ)''` inside `M`, so that approximate commutation with `σ(Γ)` becomes
  exact commutation. Then run the Theorem A endgame.
- **What it would prove.** The collapse `Q = Q'`, hence non-hyperlinearity of the Kun–Thom
  actor.
- **Kill test.** What w-spectral gap outputs versus what (CCR) needs.
- **Result.**
  - It gives stability of each relative commutant under a further ultrapower, i.e. rounding
    of approximate commutants onto `Q` (and separately onto `Q'`). It gives no comparison
    between `Q` and `Q'`.
  - The node text of `approximate-collapse-for-kt-compressor` records exactly this: the gap is
    "the OTHER former gap"; "this is the collapse statement that no spectral-gap property
    supplies".
  - `generic-perturbations-destroy-exact-commutant-gap` shows that the low band need not be the
    literal commutant, even at the finite level.
  - The w-spectral gap statement was taken from search summaries of Popa's principle and
    Goldbring's FCEP notes, not re-read.
- **Verdict: killed.**

## 2. Dimension conservation of adjoint low bands — killed

- **Idea.**
  - The adjoint almost-representation `σ_n ⊗ conj(σ_n)` on `M_(d_n)` has a robust spectral gap
    (`(T;FD)_rob`), so its low band `A_Γ` has a stable dimension across the gap window.
  - `Ad σ_n(t)` conjugates Γ's Laplacian to Λ's, so `dim A_Γ = dim A_Λ`.
  - `Λ ≤ Γ` gives `A_Γ ⊆ A_Λ` up to word length.
  - For equal-dimension subspaces the principal angles are symmetric. That would give
    `A_Λ ⊆ A_Γ`, i.e. collapse, with no dimension in the constants.
- **What it would prove.** (CCR) for every model, hence `non-hyperlinear-group`.
- **Kill test.** Find the step that isn't normalized-HS robust.
- **Result.**
  - The inclusion `A_Γ ⊆ A_Λ` uses the relators `t s t^(-1) = w_s`. Their defects are only
    normalized-HS small, and they multiply `‖x‖_op`.
  - Low-band vectors of `M_d` can have `‖x‖_op ≈ d^(1/2) ‖x‖_2`, so the error is not controlled.
  - Restricting to bounded elements loses the linear-dimension count that the angle symmetry
    needs.
  - This is the same break recorded by `generic-perturbations-destroy-exact-commutant-gap`.
  - Normalizing dimensions by `d_n^2` is vacuous here: a regular-type commutant has dimension
    about `d`.
- **Verdict: killed.** Exact linear algebra is not HS-robust against o(d)-rank relator defects.

## 3. Jones index / Connes–Størmer entropy as the conservation law — killed as a duplicate

- **Idea.** Replace Hamming counting by an intensive invariant `I` of subalgebra inclusions.
  `I` would have to be conjugation invariant, additive in the chain `Q ⊆ Q'`, and equal to 0
  only at equality. Conjugacy `Q' = Ad σ(t)(Q)` together with `Q ⊆ Q'` then forces `Q = Q'`.
  Candidates: the Pimsner–Popa index, or Connes–Størmer relative entropy computed on
  finite-dimensional coordinates.
- **Kill test.** The finite-index case, and the repo's firewall.
- **Result.**
  - With `Q ⊆ Q' ⊆ M` and `[M:Q] = [M:Q'] < ∞`, multiplicativity gives `[Q':Q] = 1`. So the
    argument works only at finite index.
  - At infinite index, strict inclusions `Q ⊊ uQu^*` are possible (shift-type structure).
  - The recorded firewall `kt-intrinsic-subfactor-data-does-not-see-ambient-wall`, cited in
    `approximate-collapse-for-kt-compressor` (2026-08-25): Jones/Pimsner–Popa index and every
    intrinsic subfactor statistic cannot decide (AC). The ambient growth index does see the
    complement, but is normalized-HS discontinuous.
  - Finite-dimensional entropy has dimension-dependent continuity. Under amplification the
    shifts cancel only for relative quantities, and the needed relative quantity is the
    discontinuous ambient index.
- **Verdict: killed as a duplicate of the intrinsic-index firewall.**

## 4. An independent Kazhdan group on the multiplicity factor — killed

- **Idea.**
  - The swap obstruction lives on diagonal checks `V ⊗ V`.
  - `quantum-expander-relative-commutant-rounding` rounds uniformly when the checks are
    `V ⊗ I`.
  - So design the actor so that a second, commuting Kazhdan subgroup `Γ'` acts on each
    Γ-multiplicity space. By Schur, the compressor's multiplicity gauge `U(m)` (see
    `agent-free-compressor-chart-edge-has-multiplicity-gauge`) is then pinned to scalars.
- **What it would prove.** Bounded or rigid multiplicity, making the unitary matching step
  work.
- **Kill test.** Does the gauge actually become scalar in trace-faithful models?
- **Result.**
  - In regular-type models, an irreducible ρ occurs with multiplicity `dim ρ`. For
    `Q_Γ × Q_Γ'` its multiplicity space is `conj(V_ρ) ⊗ l^2(Q_Γ')`, which is not irreducible for
    `Γ'`.
  - The gauge moves to `Γ'`'s right-regular commutant, one layer down. The regress never
    terminates, because trace-faithfulness forces unbounded dimensions at every layer.
  - `normalizer-multiplicity-twist-breaks-prefix-expander-rounding` also shows that ordinary
    normalizer relations do not supply the product form `V ⊗ W`.
- **Verdict: killed.** Multiplicity regress.

## 5. Deformation/rigidity at the ultraproduct level (Peterson, arXiv:2605.16669) — killed as a duplicate

- **Idea.** Peterson's framework carries deformation/rigidity into the continuous model theory
  of II_1 factors. Checked verbatim from the abstract: L(SL_3(Z)) and LF_2 are not elementarily
  equivalent, and LF_2 is not pseudomatricial. Use its rigidity to inspect the ambient
  complement `Q' ⊖ Q`, as the firewall in §3 demands.
- **Kill test.** Is this already consumed on main?
- **Result.**
  - `peterson-innerness-does-not-collapse-kt-compressor` (ESTABLISHED) proves that Peterson's
    factorial-relative-commutant innerness theorem (Theorem 5.2) cannot establish the collapse,
    even for the exact Kun–Thom pair.
  - Sanity check: SL_3(Z) is residually finite, hence hyperlinear. So only compressor-specific
    outputs could ever work.
- **Verdict: killed as a duplicate.**

## Residue

- **Exact reformulation (unclear, probably cosmetic).**
  - `β = Ad σ(t)^*` restricts to a trace-preserving injective endomorphism of `Q'` with range
    `Q`. On `L^2(Q')` it is an isometry `V` with range `L^2(Q)`.
  - By the Wold decomposition, (CCR) fails for σ exactly when `W = L^2(Q') ⊖ L^2(Q) ≠ 0`, and
    then `V^k W` (k ≥ 0) are pairwise orthogonal.
  - So failure of the collapse is a unilateral shift of infinite multiplicity inside the Λ-commutant.
  - The natural spectral certificate against wandering subspaces is approximately periodic
    `σ_n(t)`. Trace-faithfulness kills it: `τ(σ(t^k)) = 0` for `k ≠ 0` when t has infinite order.
  - Not checked against main for an equivalent node.
- **Overlap note.** Lipschitz functional calculus of an approximately central twisted element
  gives approximately invariant spectral corners with a central character. The HS commutator
  estimate `‖[f(A),X]‖_2 ≤ Lip(f) ‖[A,X]‖_2` for normal `A` is standard and was not re-read.
  This route coincides with the Deligne sector-floor program
  (`deligne-cover-sector-floor-below-exponent-one-half`), so it was not pursued here.
- **Take-away for triage.** Every spectral mechanism tested supplies rounding (stability of
  each commutant) and never a comparison between the commutants of `Γ` and `tΓt^(-1)`. The
  missing ingredient is a normalized-HS-continuous invariant of the ambient complement
  `Q' ⊖ Q`. That is exactly the requirement the firewall records; spectral gap, index, entropy,
  product checks and Peterson innerness all fail to provide it.

## Sources

- `c1168433:official/counterexample.tex` §2 (read).
- Main nodes cited above (heads and key lines read).
- Peterson, arXiv:2605.16669 (abstract, verbatim).
- Popa's w-spectral gap and Wang's isolation theorem, via search summaries only.
