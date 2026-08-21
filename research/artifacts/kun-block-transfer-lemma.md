# Kun blocks and quantitative marked-pair transfer

Former Cairn claim `kun-block-transfer-lemma`, demoted because it was
explicitly superseded for the lane by the fixed-algebra proof.  Its stronger
fixed-window quantitative question is preserved below.

Let `(p,q) = (Γ, hΓ)` be the marked pair of the Kun--Thom Theorem E pair
and `F*` the parity-trap window of `parity-trap-window`.

**Claim.**  There are `R ∈ ℕ` and `ε₀ > 0` such that for every
`(F, ε)`-multiplicative `φ : G → Sym(A)` with `F ⊇ B_R ∪ F*` (`B_R` the
`R`-ball of `G` in a fixed generating set) and `ε < ε₀`: no `S ⊆ A` with
`|S| > (1−ε₀)|A|` admits two-point label data at `(p,q)` for the window
`F`.

**SUPERSEDED FOR THE LANE (2026-08-15, same day).**  The consequence this
lemma was built to deliver, `two-point-approximation-fails`, was
established the same evening by the window-free fixed-algebra route
(`two-point-fails-via-fixed-algebra`), which needs no expansion transfer
at all.  This lemma remains open and is retained because it asks for
something the fixed-algebra route cannot give: a **fixed-window,
quantitative** impossibility with explicit `(R, ε₀)`, extending the
explicit constants of the exact-model theorem to approximate models.
Attack it only for that payoff.

**The intended proof shape.**  `φ` restricted to `Γ`-letters is a
`δ(R,ε)`-almost action of the Kazhdan group `Γ`; Kun's expander
decomposition (the permutation version, applied twice — fine `Γ`-blocks
inside coarse ambient blocks — exactly as transcribed at
`official/counterexample.tex:310-371` and Lean-instantiated in
`GroupApproximation/Kun/KunFixedDecomposition.lean`) partitions `A` into
almost-invariant blocks with uniform spectral gap, the surrogate of the
orbits of `exact-models-cannot-separate-marked-pair`.  Within each block
the sheet-expander/deletion argument of that theorem runs verbatim.  What
must be supplied is the **matching control**: in the exact case
`φ(h) ∈ φ(Γ)` forces the `h`-matching to preserve every orbit; here one
must show `φ(h)` almost-preserves the fine block partition on most of `A`.

## Attempts

- **Exact specialization (works).**  For genuine actions the blocks may be
  taken to be the literal `Γ̄`-orbits and the matching control is
  `φ(h) ∈ φ(Γ)`; this is `exact-models-cannot-separate-marked-pair`,
  proved.  So the claim is a strict generalization of a theorem, not a
  speculation about an untested mechanism.
- **Parity fence (bounds any proof).**  Flip models satisfy the two-point
  clauses exactly at every window where transport parity extends
  (`parity-flip-models-satisfy-two-point`), so the claim is FALSE if
  `F* ⊄ F`: any proof must consume the trap identity
  `h = γ'₁γ₂γ₃γ₂^{-1}γ'₁^{-1}γ₃^{-1}`.  This is why `F ⊇ F*` is in the
  hypothesis and why the trap word, not expansion alone, must carry part
  of the argument.
- **Direct trap-to-matching attempt (dies, instructively).**
  Multiplicativity gives `φ(h) ≈ φ(γ'₁)·(Γ-letter images)` within `6ε`
  Hamming, and the `Γ`-letter images almost-preserve the fine blocks.  But
  `γ'₁ ∈ hΓh^{-1}`, whose image is a priori unrelated to the `Γ`-blocks:
  substituting `φ(γ'₁) ≈ φ(h)φ(e_23(1))φ(h)^{-1}` returns a tautology.
  The obstruction is precise: the trap identity constrains how `φ(h)`
  intertwines the `Γ`-structure with its `h`-conjugate, not how it acts on
  the `Γ`-blocks themselves.  Rank the mechanisms below by how they break
  this symmetry.
- **Compressor-word factorization (open, favoured).**  `h = u e_12(x_1)
  u^{-1}` with `u ∈ SL_d(ℤ)`, and the compression semigroup generates `G`,
  so `h` is a bounded word in compressors, their inverses, and one
  `Γ`-letter.  Kun's decomposition (nested form, as recorded in
  `hs-expander-block-decomposition`'s statement of the permutation
  original) controls compressor images: fine blocks drift to fine blocks
  with almost-preserved mass.  A one-sided drift for `t` and the counting
  identity that at finite level a trace-preserving almost-injection of
  blocks is an almost-bijection — the same counting that powers
  `finite-quotient-blindness` and KT's own conservation step — would force
  `φ(h)` to almost-permute the fine blocks, which is the missing matching
  control.  The inverse-compressor bookkeeping is the delicate half.
- **Centralizer mechanism (open, new 2026-08-15, needs `r ≥ 5`).**  The
  marked element `h = e_12(x^{-m})` **commutes** with the Kazhdan subgroup
  `E := ⟨e_kl(R_+) : k,l ≥ 3⟩ ≅ EL_{r-2}(R_+)` (disjoint indices), and for
  `r ≥ 5` — a legitimate choice, Theorem E holds for all `r ≥ 3` and the
  witness claim's "any one member suffices" note covers it — `E` has
  property (T).  Multiplicativity then makes `φ(h)` almost-commute with
  every `E`-letter image, so `φ(h)` carries `E`-almost-invariant sets to
  `E`-almost-invariant sets, and by the in-block spectral gap it carries
  each fine `E`-block near a **union** of fine `E`-blocks with preserved
  mass.  Running the sheet argument with `E`-blocks as surrogate orbits
  (all `E`-letters fix `p`, so they draw the p-sheet) reduces the missing
  matching control to: `φ(h)` cannot **permute** the `E`-blocks
  nontrivially on most mass.  Commuting alone provably cannot force that —
  the block-swap prover shape (two isomorphic `E`-sets, `φ(h)` the swap)
  commutes exactly and swaps — so the residual task is to kill
  block-swapping using the rest of `Γ`, e.g. the mixed conjugates
  `h e_23(f) h^{-1} = e_13(x^{-m}f)e_23(f)` that interlock the `E`-block
  structure with the `Γ`-block structure, or the exact theorem's normality
  input reconstructed through the trap word.  This is now the sharpest
  known sub-question of the lemma.
- **Median engine adaptation (open, the KT-native route).**  The
  transcribed argument builds a size observable from fine blocks and
  normalizing medians from coarse blocks, and derives a contradiction
  between strict compression and total-variation conservation.  Its input
  from the model is separation data along the compressed direction.  The
  two-point labels are exactly such data — `j_s(p) ≠ j_s(q)` with
  equivariance is a `Γ`-almost-invariant distinction of the compressed
  coset — and the question is whether one pair of labels (rather than
  full charts) suffices to feed the strictness step (6).  If yes, the
  claim follows by KT's own conservation contradiction and the sheet
  argument is not even needed; if the medians provably need full-window
  charts, that gap is the precise reason the two-point claim could be
  TRUE, and identifying it would redirect the lane to constructing the
  witness instead.
