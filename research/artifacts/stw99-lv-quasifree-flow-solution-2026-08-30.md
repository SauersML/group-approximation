# Solution of STW Problem LV: quasifree flows on O_2 are pairwise non-cocycle-conjugate

*2026-08-30 goal session.  Problem source: arXiv:2506.10902 v2
(extraction #58 → numeral LV): "Determine when the quasifree flows
α^{(λ)} on O_2 are cocycle conjugate for irrational λ > 0."*

## Answer

Never, except trivially: `α^{(λ)} ≈_{cc} α^{(μ)}` iff `λ = μ`.
Claim `o2-quasifree-flows-cocycle-conjugacy-classified`, route
`o2-quasifree-flows-kms-separation-proof`, and
`stw99-lv-answered-by-kms-separation` closes the problem node.

## The invariant

`β(λ)` = unique root of `e^{-β} + e^{-λβ} = 1` (the quasifree KMS
temperature), READ OFF the cocycle-conjugacy class as the
trace-scaling exponent of the dual flow on the unique tracial ray of
`O_2 ⋊_{α^{(λ)}} R` (Kishimoto--Kumjian supply the unique ray for
irrational `λ > 0`).  Cocycle conjugacy preserves the marked pair
(crossed product, dual flow) by conjugacy + Packer--Raeburn exterior
equivalence, hence preserves the exponent; `β` is strictly decreasing
in `λ`, so it separates all parameters.

## The adversarial model test (why the unique ray is load-bearing)

KMS data is NOT naively cocycle-invariant: on `M_2`, the trivial flow
and `Ad(e^{itH})` are exterior equivalent, yet the trivial flow's
KMS_β states (= the trace, for every β) differ from the Gibbs states.
The dual picture resolves this correctly: `M_2 ⋊_{triv} R ≅
M_2 ⊗ C_0(R̂)` has tracial cone = measures on `R̂`, the dual flow acts
by TRANSLATION, and the rays quasi-fixed by the dual flow are exactly
the exponential densities `e^{-βx}dx`, one for each `β`, with scaling
`e^{-βs}`.  So the cocycle-conjugacy invariant is the SET of scaling
exponents of dual-quasi-invariant tracial rays — all of `R` in the
degenerate `M_2` example (matching "KMS at every β"), and the single
point `{β(λ)}` for the quasifree flows, where the ray is unique.
Exterior equivalence moves which KMS state is distinguished, never
the exponent spectrum.

## Scope notes

* Plain cocycle conjugacy (the STW formulation).  If one allows time
  rescaling as well, the same invariant classifies up to scaling of
  `β`, and the generator swap realizes `λ ↔ 1/λ` after rescaling by
  `λ`; the classification "up to rescaled cocycle conjugacy" is
  `{λ, 1/λ}`.
* The argument never uses Dean's identification of the crossed
  product with `W ⊗ K` (nor its open completion to all irrational
  `λ`); only simplicity + unique tracial ray.
* Sanity anchor for signs/normalizations: gauge action on `O_n`,
  `β = ln n`, `O_n ⋊ T ≅ M_{n^∞} ⊗ K` with dual trace-scaling `1/n`
  (Bratteli--Kishimoto picture).
