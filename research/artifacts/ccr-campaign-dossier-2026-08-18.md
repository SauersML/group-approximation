# The compressor-rigidity campaign — dossier (2026-08-17/18)

Entry point for the rigidity route to `q3-4-resolved`.  Everything
below is on main with proofs, citations, and verification ledgers in
the named nodes; this page is the map.

## The route in one paragraph

Kun–Thom's Theorem A refutes soficity of their wreath group `W` using
Theorem 4.1: sofic representations of the Kazhdan infranormal pair
have `σ(G)`-normalized `σ(Γ)`-centralizers.  The HS/unitary analogue
(`kt-centralizer-normalization-hs`) would refute HYPERLINEARITY of
`W` — the first non-hyperlinear group, refuting the Connes embedding
problem for groups, felling Pestov 3.9 (and advancing 3.4's landscape
decisively either way).  This campaign reduced that analogue to its
minimal open core and closed everything else.

## What is proved (all kernel-of-the-argument, all on main)

1. **(CCR) minimal kernel** — the endgame needs only one containment
   for one compressor: `σ(tΓt⁻¹)' ∩ M ⊆ σ(Γ)' ∩ M`.
2. **(CCR) for coordinate models** (`ccr-for-coordinate-collapsing-models`):
   per-coordinate Kazhdan uniformity + image collapse.  Printed
   precedent for the interchange step: Peterson 2605.16669 Prop 7.8.
3. **Group-algebra slice** (`ccr-group-algebra-slice`):
   `FC_Λ(G) = Z`, so `σ(Λ)' ∩ L(G) = Z(L(G))` for every embedding —
   audited, repaired (binomial pigeonhole, determinant step).
4. **Char-p root-torsion collapse** (`char-p-root-torsion-collapse`):
   every f.d. representation kills a finite-codimension congruence
   ideal on the elementary part (root subgroups are elementary
   abelian `p`; f.d. images finite).
5. **FD-invisibility — the capstone**
   (`fd-invisibility-of-compression`): `ρ(Λ) = ρ(E)` in EVERY f.d.
   representation (`S_Λ + J = R` + same-slot additivity).  Closes
   the coordinate regime of (CCR) unconditionally; answers the
   twisted-tower criterion (CC) = NO vacuously; makes the verified
   nonzero relative `SK₁` (`(ℤ/2)²` for the `𝔽₂[C₂×C₂]` quotient —
   real, but not load-bearing) harmless.
6. **Robust spectral gap free from (T)**
   (`el-r-polynomial-robust-spectral-gap`, closed by citation): DV
   2506.20843 Cor 7.7 — discharges the approximate-Kazhdan
   uniformity gap (`π ⊗ π̄` template, Lem 8.2).

## What is refuted / fenced (never re-attempt)

Finite-quotient and amplification refutations; the bicommutant
shortcut (`σ(γ) ⊥ L²(σ(Λ)'')`); small-block gluing; fixed-λ
uniformity arguments; subcone interpolation (self-similar);
pure-relative-(T) upgrades (explicit counterexample rep
`ℓ²(M/M₀)` — `EL₂(S_Λ)` preserves the compressed module); the
`𝔽_q[x]/(x^e)` K-theory testbeds (K₂ = 0, all `e`); HS-stability
routes for Γ (Becker–Lubotzky forbids); "roots going infinite" as an
enemy signature (the Cantor limit is universal — trace-faithfulness
forces Haar root algebras for EVERY σ).

## The wall — final form

`approximate-collapse-for-kt-compressor` (AC), equivalent forms:
- torus form: `Ad σ(h)`-invariance of `σ(Λ)' ∩ M` for finitely many
  explicit monomial diagonals `h`;
- bimodule form: no honest quasi-regular (`ℓ²(M/M₀)`-type,
  `Λ`-spherical) content in the conjugation bimodule of a
  trace-faithful matrix-ultraproduct representation.

Structural mirror, exact: the sofic proof could not be pure (T) and
consumed the permutation ambient (Kun's decomposition); any unitary
proof cannot be pure representation theory (refuted above) and must
consume the matricial ambient.  The published frontier is
Alekseev–Thom OP 6.2 (2026-08-05, unattempted); its part (b) with
conjugation-coherent lifts converts (AC) to finite-dimensional form.

## Method map for the successor campaign

- The (T;FD)_rob spectral calculus (free) + DV/Peterson intertwiner
  transport + de la Salle's Poincaré = the assembled toolkit; the
  missing piece is matricial-ambient control of quasi-regular
  bimodule content — Popa intertwining adapted to varying-dimension
  matrix ultraproducts (does not exist yet; Peterson §6 is the
  free-product version and does not transport).
- Alternative lever: the ∀∃-expressibility of (AC)-shaped statements
  (Jekel remark) — model-theoretic transfer.  RANK WARNING
  (verified): finite presentation of `EL_r(𝔽_q[x̄])` is FALSE at
  `r = 3` (Krstić–McCool), open at `r = 4`, and holds for `r ≥ 5`
  (synthesis; Tulenbaev abstract-only) — a campaign wanting this
  lever must pin `r ≥ 5`; KT needs only `r, d ≥ 3`.
- Secondary input, status verified: bounded elementary generation —
  proved in one variable with explicit widths (Nica; KPV), OPEN both
  directions for `d ≥ 2`; and in char `p` BEG never yields bounded
  cyclic generation (Abért–Lubotzky–Pyber fence).
- Relative-(T) attribution: cite Kassabov (Invent. Math. 170) and
  the EJK Memoir (AMS 1186, Appendix A, Thms A.1/A.8/A.9) for the
  module-pair forms; EJ 2010 imports, not proves, relative (T).
  Confirmed alongside: `St₅(L_{𝔽₂}(1,2))` IS finitely presented
  (Krstić–McCool Thm 3, rank 5 ≥ 4 — the fork's rank choice is
  load-bearing), and `EL₃(L_{𝔽₂}(1,2)) ≅ L^×` has (T) outright
  (in-repo Lean + Khanh–Thanh Cor. 4.4 — a combination nobody
  spells out in print).

## Stakes and framing

Whichever way (AC) resolves: proof ⟹ first non-hyperlinear group,
group-CEP refuted, Pestov 3.9 falls; refutation ⟹ the rigidity route
dies and the flexible side gains its first real evidence — and the
printed non-sofic groups then press Pestov 3.4 directly.  The other
program fork (`leavitt-steinberg-hs-stability-fork`) bottlenecks in
the same normalized-HS nexus; the two lanes converge here.

*Companion criterion-fork record:*
`research/artifacts/atlas-true-criterion-probe-2026-08-15.md` — the
flip first-order rigidity theorem, exact second-order verdict, and
the closed GPU probe.
