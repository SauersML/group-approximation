---
rg: 2
id: kt-centralizer-normalization-hs
kind: claim
title: Hilbert–Schmidt analogue of Kun–Thom centralizer normalization
invalidates: [growing-fiber-models]
distinct_from:
  invariant-cartan-completion: that asks for an invariant diagonal masa and routes through Corollary D; this asks for normalization of a relative commutant and routes through Theorem A's endgame — no masa appears in it at all
  hs-expander-block-decomposition: that is the HS transcription of Kun's decomposition, which is the INPUT to Kun–Thom Theorem 4.1; this is the transcription of Theorem 4.1 itself, and it needs the cluster groupoid and the two median arguments on top of any decomposition
artifacts:
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

Let `Γ < G` be an infranormal, non-normal Kazhdan pair and let
`σ : G → U(∏_𝒰 M_(d_n))` be a trace-preserving (hyperlinear) representation.
Is the relative commutant `σ(Γ)' ∩ ∏_𝒰 M_(d_n)` normalized by `σ(G)`?

This is Kun–Thom Theorem 4.1 with `𝒮_𝒰` replaced by the unitary group of the
tracial ultraproduct. **A positive answer refutes hyperlinearity of `W`**, by
transcribing their proof of Theorem A verbatim: `Γ` fixes the coset `Γ`, so
`ρ(a_Γ)` lies in the relative commutant; normalization puts every
`ρ(a_(gΓ)) = ρ(g)ρ(a_Γ)ρ(g)⁻¹` there too; but for a strict compressor `t` and
`γ ∈ Γ \ tΓt⁻¹` one has `σ(γ)ρ(a_(tΓ))σ(γ)⁻¹ = ρ(a_(γtΓ)) ≠ ρ(a_(tΓ))`, the
two lamps being at `‖·‖₂`-distance `√2`.

## Why it is not a corollary of the permutation version

Kun–Thom's proof of Theorem 4.1 runs on the finite cluster groupoid of almost
equivariant partial bijections between the `Γ`-expander components: two median
arguments, one on the **vertex mass** of a connected groupoid component and one
on the **order of its isotropy group**, force a transported functor to be full.
Both invariants are counting invariants of a permutation action on a point set.
In the Hilbert–Schmidt category:

- property (T) still supplies the analogue of expansion for free — an action of
  a Kazhdan group on a tracial von Neumann algebra has a spectral gap on
  `L²(M) ⊖ L²(M^Γ)` — so the *expansion* input is not the obstacle;
- what is missing is the *component structure*. Kun–Thom's Lemma 2.3 identifies
  `D_𝒰^(σ(Γ))` with `∏_𝒰 D(Q_n)`, an **atomic** partition algebra whose cells
  have sizes. The fixed algebra `σ(Γ)' ∩ ∏_𝒰 M_(d_n)` of a hyperlinear
  approximation need not be atomic — for `σ ⊗ 1` it contains a `II₁` factor —
  so there are no component sizes and no isotropy orders to run medians on.

This is the decisive open sub-claim on the rigidity side. It is *a priori*
independent of `invariant-cartan-completion`: that one goes through Corollary D
and an invariant masa, this one through Theorem A and a relative commutant, and
neither is known to imply the other. Both, if established, refute
`hyperlinear-wreath-model`; both, if refuted, are consistent with either answer
to Q3.4.

`hs-expander-block-decomposition` is the natural first input — it is the HS
transcription of Kun's decomposition, which is what Kun–Thom feed into
Theorem 4.1 — but it is not recorded as a `requires` here, because even with a
decomposition in hand the two median arguments have no evident HS form: the
quantities they compare are a component's vertex mass and its isotropy order,
and neither survives when the blocks are matrix corners rather than orbits.

## Position relative to Alekseev–Thom Open Problem 6.2

Open Problem 6.2 of arXiv:2608.05362 — statement checked against the full text
in `notes/CREDIT_AND_PRIORITY_AUDIT.md` — asks whether the commutant of a
Kazhdan representation into a tracial matrix ultraproduct is an ultraproduct of
finite-dimensional subalgebras, i.e. whether it admits a **coordinate
description** by centralizers of lifts. This claim asks a different question
about the same object: not how the commutant is described, but whether it is
**normalized** by the ambient group.

The two are adjacent and the dependence runs one way. A positive answer to
OP 6.2 would supply, in the Hilbert–Schmidt category, exactly the coordinate
structure that Kun–Thom's proof consumes — components with masses and isotropy
groups on which medians can be run — and would therefore be the natural first
input here. A negative answer would say the coordinate picture fails already at
the description stage, which is where the flexible side expects the room to be.
Nothing here resolves OP 6.2, and this node must not be read as a claim on it:
OP 6.2 is a published open problem of Alekseev and Thom, and the repository's
interest is the downstream invariance question.

The same adjacency holds one metric class over. In any metric ultraproduct of
finite groups the ultraproduct commutant strictly contains the ultraproduct of
the coordinate centralizers, because the coordinate maps are approximate rather
than genuine homomorphisms; so OP 6.2's difficulty is present in the
bi-invariant category too and is not an artefact of unitaries.

Adjacent, and worth reading before attacking: Alekseev–Thom arXiv:2608.05362,
whose conclusion is that the centralizer of a sofic embedding of a Kazhdan
group is itself a metric ultraproduct of **permutation** groups. The
permutation-specificity of that conclusion is exactly the point at issue here.

## Attempts

**2026-08-18 (sharpening, no resolution).**  Two reductions that shrink
what must be proved, recorded after re-reading the endgame:

1. **The minimal sufficient kernel is one containment for one
   compressor.**  Unwinding `σ(g)(σ(Γ)' ∩ M)σ(g)* = σ(gΓg⁻¹)' ∩ M`, the
   Theorem-A endgame does not consume full `σ(G)`-normalization: the
   contradiction only needs `ρ(a_{tΓ}) ∈ σ(Γ)'`, i.e.

   ```text
   (CCR)   σ(tΓt⁻¹)' ∩ M  ⊆  σ(Γ)' ∩ M
   ```

   for ONE strict compressor `t` and every trace-preserving
   `σ : G → U(M)`, `M` a matrix ultraproduct.  The reverse containment
   is free from `tΓt⁻¹ ⊆ Γ`.  Slogan: *compressing the Kazhdan group
   must not grow its relative commutant.*  This is strictly weaker than
   the normalization question in the header (which quantifies over all
   `g`, including the incomparable `SL_d(ℤ)`-twisted copies), so a
   proof may attack (CCR) directly; a refutation of (CCR) kills the
   route while a refutation of full normalization would not.

2. **Amplification cannot refute it.**  The `σ ⊗ 1` example above
   breaks only the atomic *proof technique*, not the *statement*:
   `(σ ⊗ 1)(Γ)' ∩ (M ⊗ M_k) = (σ(Γ)' ∩ M) ⊗ M_k` and conjugation by
   `σ(g) ⊗ 1` acts componentwise, so normalization (and (CCR)) for
   `σ ⊗ 1` is equivalent to that for `σ`.  Any genuine counterexample
   must entangle the multiplicity space with the group image — plain
   multiplicity is invisible to the question.

Status after both: the hole is unchanged in kind — (CCR) is a new
rigidity statement with no known proof mechanism once atomicity is
gone — but its surface is smaller and better named than "transcribe
Theorem 4.1".  Adjacent recorded fact pointing the same direction:
`t ∈ Γ*` is REFUTED for KT pairs (the compressor lies outside the
profinite-closure skeleton), so (CCR) cannot be reached through
finite-quotient approximations of `t`; whatever proves it must use the
ultraproduct structure itself.

**2026-08-18b ((CCR) on the canonical congruence representation).**
A residual chain gives the canonical faithful-trace sofic
`σ = ∏_𝒰 (regular rep of G/N_n)` (`tr σ(g) = lim tr → 0` for
`g ≠ e`).  Three facts localize (CCR) there:

1. In congruence quotients the compression COLLAPSES:
   `π(tΓt⁻¹) = π(t)π(Γ)π(t)⁻¹ = π(Γ)` exactly, because the elementary
   part `E` is normal in `Q_M` and `π(Γ) = E` — the same
   finite-quotient-blindness that drives the two-point refutation.  So
   the coordinatewise commutants of `Λ̄_n` and `Γ̄_n` are EQUAL at every
   level and coordinatewise (CCR) is a triviality.

2. Hence the entire content of (CCR) for this `σ` lives in the
   **excess commutant** — elements almost-commuting with `σ(Λ)`
   elementwise without coordinate centralizer structure — precisely
   the approximate-vs-genuine homomorphism gap of Alekseev–Thom
   OP 6.2, now with a sharp question attached to it rather than a
   description problem.

3. The naive counterexample template dies structurally: taking
   `x = σ(t) y σ(t)⁻¹` with `y` in the coordinate commutant of
   `Γ̄` gives `[x, σ(γ₀)] = σ(t)[y, σ(t⁻¹γ₀t)]σ(t)⁻¹`, and
   `t⁻¹γ₀t ∈ E` by normality of `E` in `G`, so `y` commutes with it
   and `x` commutes with `σ(γ₀)` — the transported commutant never
   leaves the protected zone.  Any refutation of (CCR)-for-this-`σ`
   must build `x` with no coordinate structure at all; any proof must
   convert Kazhdan `(T)`-stability (almost-commuting with the
   generators of `Λ` ⟹ near the exact centralizer, uniformly in `n`)
   into control of exactly that excess.

Net: for the canonical `σ`, (CCR) is a clean, self-contained question
about excess commutants of Kazhdan images in sofic ultraproducts.

**2026-08-18h: literature position (agent sweep, all five threads
complete; verification ledger below).**

1. **(AC) is the per-compressor core of the tracial-ultraproduct
   analogue of Kun–Thom Theorem 4.1** (statement verified verbatim
   from arXiv:2608.06222), and the ambient unitary question for the
   FULL group's commutant is Alekseev–Thom **Open Problem 6.2**
   (arXiv:2608.05362 §6, verified verbatim, posted 2026-08-05 —
   thirteen days before this entry).  Nobody has attempted either;
   2608.06222 has exactly one citing paper (2608.02025, which uses
   only the weak-sofic corollary).  This node is ahead of the
   published frontier, not behind it.
2. **The KT 4.1 proof is structurally non-transportable — full
   census.**  Operator algebras enter their proof only as a
   container; after the crossed-product embedding the argument lives
   in the diagonal subalgebra, and the objects it runs on (expander
   components, cluster groupoid, orbit counts, Cheeger constants)
   do not exist for a unitary in `M_{d_n}` — no set is acted on.
   Confirms 2026-08-18's "no atomicity" analysis at reference level.
3. **Hard prohibition (Becker–Lubotzky arXiv:1809.00632):** Γ is
   infinite, hyperlinear, Kazhdan ⟹ NOT normalized-HS-stable (their
   theorem, verified from abstract; Thm 1.4 numbering
   subagent-verified).  Never route (AC) through HS-stability of Γ;
   the liftable case is vacuous — far-from-genuine asymptotic
   representations are guaranteed to exist.
4. **One transportable mechanism exists — and its hypothesis turned
   out to be FREE (second sweep pass, Gate 0):** property (T) implies
   Dogon–Vigdorovich `(T;FD)_rob` unconditionally (2506.20843
   Cor 7.7, no lattice input), so
   `el-r-polynomial-robust-spectral-gap` is CLOSED BY CITATION, the
   approximate-Kazhdan uniformity gap of 18f is discharged in print
   (`Ad π_n = π_n ⊗ π̄_n` + DV Lem 8.2 template), and the route
   `hs-normalization-via-robust-spectral-gap` now rests on exactly
   one open requirement: (AC) proper, promoted to the claim
   `approximate-collapse-for-kt-compressor`.  Consistency with
   Becker–Lubotzky resolved (printed `𝔽₂×𝔽₂` separation; the
   hyperfinite weakening is on the input class).  Gate 1 (Peterson
   2605.16669), CORRECTED after the §6 residual was closed by a full
   PDF read (pp. 18–26): **partial positive**, not negative.  No
   partial answer to OP 6.2 and no (CCR) shape (no normalizers of
   commutants, no `N' vs (uNu*)'` comparison) — but four citable
   items: (i) the proof of his Prop 7.8 contains the (T)-licensed
   interchange formula `π(Γ)' ∩ ∏_𝒰 M_{n_ι} = ∏_𝒰 (π_{n_ι}(Γ)' ∩
   M_{n_ι})` IN PRINT, in the varying-dimension matrix ambient — the
   printed precedent for `ccr-for-coordinate-collapsing-models`'s
   steps 1–2; (ii) his class-𝒞_T remark proves the conjugated-family
   interchange `α(P)' ∩ N^𝒰 = ∏_𝒰 (α_ι(P)' ∩ N)` under UNIFORM WEAK
   SPECTRAL GAP of the embedding family — the closest published
   statement to the (CCR) shape, genuine coordinates; (iii) his
   Thm 5.2: coordinatewise deformations of a (T) subfactor with
   factorial relative commutant are INNER (Connes rigidity in the
   ultraproduct) — a second intertwiner-transport mechanism, closer
   to the compressor picture than DV Lem 3.1; (iv) the Jekel remark:
   relative-commutant statements about images of finitely presented
   (T) groups in ultraproducts are ∀∃-expressible, hence transfer
   along elementary equivalence — a model-theoretic attack surface on
   (AC) not previously considered.  FLAG now load-bearing twice
   (here and DV Def 7.5): whether `EL_r(𝔽_q[x₁…x_d])` is finitely
   presented must be settled before either lever is pulled — verify,
   do not assume.  All four items live in the genuine-coordinate
   regime; (AC) proper remains the sole open requirement.
5. **No applicable counterexample mechanism:** Ioana's 2108.09589
   engine (the only one producing controlled far-from-genuine
   asymptotic reps) is blocked when a factor has (T) (de la Salle
   2204.07084 Thm 0.1).
6. **Framing fact for the program:** the non-sofic groups now in
   print are either hyperlinear (Pestov 3.4 = NO) or non-hyperlinear
   (Pestov 3.9 = NO and group-CEP refuted); whichever way this
   node's question resolves, one of Pestov's two remaining questions
   falls (numbering verified from arXiv:0804.3968).  As of
   2026-08-18 no non-hyperlinear group exists in print (stated
   explicitly in the OpenAI chapter, p. 80, subagent-verified).

   *Ledger:* items marked "verified verbatim"/"census" were read from
   source HTML by the sweep agent; DV internals, the OpenAI page, and
   Pestov numbering were verified by its subagents; the
   (AC)-to-4.1-core identification, the 6.2(b) coherent-lift
   reduction, and the Becker–Lubotzky application to Γ are the
   sweep's own inferences, adopted here after checking their logic
   against this node's records.

**2026-08-18g: two trap-fences for the next campaign.**

1. **The bicommutant shortcut is impossible.**  `σ(γ) ∈ σ(Λ)''` would
   imply (CCR) instantly (bicommutant), and the congruence collapse
   makes it look plausible — the diagonal `(π_n(λ_n))_n` EQUALS
   `σ(γ)` coordinatewise.  But it provably fails, always:
   trace-faithfulness gives `⟨σ(γ), σ(λ)⟩ = tr σ(γλ⁻¹) = 0` for every
   `λ ∈ Λ`, so `σ(γ)` is orthogonal to `L²(σ(Λ)'')` and
   `E_{σ(Λ)''}(σ(γ)) = 0`.  The diagonal of escaping group elements
   coincides with `σ(γ)` in `M` yet lies outside the von Neumann
   closure of the constants.  Moral: (CCR), if true, holds strictly
   "from the commutant side" — `σ(Λ)' ∩ M` must be small enough
   without `σ(Γ)` ever entering `σ(Λ)''`.  Do not re-attempt.
2. **Small-block surgery cannot refute (CCR).**  Gluing junk blocks
   of dimension fraction `o(1)` onto genuine representations produces
   approximate representations for free, but any `x` supported on the
   junk has `‖x‖₂ → 0`: a counterexample needs
   `‖[x, σ(γ₀)]‖₂ ≥ c > 0`, so its `Λ`-commuting structure must be
   macroscopically distributed across the coordinates.  Do not
   re-attempt block-gluing refutations.

**2026-08-18f: the residue is an approximate-collapse question, and
both program forks meet there.**  Re-running the coordinate proof
against an arbitrary `σ` (approximate coordinates `π_n`): steps 1–2
survive — in the ultraproduct `x ∈ σ(Λ)'` is EXACTLY `Λ`-invariant,
no per-coordinate Kazhdan inequality needed — and the sole failure
point is step 3.  The residue of (CCR) is therefore precisely:

```text
(AC)  for trace-faithful ultraproduct representations of G, does
      dist₂(π_n(γ), π_n(Λ)) → 0 hold in some coordinatization —
      i.e. does the congruence collapse π(Γ) ⊆ π(Λ) survive the
      passage from genuine quotients to approximate ones?
```

For genuine coordinates (AC) is the proved collapse (`E`-normality);
a (CCR) counterexample needs approximate finite-dimensional
representations of `G` that separate `Λ` from `Γ` in a way NO genuine
finite quotient can — itself a new kind of object, whose existence
would be notable independently.

*Honesty amendment (2026-08-18 audit):* (AC) is necessary-looking but
NOT shown sufficient — for approximate coordinates, step 2's
per-coordinate Kazhdan inequality is also unavailable (`Ad(π_n|_Λ)`
is not a representation), and exact `Λ`-invariance in the ultraproduct
controls fixed-`λ` sequences, not diagonals.  The residue is honestly
TWO named questions — (AC) plus an approximate-Kazhdan uniformity
lemma (almost-invariance under generators of an almost-representation
propagates image-wide with word-length-free constants) — or ONE
question if (AC) is restated in commutation-tolerant form, against
`{u : ‖[x_n, u]‖₂ small}` rather than the bare image `π_n(Λ)`.  A
second uncharted regime, between the proved theorem and (AC): genuine
coordinate chains that SEPARATE `Λ` from `Γ` (if any exist for `G` —
no congruence chain does); the collapsing-regime proof says nothing
there.  Structural note worth carrying: this
places the rigidity route's residue in the same normalized-HS
stability nexus as the OTHER open fork
(`leavitt-steinberg-hs-stability-fork`) — both now bottleneck on
whether approximate representations of specific (T) groups can evade
behavior that all their genuine representations share.  Literature
adjacent to any future attack: De Chiffre–Glebsky–Lubotzky–Thom
cohomology-vanishing stability (unnormalized Frobenius — the
normalized case is the chasm), and Popa rigidity for the bimodule
formulation of 2026-08-18e.

**2026-08-18e: the coarse slice is clean, and the enemy now has a
name.**  Decompose `L²(M) = L²(L(G)) ⊕ H` as `Ad G`-representations
(`L(G)` is conjugation-invariant).  The `L(G)`-slice is closed by
2026-08-18d.  Inside `H`: any sub-bimodule isomorphic to a multiple of
the coarse bimodule contributes NO `Λ`-fixed vectors — the conjugation
action on `ℓ²(G×G)`, `g·(a,b) = (ga, bg⁻¹)`, is free, and `ℓ²`
functions constant on infinite orbits vanish.  And since `Λ` has (T),
weak containment of `triv_Λ` upgrades to actual containment, so a
counterexample to (CCR) must be an HONEST `Λ`-spherical,
non-`G`-trivial sub-bimodule of `H` for a matrix ultraproduct `M` —
quasi-regular-shaped (`ℓ²(Γ/Λ)`-type) bimodule content actually
embedded, not just weakly approximated.  The same (T) fact helps the
refutation side too: to refute (CCR) it suffices to produce
almost-`Λ`-central elements of `M ⊖ L(G)` that are uniformly far from
`Γ`-central — (T) then converts them to an exact `Λ`-fixed,
non-`Γ`-fixed vector.  Both attack surfaces are now stated in
bimodule language; the question "which `L(G)`-bimodules are
matrix-ultraproduct-realizable with actual (not weak) spherical
content" is the precise residue.

**2026-08-18d: the group-algebra slice is PROVED, for every σ.**
`FC_Λ(G) = Z` (finite-orbit pigeonhole + transvection rigidity over
the compressed subring, which retains the constants), hence
`σ(Λ)' ∩ L(G) = σ(Γ)' ∩ L(G) = Z(L(G))` unconditionally — every
group-algebra-supported counterexample channel (centralizer excess,
finite-orbit sums) is dead.  See `ccr-group-algebra-slice(-proof)`.
The full question now lives entirely in `M ⊖ L(G)`.

**2026-08-18c: the canonical case is PROVED.**  (CCR) holds for every
coordinatewise ultraproduct of genuine finite-dimensional
representations with image collapse `π_n(Γ) ⊆ π_n(Λ)` — in particular
for the canonical congruence `σ` — by per-coordinate Kazhdan
uniformity (ε-commutation with the generators of `Λ` is `2ε/κ`-
commutation with EVERY element of `π_n(Λ)`, uniformly) composed with
the collapse.  See `ccr-for-coordinate-collapsing-models(-proof)`.
No groupoids, medians, or atomic invariants appear.  Consequences:
congruence models can never refute the route, and the open remainder
of THIS node is exactly the transport of that uniformity across the
approximate-coordinate gap (the OP 6.2 locus) for arbitrary `σ`.
