# Swarm log: `sp21-lattice-has-congruence-subgroup-property` (2026-09-16)

Agent: `swarm-sp21-lattice-has-congruence-su`. The lock was held on the target for the
session. Nothing was committed.

## Setup

- **Target.** Some torsion-free cocompact arithmetic `Sp(2,1)` lattice `Γ <= G(O)` has a
  finite congruence kernel `C = ker(Γ^ ->> Γ̄)`.
- **What the graph already establishes around it.**
  - **Theorem A** (`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`): finite
    rank of a pro-p completion iff a finite pro-p kernel.
  - `sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel`.
  - `sp21-pro-p-kernel-invisible-to-local-linear-reps`.
  - `sp21-gs-certificate-shape-at-uniform-levels`.
  - The dead-space records on `sp21-lattice-pro-p-completions-have-finite-rank` and on
    `sp21-lattice-few-alternating-and-large-rank-quotients`.
- **Hole worked.** The target itself. No sub-hole was split off.

## External literature gate (checked 2026-09-16)

The status is still **open**. No 2024–2026 source found here settles CSP for cocompact
`Sp(n,1)` lattices.

| Source | Checked | What it says for the target |
|---|---|---|
| Lubotzky, *Some more non-arithmetic rigid groups*, arXiv:1105.4785, §4, Remark 4.2 | re-checked 2026-09-16 | Says the question is open; payoff is a hyperbolic group without finite quotients |
| Wilton–Sisto, arXiv:2410.00556 (v1 2024-10-01, v2 2024-11-25) | abstract and listing | CSP for mapping class groups assuming universal residual finiteness of hyperbolic groups; nothing on `Sp(n,1)` |
| Baumann–Kammeyer, arXiv:2605.03107 (2026-05-04) | abstract | Higher-rank only |
| Titz Mite–Witzel, arXiv:2509.05054 (2025) | abstract | Non-residually-finite `C̃_2` lattices; not arithmetic rank one |
| Mason–Premet–Sury–Zalesskii, arXiv:0710.4009 | abstract | Positive-characteristic local fields; not relevant to `Sp(2,1)` |
| Agol–Groves–Manning, arXiv:0802.0709 (Geom. Topol. 13, 2009) | abstract | Universal residual finiteness implies QCERF; used below for calibration only |
| Tholozan–Tsouvalas, arXiv:2207.14356 | as recorded on the target; not re-read | — |
| Prasad–Rapinchuk survey, arXiv:0809.1622 | **not read** | The PDF fetch returned binary. `pdftotext`, `fitz` and `pypdf` were unavailable or crashed. Unverified |
| Grunewald–Jaikin-Zapirain–Zalesskii, *Cohomological goodness and the profinite completion of Bianchi groups*, Duke Math. J. 144 (2008) | **not fetched** | The web-search budget was exhausted and the arXiv API returned 503. The folklore remark attributed to it is unverified |

## What was proven (promoted)

- **Claim.** `research/sp21-finite-congruence-kernel-forbids-p-goodness.md`, ESTABLISHED.
- **Route.** `research/sp21-finite-congruence-kernel-forbids-p-goodness-proof.md`, with
  `requires: []`.
- **Artifact.** `research/artifacts/sp21-congruence-goodness-2026-09-16.md`, the full
  proof.

Set `D = 21·[k:Q]`. The claim has three items.
1. If `C` is finite, then for every prime `p` and every finite-index `Γ_1`,
   `cd_p(Γ_1^) >= D`. Some finite simple `A` killed by `p` has
   `H^9(Γ_1^;A) != 0 = H^9(Γ_1;A)`. So no finite-index subgroup is good or p-good.
2. If `C` is finite, then for every `p` some finite-index `Γ_1` has
   `H^9(Γ_1^;F_p) != 0 = H^9(Γ_1;F_p)`, with trivial coefficients.
3. If the pro-p kernel `N_Δ` of a finite-index `Δ <= Γ(p)` is finite, then
   `H^9(Δ^_p;F_p) != 0 = H^9(Δ;F_p)`.

**The mechanism.**
- `Γ_1\H^2_H` is a closed aspherical 8-manifold.
- Strong approximation makes the congruence closure open.
- A finite kernel splits off an open `M`, which is isomorphic to an open subgroup of
  `G(O^)`.
- `M` then contains a closed uniform subgroup of `∏_{𝔭 | p} G(O_𝔭)` of dimension `D`.
- Lazard gives that subgroup `cd_p = D`, and closed subgroups do not raise `cd_p`.
- Serre's simple-module test turns `cd_p > 8` into a nonzero degree-9 class.
- For item 2, the cohomology of a closed subgroup is a direct limit over the open
  subgroups containing it.

**Novelty.** None is claimed. This is the folklore reason that CSP makes `SL_n(Z)` not
good. The repository already uses the same mechanism for `SL_3(Z)`, in
`research/artifacts/review-swarm4-2026-09-12.md` §41.3.

**Graph meaning.**
- If the target holds, its lattice is a residually finite Kazhdan hyperbolic group that is
  not good.
- Goodness of one lattice refutes CSP for its `G`. So does goodness of one finite-index
  subgroup, or `cd_p(Γ_1^) <= 8` for one `p`.
- The universal incompatibility was already derivable: `every-hyperbolic-group-is-good`
  gives universal residual finiteness, which gives the negation of the target. The
  lattice-local form is the addition.
- **Integrator suggestion; I did not edit nodes I do not own.** With this theorem
  established, the two open claims exclude each other. Either `refuted_by` link would
  therefore be sound:
  - (i) `every-hyperbolic-group-is-good` could carry
    `refuted_by: [sp21-lattice-has-congruence-subgroup-property]`. That link is new and
    rests on Theorem 1 of the artifact.
  - (ii) The target could carry `refuted_by: [every-hyperbolic-group-is-good]`. This is
    already justified through universal residual finiteness, and now also directly.

  Only one of the two may be added. Both together form a refutation cycle, which
  compilation rejects as non-stratified. Neither is added here, because both files belong
  to other agents.

## Approaches tried and where each dies (not promoted)

1. **Jordan–Hölder reformulation.**
   - **Observation (verified).** An open `V <= Γ^` is the closure of a congruence subgroup
     iff `V ⊇ C`, since `π^{-1}(π(V)) = V·C`. So every congruence closure contains `C`,
     and congruence data cannot see `C`.
   - **Consequence.** Suppose `C != 1`, and let `Γ_0` be congruence. Pick an open normal
     `V` with `C ⊄ V`, and put `W = (V ∩ Γ^_0)·C`. `W` is the closure of a congruence
     subgroup `Δ_2 <= Γ_0`, and `C` maps onto `W/(V ∩ Γ^_0) != 1`. So `C` maps onto a
     simple quotient `W/K̂`, and `K̂ ∩ Γ` is a non-congruence normal subgroup of `Δ_2`
     with simple quotient.
   - **The equivalence.** `C` is finite iff some finite-index `Γ_1` has trivial kernel
     `C ∩ Γ_1^`, as in Lemma 3 of the artifact. Hence CSP holds iff there is a
     finite-index `Γ_0` such that every simple quotient of every congruence subgroup of
     `Γ_0` is congruence.
   - **Where it dies.** This is an equivalence, not a reduction. The split into abelian
     and nonabelian simple quotients does not make either half easier:
     - the abelian half is the pro-p territory of Theorem A and
       `sp21-lattice-pro-p-completions-have-finite-rank`;
     - the nonabelian half is `sp21-noncongruence-simple-kernels-separate-points` and
       `sp21-lattice-few-alternating-and-large-rank-quotients`.

     The target is existential over `G`, so both halves must hold for the same `G`.
2. **Abelian quotients only.**
   - **What it gives (verified).** Assume every finite abelian quotient of every
     congruence subgroup is congruence. For a congruence `Δ`, (T) makes `Δ/[Δ,Δ]` finite.
     So `[Δ,Δ]` is congruence, that is, its closure contains `C`. Iterating, every term
     of the derived series of a congruence subgroup is congruence.
   - **Where it dies.** That is all it gives. The nonabelian simple sections are untouched,
     so there is no reduction.
3. **Finite generation of `C`.** It would be natural to show that (T), or bounded
   generation, makes `C` finitely generated and then deduce finiteness. This dies at the
   second step. A finitely generated profinite group need not be finite. For example, a
   product `∏_p` of finite p-groups is typically finitely generated and infinite, and
   nothing here rules out such an abelianization of `C`.
4. **QCERF side observation (sketch, unverified imports).** Assume CSP, and let
   `Λ <= Γ` be finitely generated, Zariski-dense and of infinite index, for example a
   quasiconvex Schottky subgroup.
   - **The argument.** Suppose the closure `Λ̄` of `Λ` in `G(O^)` is open. This is the
     Weisfeiler/Pink/Matthews–Vaserstein–Weisfeiler strong approximation for Zariski-dense
     subgroups. The trace-field hypotheses and the joint closure over finitely many primes
     were **not checked**. Then `π^{-1}(Λ̄) = Λ^c·C` is open, where `Λ^c` is the
     profinite closure. With `C` finite, `Λ^c` is open. So `Λ` is not separable, and `Γ`
     is not QCERF.
   - **Where it dies.** This is a consequence of CSP, not a route into it. The converse
     test, proving QCERF for a Kazhdan hyperbolic lattice, is out of reach: no
     cubulation exists, and Agol–Groves–Manning only relate QCERF to universal residual
     finiteness.
5. **Torsion in `Γ^` (sketch, standard imports not re-read).** Assume CSP. For almost all
   `𝔭` the model is smooth reductive with `G(F_𝔭) ≅ Sp_6(F_𝔭)`. Choose `N𝔭 ≡ 1 mod p`,
   by Chebotarev, so that `p | |Sp_6(F_𝔭)|`. The reduction kernel is pro-`ℓ` with
   `ℓ != p`, so a p-element lifts by profinite Schur–Zassenhaus.
   - **What it gives.** The open `π(M)` contains `∏_{𝔭 ∉ S} G(O_𝔭)`, which gives
     p-torsion in `Γ^` for every `p`. So `cd_p(Γ^) = ∞`. This is stronger than
     Theorem 1(a).
   - **Why it was not promoted.** It needs more imports (integral models, Lang,
     Chebotarev) and says nothing about pro-p completions. The promoted version uses only
     the primes above `p`.
6. **Cup-product and duality constraints.** Under CSP, deep pro-p completions are uniform
   of dimension `D`, and `Λ^* H^1 -> H^*(Δ;F_p)` must truncate at degree 8. Poincaré
   duality in degree 8 is compatible with that truncation, so there is no contradiction.
   Details are in artifact §4 (C4).

## Certificate boundary

- No computation was run, and no `experiments/` directory was created.
- The promoted claim is a proof from the imports listed on its route: Cartan, strong
  approximation, uniform subgroups, Lazard's `cd_p`, and four Serre propositions. None of
  these sources was re-read in this session, and the numbering is from memory.
- The contrapositive tests in artifact §4 (C3) are **not** finite certificates.
  Degree-9 profinite cohomology is a direct limit over all finite quotients.

## What remains open

- The target itself, and every existing hole below it.
- This session adds a necessary condition, not progress toward sufficiency. Any lattice
  with CSP is a non-good residually finite hyperbolic group. Equivalently, CSP cannot be
  proved through any method that also proves goodness.

## Referee (2026-09-16)

**What I read.**
- All four solver files in full.
- The target node; `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`;
  `normal-subgroups-of-arithmetic-lattices-are-congruence-open`;
  `every-hyperbolic-group-is-good`; `good-cocompact-proper-groups-are-virtually-torsion-free`;
  `review-swarm4-2026-09-12.md` §41.3.
- `git status` showed no unlisted solver files.

**What I checked, step by step.**
- **Lemma 1.** The proper projection `G_∞ -> Sp(2,1)`, the free action and `cd = 8` for
  local coefficients are correct.
- **Lemma 2.** Density of `G(O)` in `G(O^)`, the finite-coset argument and openness of
  the projection to `G_p` are correct.
- **Lemma 3.** Correct; this is the compact-to-Hausdorff bijection argument.
- **Lemma 4.** The containment `L ⊆ B ⊆ W` holds coordinate by coordinate. The dimension
  count `Σ_{𝔭|p} 21[k_𝔭:Q_p] = 21[k:Q]` is correct.
- **Step 0.** The cofinality of normal cores is correct.
- **Theorems 1–3.** Correct as deductions from (I1)–(I7). Theorem 1 is the finite-orbit
  argument for `A`. Theorem 2 is the direct limit over open `V ⊇ U'`. Theorem 3 uses that
  `GL_m(O_𝔭,𝔭)` is pro-p.
- **Sanity check.** The same mechanism for `SL_3(Z)` gives `cd_p(SL_3(Z_p)-uniform) = 8 > 3`.
  That matches the known non-goodness of `SL_n(Z)`, `n >= 3`.
- **Quantifiers.** They match the claim statement. Torsion-freeness is used only in
  Lemma 1 and is a standing hypothesis. The setting (`k`-anisotropic, compact at the other
  archimedean places) is what "cocompact lattice in `Sp(2,1)`" means for the target.
- **Imports (I1)–(I7).** These are textbook theorems: Cartan; strong approximation;
  Lazard and Serre's `cd_p = dim` for torsion-free compact p-adic analytic groups; Serre
  GC I, Propositions 11, 14 and 21 and the limit proposition in §2.2. They are acceptable
  trust surface for a literature-import direct proof. My own recollection of Serre I §3.1
  Prop. 11, §3.3 Prop. 14 and §4.1 Prop. 21 agrees with the solver's numbering. I did not
  re-read the sources: the web-search budget is exhausted. The numbering stays marked as
  from memory.
- **Citation spot check.** Crossref and Project Euclid confirm Grunewald–Jaikin-Zapirain–
  Zalesskii, Duke Math. J. 144 (2008), no. 1, 53–72, DOI 10.1215/00127094-2008-031. The
  abstract does not mention `SL_n(Z)`, so the attribution of the folklore remark stays
  unverified. The claim and artifact now say exactly this.
- **Duplicates.** `bin/cairn search --similar` and a lexical search for goodness/CSP found
  no existing claim with this content. The five `distinct_from` entries are accurate.
- **Novelty.** None is claimed, and that is correct. "New" in the claim means new to the
  graph, which is accurate. The §41.3 reference is the same `cd_p` mechanism used for
  `SL_3(Z)` (cohomological completeness), which is a fair description.

**What I changed.**
- **Claim.** I defined `Γ(p)` and `Δ̄_p` inline, since item 3 used them without
  definition, and I updated the GJZ attribution sentence.
- **Artifact.** I recorded the bibliographic verification of GJZ.

**What I did not change.**
- I added no `refuted_by` link. The solver's integrator suggestion is sound: add at most
  one link between `every-hyperbolic-group-is-good` and the target. Both files are
  committed nodes owned elsewhere, and the link is not essential to landing.
- The side observations in approaches 4 and 5 (QCERF, p-torsion) are sketches with
  unchecked imports and correctly stay in notes.

**Verdict.** Sound and honestly labelled. It lands with small fixes, and the direct proof
stands.
