# One ladder behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 3 of 3

Lane `un-synthesis`, 2026-09-13, refresh 3 (main tip 6e4ef12930). Status tags and review landings as in part 1.

## 11. The complexity face

[PASS · 811353c0ef.]
- **Measures are `Π⁰₁`** (`effective-subshift-invariant-measure-existence-is-pi01`). For effectively closed subshifts of a f.g.
  group with solvable word problem, existence of an invariant probability measure is `Π⁰₁`. Novelty: FOLKLORE-level (compare
  Hochman 2009).
- **The LEF type is `Π⁰₁`** (`effective-free-group-kazhdan-lef-type-is-pi01`). On effectively closed, minimal, topologically
  free `F_r`-subshifts, "LEF in every rank" is that `Π⁰₁` set. Its complement is witnessed by `Σ⁰₁` paradox certificates.
- **Contrast.** LEF recognition over finite presentations is `Π⁰₂`-complete (`lef-of-finite-presentations-is-pi2-complete`).
- **[OPEN]** `effective-free-group-kazhdan-lef-type-is-pi01-complete`.

## 12. Along the Pestov end: markings, word problems, isomorphism type

[PASS · 5c8c71e333.]
- **SUBSUMED in substance.** `continuum-many-simple-kazhdan-lef-groups` and `every-turing-degree-is-a-simple-kazhdan-lef-word-problem`
  are subsumed by the older `subshift-elementary-group-word-problem-degree`.
  - That node is by lane ex-kazhdan-simple-hyperlinear, 2026-09-12, reviewed PASS (`ex-review-groups-2026-09-12-part11.md`
    §11.4).
  - It states `WP(G_X) ≡_T L(X)` (also for `G_X/Z`) and `L(X_α) ≡_T α`, realises every Turing degree, and gives uncountably
    many isomorphism classes.
- **Over `F_2`, the marking already determined `X`:** `binary-subshifts-embed-in-three-marked-kazhdan-groups` (root, 2026-09-13).
- **New in this swarm (refinements only).**
  - Explicit words `W_w` with `W_w(σ_X) = 1` ⟺ `w ∉ L(X)`, for every `q` (`marked-subshift-elementary-group-determines-language`).
  - Truth-table equivalence `WP(S_X) ≡_tt L(X)` (`subshift-elementary-group-word-problem-equals-language`).
  - `sturmian-language-is-turing-equivalent-to-angle` is FOLKLORE.
- **Isomorphism type** [OPEN; `subshift-elementary-group-isomorphism-forces-orbit-equivalence`]. Does `S_X ≅ S_Y` force strong
  orbit equivalence? Lane un-orbit-equivalence (6febb83e3c, unreviewed) imports Zel'manov 1985 verbatim: isomorphisms of
  `GL_n`/`E_n` over rings with `1/2` are standard on the elementary subgroup. So the ring route applies for odd `q`, and the
  `K_0` and Giordano–Putnam–Skau steps remain.

## 13. Characteristic dependence: the Grigorchuk groupoid

[PASS · e6fc337462; credit CEPSS 1806.04362 and Nekrashevych.] Let `𝒢` be the Grigorchuk germ groupoid: ample, minimal,
effective, Cantor unit space, not Hausdorff. Put `R_q = A_(F_q)(𝒢)`.
- **Theorem A** (`grigorchuk-steinberg-algebra-simple-iff-char-not-two`). `R_q` is simple ⟺ `q` is odd.
- **Theorem B** (`grigorchuk-elementary-groups-simple-kazhdan-iff-odd-char`). For `n ≥ 3`:
  - `R_q` is finitely generated and carries a unital binary Leavitt family;
  - `EL_n(R_q)` is nonsofic with no MF quotient, for every `q`;
  - for `q` odd, `EL_n(R_q)/Z` is infinite, simple and Kazhdan (Theorem NH);
  - for `q` even it is not simple modulo centre, because of the singular ideal.
- **Reading.** Simplicity of the Kazhdan group reads off `q mod 2`; its approximation profile does not change.

## 14. Paradoxical families

[PASS · 1df28bd83f and ef5760d6c3.]
- **Theorem B** (`paradoxical-cantor-actions-give-simple-kazhdan-not-mf`). Take a minimal, topologically free Cantor action of a
  f.g. group with a finite separating clopen family (H-gen) and a paradoxical decomposition (H-par). Then
  `EL_N(LC(X,F_q)⋊Γ)/Z` (`N ≥ 3`) is infinite, f.g., simple and Kazhdan, and every `EL_n` (`n ≥ 2`) has no MF quotient.
  - (H-par) follows from minimality plus a north–south element (`north-south-minimal-cantor-action-is-paradoxical`).
- **Instances:**
  - **Family T:** `A*B` on its ends, e.g. `PSL_2(ℤ)`;
  - **Family P:** `PSL_2(ℤ[1/p])` on `P¹(ℚ_p)`;
  - **Theorem G** (`paradoxical-steinberg-elementary-simple-kazhdan-not-mf`) with its instances
    `product-two-graph-kp-elementary-simple-kazhdan-not-mf` (`L(1,m)⊗L(1,n)`) and `odometer-nekrashevych-elementary-simple-kazhdan-not-mf`
    (Exel–Pardo quote-checked).
- **Every group containing `F_2`** [PASS · ef5760d6c3; lane un-horofunction-families 703e356968].
  - `f2-groups-have-paradoxical-free-minimal-subshifts`: every f.g. `Γ ⊇ F_2` has a free minimal subshift satisfying (H-gen)
    and (H-par). The construction encodes a two-piece paradox and multiplies by a Gao–Jackson–Seward free minimal subflow.
  - `f2-group-subshift-elementary-simple-kazhdan-not-mf`: the associated `S_N` are infinite, f.g., simple and Kazhdan, with
    no MF quotient.
  - Instances (the `F_2` input is recalled, not separately established): non-elementary hyperbolic groups, one-ended
    included, and `SL_n(ℤ)`.
  - The natural-boundary claim `hyperbolic-group-cantor-model-simple-kazhdan-not-mf` stays [OPEN], but its downstream use no
    longer waits for it.
- **[OPEN]** `boundary-kazhdan-families-pairwise-non-isomorphic`.

## 15. Examples and calibration refutations

| ring `R` | f.g. | simple | ring type | `EL_N(R)`, `N ≥ 3` | status |
|---|---|---|---|---|---|
| `L_k(1,2)`, `k` finite | yes | yes | not directly finite | Kazhdan, no MF quotient, nonsofic | printed; OpenAI + Lean |
| `LC(X,F_q)⋊ℤ`, minimal subshift | yes | yes | exactly matricial | simple Kazhdan LEF | PASS, Lean |
| `LC(∂F_d,F_q)⋊F_d` | yes | yes | purely infinite | simple Kazhdan, no MF quotient, nonsofic, stable, `C*_r` not MF | PASS |
| `LC(Z,F_q)⋊Γ`, `Γ ⊇ F_2`, paradoxical subshift | yes | yes | paradoxical | simple Kazhdan, no MF quotient | PASS · ef5760d6c3 |
| RF-group Toeplitz ring (Kazhdan `Γ` allowed) | yes | yes | exactly matricial | LEF Kazhdan | PASS · 97bf4bc468 |
| `LC(X,F_q)⋊Γ_p` (Abels–Prüfer) | yes | yes | rank model, not matricial | simple Kazhdan, linear sofic, not LEF | PASS · 560decb046 |
| Toeplitz extension of the Pestov ring (`F_2`) | yes | no | defect ideal `J` locally matricial | `n≥4`: radical `EL_n(R,J)`, max MF quotient simple Kazhdan LEF | PASS · c341a29e49 |
| Grigorchuk `A_(F_q)(𝒢)` | yes | iff `q` odd | Leavitt family | nonsofic, no MF quotient; simple mod centre iff `q` odd | PASS · e6fc337462 |
| Labbé `LC(Ω_U,F_2)⋊ℤ²` | yes | yes | stably finite, rank model; matricial ⟺ torus modules | linear sofic; MF-or-rigid for `N≥3`; LEF OPEN | §16 decider |
| `L_k(2,3)` | yes | — | non-IBN | no MF quotient for `N ≥ 3` | PASS · d60f405998 |
| `L_k(3,4)` | yes | — | non-IBN `(3,4)` | no MF quotient for `N ≥ 4`; `N = 3` OPEN | §16 |
| odometer `LC(ℤ_2,F_q)⋊ℤ` | **no** | yes | exactly matricial | LEF, **no (T)** | PASS |
| Weyl `A_1(ℚ)` | no | yes | matricial over `∏M_p(F_p)` only | LEF | PASS; FOLKLORE |
| `F_q[Γ]`, `Γ` amenable, not LEF | yes | no | stably finite, faithful rank | Kazhdan, linear sofic, not LEF | PASS; FOLKLORE |
| Toeplitz `J = F_2⟨s,t:ts=1⟩` | yes | no | defect not full | infinite middle MF regime | printed + unreviewed |

**Refutations every statement respects** (PASS · 10083fd646).
- **(F1)** Matriciality must be over varying finite fields.
- **(F2)** Kazhdan families need finitely generated rings.
- **(F3)** A rank function plus stable finiteness does not give LEF.
- **(F4)** "No MF quotient" needs a full defect.
- **(F6)** [printed l.1072] In positive characteristic, `EL_4(R)` MF ⟹ `R` directly finite.
- **Root Attempts F1:** simplicity is essential.

## 16. The open core, and the open middle around it

**Core.**
- **(Σ⇒)** `linear-sofic-el-groups-force-rank-model`. Famous-level: at `L_(F_2)(1,2)` it would give a non-linear-sofic group
  (part 1 §0.1). It reduces exactly to ring rigidity (RR_k) after the PASS lift, and the missing ingredient is a frame.
- **(M⇐)** `stably-finite-simple-rings-have-mf-elementary-groups`, correct form `mf(R) = ∞` for simple stably finite `R`.
  - Over `F_2` Steinberg algebras only the rigidity half remains [PASS · e07954d78e].
  - First test rings: the Abels–Prüfer ring (§8.5) and the Labbé ring.

**The decider: the Labbé ring over `F_2`** [OPEN, `labbe-wang-shift-crossed-product-is-exactly-matricial`].
- **Matricial.** Periodic quantum tilings exist at every scale, so neither `D([[Ω_U]])` nor `R` is finitely presented, and
  every `GL_n(R)` is LEF.
- **Not matricial.** Every `EL_N(R)` (`N ≥ 4`) is non-LEF, and by S2 either:
  - MF: a simple Kazhdan MF non-LEF group; or
  - MF-rigid: a counterexample to (M⇐).
- **Proved criteria.**
  - Torus criterion [PASS · 72ff092a72, `torus-quantum-tilings-decide-matriciality-of-sft-rings`]. Matriciality ⟺ nonzero
    finite-dimensional modules of the translation-free torus tiling algebras at every scale.
  - Divergence [PASS]: witness dimensions and periods must diverge.
  - Descent [PASS · 81d6f6e73b, `torus-tiling-modules-restrict-to-smaller-scales`]: modules at unboundedly many scales suffice.
  - Constant-shape inflation [PASS · 81d6f6e73b, `constant-shape-substitutions-inflate-torus-tiling-modules`].
  - Corollary [PASS · 81d6f6e73b, `self-similar-sft-matricial-iff-one-torus-module`]. For SFTs with a constant-shape
    substitution, matriciality ⟺ ONE torus module at scale 3.
- **Firewall.** Labbé's morphism has letter-dependent shapes, so the corollary does not reach `Ω_U`. A constant-shape
  substitution would give rational eigenvalues, which the golden rotation factor excludes (recalled).
- **Consequence of (L⇒).** If the ring is finitely presented, no `EL_N` (`N ≥ 4`) over it is LEF.

**The low-rank band** [OPEN, `el-n-mf-quotient-below-twice-paradoxical-level-exists`].
- For `L_k(3,4)` the band is `{3,4,5}`. `N ≥ 4` is settled by non-IBN, so only `N = 3` is open, reduced to
  `leavitt-3-4-module-iso-image-normally-generates-e3`.
- **Firewall** [PASS · d166da76b2]:
  - `ara-goodearl-leavitt-mn-monoid-is-one-relator` [import];
  - `leavitt-module-rank-iso-columns-are-not-completable`: no column of a module isomorphism at module rank is completable;
  - `module-iso-conjugates-of-el-are-stably-elementary`.
- A nontrivial MF quotient of `EL_3(L_k(3,4))` would be a Kazhdan group with an MF quotient inside `EL_4`, which has none.

**Remaining open middle.**
- `invariant-measure-gives-rank-function-any-field` (Kaplansky-hard) and `type-semigroup-reflects-paradox-of-steinberg-algebra`.
- `free-minimal-subshift-elementary-groups-are-sofic` (Arzhantseva–Păunescu Q 8.5).
- `boundary-action-simple-kazhdan-group-is-hyperlinear` (famous either way) and `hyperlinear-groups-kill-rigid-compression-defects`.
- `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure`.
- `paradox-side-elementary-group-is-finitely-presented`, `elementary-group-lef-growth-separates-subshifts`,
  `effective-free-group-kazhdan-lef-type-is-pi01-complete`, `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.
- `measure-rf-class-is-exactly-virtually-free-groups`, `hyperbolic-group-cantor-model-simple-kazhdan-not-mf`,
  `boundary-kazhdan-families-pairwise-non-isomorphic`.
- `steinberg-gl-max-mf-quotient-is-low-degree-homology`, `quantum-matricial-models-separate-full-groups-from-elementary`.
- `relative-torsion-defect-mf-radical-step`, `mf-radical-contains-hilbert-hotel-elementary-subgroup`,
  `hilbert-hotel-radical-is-reached-in-one-step`, `positive-entropy-subshift-crossed-product-is-amenable`.

## 17. Status ledger

- **PASS.**
  - Simplicity: S4 and ingredients, NH, Grigorchuk A/B, imports.
  - The ladder: (L⇐), (L⇒) with both lemmas, (Σ⇐), (M⇒), and the Σ⇒ lift lemma with its wiring.
  - Paradox side: Theorem P (three nodes), non-IBN, the groupoid no-measure theorem, the bridge, unperforated purity, char-0
    dichotomy, Lemma C and linear images (credit to older nodes), Theorem S, Corollary S2.
  - The sandwich with `d(R)`, first-stage containment, the congruence-invisible step, the Toeplitz extension object, transient
    firewall, Conley lemma.
  - Measure side: the Tarski chain, char-0 rank function, all measure-side ring theorems, the Kerr–Nowak import, torus
    criterion, divergence, descent, inflation and its corollary, Følner rank models, Elek (PRIOR), growth and complexity rank
    models, Labbé complexity, Theorem T, the 𝔑 propositions, RF-group Toeplitz, ℤ² non-RF.
  - The free-group and virtually-free flagships.
  - Objects: boundary families (Theorem B, Families T/P, Theorem G, KP, odometer Nekrashevych), `F_2` paradoxical subshifts and
    their groups, boundary nonsofic and stable, the middle rung.
  - Traces T0–T5 (credit fixes); `C*_r` measure-free not MF; the not-PMF and permutation-vector firewalls; full-groups bridge;
    `K_1` face; complexity; coarse face; the calibration rows; the low-rank firewall nodes.
  - Markings, word problems and continua: PASS, but SUBSUMED in substance.
- **Unreviewed:** Proposition R (M⇐ correct form, un-m-converse); the Toeplitz middle-regime theorem; the orbit-equivalence
  Theorem G; the (RR_k) reduction text.
- **OPEN:** the root, (Σ⇒), (M⇐), and every item in §16.

## 18. Credits and novelty

- **Carried prior work:**
  - Ershov–Jaikin-Zapirain;
  - Steinberg, BCFS, Clark–Edie-Michell, CEPSS;
  - Stepanov 1997;
  - Beuter–Gonçalves 2018;
  - Clark–Sims;
  - Rainone–Sims, KMP, ABBL, Goodearl–Handelman;
  - Larki;
  - Kerr–Nowak (Thm 5.2, **Lemma 5.1**) and Ma;
  - Grigorchuk–Medynets;
  - Elek, **Arzhantseva–Păunescu Cor 11.15**, Ara–Claramunt;
  - Gao–Jackson–Seward;
  - Abels;
  - Schafhauser and Rainone–Schafhauser;
  - Kirchberg 1994, Ozawa, Brown Mem. AMS 184;
  - Magee–de la Salle;
  - Vershik–Gordon, Malcev, Elek–Szabó;
  - Ara–Goodearl–Pardo, Ara–Brustenga–Cortiñas, Matui;
  - Spielberg 1991;
  - Exel–Pardo;
  - **Zel'manov 1985**;
  - Conley;
  - **OpenAI 2026-08-01** (the first nonsofic group).
- **Older in-repo nodes that subsume swarm nodes:**
  - `compression-defect-dies-in-finite-dimensions`, `locally-residually-finite-targets-kill-compression-defects` and
    `zariski-envelope-compression-rigidity` (Lemma C theorems);
  - `subshift-elementary-group-word-problem-degree` and `binary-subshifts-embed-in-three-marked-kazhdan-groups` (continua and
    degrees);
  - `stw10-kazhdan-full-group-traces-are-qd` (trace collapse);
  - `halvable-corner-makes-projective-elementary-groups-nonsofic` (boundary nonsoficity);
  - `free-minimal-crossed-products-are-simple-with-rank-models` (free rank models).
- **Bounded novelty.**
  - **NEW (bounded):**
    - the free and virtually free dichotomies as group-level statements;
    - the local-annihilation criterion as stated;
    - the threshold corollaries;
    - the target-agnostic Lemma C and the Zariski proof over arbitrary fields;
    - the linear-images composition;
    - the Toeplitz extension object;
    - the `F_2` paradoxical subshift families;
    - the Σ⇒ lift and firewall.
  - **New example, not a first:** `S_∂`.
  - **FOLKLORE:** ring Tarski, Theorem S, the Weyl and group-ring calibrations, stability ⟺ nonsofic.
  - **PRIOR:** MF traces, the Kazhdan trace collapse, `K_1` formulas, full-group LEF, the crossed-product dictionary, Elek's
    rank-model theorem.
- **Before public framing:** decide local annihilation versus Stepanov's condition (b), and read Vaserstein LNM 854. MathSciNet
  and zbMATH were not reached by any novelty pass.
