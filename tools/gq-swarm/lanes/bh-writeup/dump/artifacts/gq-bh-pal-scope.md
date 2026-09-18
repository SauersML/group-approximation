# Palomar BH megasubmission: which solved open problems go in, and what each costs in Lean

Lane `bh-pal-scope`, 2026-09-18, read at origin/main `2143f2ef3`. This is a scoping artifact,
not a claim. The scope rule is the user's (09-18): only printed open problems that this repository
solved and that the literature has not, with no literature-only results. Everything listed as a
solution here is a lane result on main, and priority searches were bounded (arXiv only; no
MathSciNet or zbMATH).

Sources for status and printed wording:
- `gq-bh-bh-lit-survey.md` (bh-lit, d7b638fef);
- `gq-bh-bh-map-subgraph.md` (bh-map, f0965b866);
- `gq-bh-bh-bbmz-problems-status.md` (bh-bbmz-problems, e1b8dd9a7);
- `gq-bh-bh-verify-{metabelian,linear,artin}-report.md`;
- `gq-bh-palomar-plan.md` (29f374a9b);
- `gq-bh-bh-lit-lean-ecosystem.md` (f9c8e7c95).

"Lit inputs" means published theorems that an unconditional Lean proof must also formalize.
They are unavoidable, because Palomar accepts no hypotheses. The user's "no literature" rule
limits the **submitted theorems**, not the inputs of their proofs.

## 1. Recommended theorem list (tiers by value times feasibility)

### Tier 1: printed, solved here, feasible

**T1. Kourovka 14.10(c) (P. de la Harpe, active in the 2026 issue) = BBMZ Problem 2.7.**
- **Node:** `gl-n-q-explicit-natural-fp-overgroup`. ESTABLISHED and refereed here, as an
  explicit construction; whether it is "natural" is a matter of taste. The GL_n(Q) node itself
  stays open.
- **Result:** St_10(R_L) is an explicit f.p. group containing every GL_n(Q). R_L is the ring with
  6 generators and 9 relators.
- **Priority:** Mikaelian 2507.04347 §1.4 only announces a non-natural overgroup, with no
  construction.
- **Challenge sketch (Mathlib-only):** `R_L := RingQuot (FreeAlgebra ℤ (Fin 6)) rel`, with the 9
  relators written out, and `SteinbergGroup n R := PresentedGroup` on the symbols `x_ij(r)`, with
  the standard relations. Then
  `theorem explicit_fp_overgroup_of_all_gl_n_q : Group.IsFinitelyPresented (SteinbergGroup 10 R_L)
  ∧ ∀ n, ∃ f : GL (Fin n) ℚ →* SteinbergGroup 10 R_L, Function.Injective f`.
  The shared definitions come to about 60 lines.
- **Lean chain:**
  1. St_N(R) is f.p. for f.p. R and N ≥ 5 (the repo's own direct proof,
     `steinberg-groups-of-fp-rings-are-fp-in-rank-five`, refereed);
  2. R_L and a unital Q → R_L, whose injectivity needs a faithful R_L-module;
  3. the Leavitt-pair centralizer embedding `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`
     (part 2), all n into St_10;
  4. injectivity through E_10(R_L) ⊆ GL_10(R_L).
- **Lit inputs:** none beyond standard Steinberg relations.
- **Existing Lean to reuse:**
  - `Manuscript/SimpleKazhdanSofic/LeavittFP/` (`KMGroup`, `kmGroup_isFinitelyPresented`,
    `steinbergLeavitt_isFinitelyPresented`, `SteinbergIso`, `CommutatorCalculus`,
    `WordCalculus`);
  - `Manuscript/SimpleKazhdanSofic/Full/LVH2GL3/RankFive.lean`;
  - `BooneHigman/SteinbergBasic/`.
- **Size:** 3–6 kLOC new. It is independent of the other session's chain.

**T2. BBMZ Problem 5.3(7), and BHM 2407.03149 l.272 ("remains open for the class of finitely
generated metabelian groups").**
- **Nodes:** `fp-metabelian-groups-satisfy-boone-higman`, ESTABLISHED 09-13, with an internal PASS
  and bh-verify-metabelian's adversarial PASS (05d6a15ff). The f.g. form is T2 of the existing pair.
- **Challenge:** the existing pair `Palomar/MetabelianBooneHigman*`, merged verbatim:
  `fp_metabelian_embeds` and `fg_metabelian_embeds`.
- **Lean chain:** the other session's `GroupApproximation/BooneHigman/**` (bh-met lanes, very
  active). T1 needs the 10 gap Statements of `Metabelian/ChainWiredFrontierThree.lean`: van der
  Kallen stability, Suslin/Horrocks, Bruhat big cell, Higman V swap section, Röver–Nekrashevych
  relators, generic torsion in V perfect, and so on.
- **Lit inputs:** Zaremsky 2405.09722 Thm 1.1 (f.p. self-similar embeds in f.p. simple; this is
  the `FPSelfSimilarEnvelopeStatement` half), Wehrfritz 1975 quasi-linearity, and the classical
  K-theory above.
- **Size:** very large, but in progress in the other session. Our part is integration and taking
  unowned gaps.

**T3. Every f.g. linear group over any field.**
- **Status:** not itself numbered, but the literature stops at f.g. subgroups of GL_n(Q)
  (Zaremsky Thm 1.2), and it is the umbrella for T2 and T6.
- **Node:** `finitely-generated-linear-groups-satisfy-boone-higman`, ESTABLISHED, with
  bh-verify-linear's adversarial PASS (ac8c87777).
- **Challenge:** `fg_linear_embeds : ∀ (K) [Field K] (n) (H : Subgroup (GL (Fin n) K)),
  H.FG → EmbedsInFinitelyPresentedSimpleGroup H` (T3 of `Statement/Basic.lean`, verbatim).
- **Lean chain:** T3 ⇐ `LinearHostStatement` ∧ `FPSelfSimilarEnvelopeStatement`
  (`Products/Hosts.lean`). `LinearHostStatement` is undischarged. It needs:
  - char-0 coordinates to GL_N(Z[1/m][t̄]), which exist partly (`Coordinates/`, `CharZeroCoords*`);
  - char-p Nagata coordinates (`CharPCoords*`, `CharPHost/`);
  - the affine self-similar host R^N ⋊ E_N(R), f.p. via the rank ≥ 5 Steinberg and K_2 control
    (`ElemFP*`);
  - both self-similar state formulas.
- **Lit inputs:** as T2, plus Nagata normalization, miracle flatness and Quillen–Suslin.
- **Size:** medium-large, sharing T2's envelope half. New work is about 5–10 kLOC.

**T4. lean-eval `higman_infinite_simple`** (an open formalization problem, marked unsolved on its
page).
- **Note:** the mathematics is Hyde–Lodha's (Q₂). What is new is the first formalization.
  List it under "formalization firsts", not as a mathematical solution.
- **Existing:** `GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleClosed.lean`,
  `finitelyPresentedInfiniteSimple_closed` (closed, `#audit_closed_axioms`).
- **Work:** a bridge to lean-eval's exact statement via `exists_mulEquiv_presentedGroup`, plus the
  Mathlib version check (4.32.0 against 4.32.2).
- **Size:** 0.1–0.5 kLOC. This is the cheapest win.
- **Also:** state it in the megaconfig as
  `∃ (α) (rels : Set (FreeGroup α)), Finite α ∧ rels.Finite ∧ IsSimpleGroup (PresentedGroup rels)
  ∧ Infinite (PresentedGroup rels)`. The lean-eval submission itself is the user's to post.

**T5. Kourovka 17.59 (S. Kohl; unsolved in the 2026 issue): CT(Z) = RCWA⁺(Z).**
- **Node:** `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`, a lane proof (fc9c15d54),
  not reviewed.
- **Challenge sketch:** define the class transposition `τ : Equiv.Perm ℤ` inline, then
  `CT := Subgroup.closure (range τ)` and
  `RCWAplus := {g | (∃ m ≥ 1, ∀ r, ∃ a b c, c ≠ 0 ∧ ∀ t, c·g(r+tm) = a(r+tm)+b) ∧ g '' Ici 0 = Ici 0}`.
  `theorem kourovka_17_59 : (CT : Set (Equiv.Perm ℤ)) = RCWAplus`, about 40 lines.
- **Lean chain as proved on main:**
  - (⊆) is elementary.
  - (⊇) reduces to item 3 of `ct-p-z-is-a-one-vertex-k-graph-full-group`, that CT_P(Z) is the
    whole piecewise-canonical group. That item currently rests on Matui's `simple2`, Li's
    homology–abelianization sequence and FKPS homology.
  - **Recommendation:** first find an elementary proof that every piecewise-canonical box
    permutation is a product of class transpositions, by the V-style refine-and-swap argument.
    That removes every literature input.
- **Size:** 2–4 kLOC after the elementary proof exists. There is no RCWA or class-transposition
  Lean in the repo yet.

### Tier 2: printed and solved here, but large literature inputs

**T6. Exceptional spherical Artin groups E_6–E_8, F_4, H_3, H_4** (part of BBMZ 5.3(13); BFFHZ:
"remains open for the exceptional type spherical Artin groups"; survey Rem 5.4).
- **Nodes:** `spherical-artin-groups-satisfy-boone-higman` and
  `e-type-artin-groups-satisfy-permutational-boone-higman`. PASS from bh-verify-artin,
  conditional on T3.
- **Challenge:** `ArtinGroup M := PresentedGroup` of the braid relations of a Mathlib
  `CoxeterMatrix`, with E_8 etc. as literal matrices.
- **Lit inputs:** faithfulness of the Cohen–Wales / Digne (Krammer-type) representations. This is
  very large and the real cost.
- **Size:** T3 plus faithful linearity, 20+ kLOC. Defer until T3 closes.

**T7. BFFHZ Q3.1 (graph products of PBH groups are PBH): answered YES.**
- **Node:** `pbh-class-closed-under-graph-products`, a lane proof from 09-14, re-checked twice
  today (6ff495ba8, 1ed3a4de1).
- **Challenge:** inline the type (A) definition and the class B_A (subgroups of f.p. groups with
  a type (A) action), plus the graph product as a quotient of `Monoid.CoprodI` by commutation
  relations. This needs no fp-simple host, since the question is about B_A.
- **Lit inputs:** BFFHZ Theorems C and E (type (A) actions for `Aut_H(H*F(x,y))`-type actors)
  and Zaremsky Prop 5.5.
- **Existing Lean:** `GroupApproximation/TypeA2/` (from the FFWZ 5.8 pair) and
  `Algebra/GraphProduct.lean`.
- **Size:** 8–15 kLOC.

**T8. Kourovka 17.61 (S. Kohl; unsolved in the 2026 issue): CT_P(Z) is f.p. for finite P.** In
fact it is simple and F_∞.
- **Node:** `ct-p-z-is-a-one-vertex-k-graph-full-group`, a lane proof (fc9c15d54).
- **Challenge:** `IsSimpleGroup CT_P ∧ Group.IsFinitelyPresented CT_P`, with CT_P the closure of
  the P'-smooth class transpositions.
- **Lit inputs as proved:** Li 2110.04505 Cor. `OneVertex` (F_∞), Matui 1210.5800 `simple2`,
  Li 2209.08087 `AHConj`, and FKPS 1808.07807.
- **Recommendation:** a direct finite presentation, generalizing Brown's presentation of V to the
  mixed-radix box calculus. `GroupTheory/HigmanThompson/BrownPresentation.lean` exists to extend.
  Simplicity then follows from an Epstein-type argument; the repo has simplicity criteria.
- **Size:** 8–15 kLOC. The research step, an explicit presentation, comes first.

### Tier 3: excluded by the scope rule

These are solved here but answer no printed question, or are instances of a printed universal
question, or rest mainly on published theorems:
- B̃_n and C̃_n Artin (PBH). BFFHZ list them open, but C̃_n is one line from BFFHZ Cor B plus
  Charney–Crisp, and B̃_n needs the Li–Roushon fibration plus BFFHZ Thm A. The novelty is weak
  and the formalization is infeasible.
- Forest-type Artin groups (PBH form). Plain BH was already secondary-sourced.
- BS(1,3) ≤ 3V. No printed question; it does not answer Callard–Salo.
- A Juschenko–Monod group inside 2V (`smart-trace-full-group-embeds-in-brin-thompson-2v`). No
  printed question; it also needs SMART minimality (COT) and 2V f.p. and simple.
- Surface-by-free and free-by-free groups; ascending HNN extensions of free groups. Corollaries of
  BLIW Thm 11.1 / §12.5.
- Lodha's S with a type (A) action (1e64376ae) and circle PL groups T(l;A,P) (33f9eaf07). These
  are positive instances of Zaremsky Q5.13(i) and BFFHZ Q3.4, which ask about every f.p. simple
  group, so they answer neither. They also rest on Lodha's and Stein's theorems.
- Kourovka 17.60 for |P| ≠ |Q| only (partial; rests on Matui `iso2`).
- Kac–Moody lattices are PBH (Rybak MIF plus BFFHZ's own "in particular" clause, so literature).
- 2V_τ, the universal host DV_F, E^n × T lattices, RF soluble finite rank, and field-representable
  algebras.

## 2. Proposed Lean lane roster (disjoint paths; lander `gqland-lean.sh`)

| Lane | Target | Owns |
|---|---|---|
| bh-pal-surface | challenge, solution skeleton, model tests, config, gate tuples; yaml switched now (WIP) | `Palomar/BooneHigman*`, `Palomar/comparator-boone-higman.json`, `scripts/PalomarBooneHigman*`, `formalization.yaml` |
| bh-pal-integrate | root wiring, cyclecheck, liaison with the bh-met chain, Palomar check runs | root `GroupApproximation.lean` insertions |
| bh-pal-leaneval | T4 bridge and the lean-eval hand-off | `GroupApproximation/BHPalomar/LeanEval/` |
| bh-pal-stn-fp | T1(a): St_N(R) f.p. for f.p. R, N ≥ 5 | `GroupApproximation/SteinbergFP/` |
| bh-pal-rl | T1(b): R_L, faithful module, Q ⊆ R_L, Leavitt-pair embedding GL_n(Q) → St_10(R_L) | `GroupApproximation/SteinbergFP/Resolvent/` |
| bh-pal-linear-scout, then bh-pal-linear-char0, -charp, -assembly | T3: `LinearHostStatement` | `GroupApproximation/BooneHigmanLinear/` |
| bh-pal-met-join | T2: take unowned Frontier-Three gaps after checking the bh-met commit log | the gap files, via the GQ_BASE rule |
| bh-pal-kourovka59 | T5: elementary proof first (research node), then Lean | `GroupApproximation/ClassTransposition/` |
| bh-pal-kourovka61 | T8: explicit finite presentation research, then Lean | `GroupApproximation/ClassTransposition/Presentation/` |

**Deferred:** T6 (faithful Artin representations) and T7 (BFFHZ C/E). Launch them only after T1–T5
have green builds.

## 3. Notes

- Every Tier 1–2 item is still internally reviewed only, and formalization is the external check.
  Status lines on the Palomar surface must say "formalized"; they must not say "refereed".
- Surface rules (American English, no `research/*.md` references, credit wording) apply to
  every challenge docstring.
