# gq critic pass 1 (2026-09-17, ~23:00 CDT)

Lane `gq-critic`. Read: all 59 boards in `$GQ/board`, the 26 landings in `$GQ/state/landed.log`, and the status
lines of the gq nodes on origin/main (up to 917e91b63). No claims of my own. Node ids are backticked.

## 0. Summary

- **The swarm has produced about 20 obstruction and reduction nodes and 0 constructions.** Of the obstructions:
  - roughly a third kill *natural* (standard-action) copies of GL_n(Q), which `gq-heretic` H3 shows decide
    nothing;
  - the abstract ones are O1–O4, `lifts-add-no-unipotent-divisibility`, `bffhz-closures-cannot-create-gl-n-q`,
    `proper-semisimple-cat0-groups-contain-no-gl-2-q`, `extension-product-closures-cannot-create-sl-n-q`
    (gq-union-alt, landing), and `circle-groups-with-divisible-free-germs-omit-gl-n-q` (gq-deep-pp-1, landing).
- **Only three kinds of operation can create GL_n(Q) at all.** gq-union-alt's closure class P_n = {H : every
  SL_n(Q) → H trivial} contains every Q-free group and every BS(1,4)-free group. It is closed under subgroups,
  extensions, products, free products and wreaths. So GL_n(Q) can only come from:
  - (U) directed unions (then the fp problem is the whole difficulty);
  - (E) graphs of groups with **nontrivial** edge groups;
  - (T) Thompson-type completions: SV_G, V_d(G), germ extensions, nV, RSGs.
  Every construction lane must say which of U/E/T it uses.
- **The root needs infinitely many n** (`gl-n-q-targets-are-cofinal-in-n`), so any host must contain SL_3(Z).
  About 8 lanes work at n = 2 only: sl2q, va-gl2, va-affq, affq, pp-psl2q, pp-lift, bt-kojima, heis-q. That is
  fine for stepping stones, but no construction lane checks SL_3(Z)-compatibility. **Rule proposal:** every
  construction must say where SL_3(Z) sits.

## 1. Construction mechanisms that survive every landed obstruction

Checked against O1 (no residually finite overgroup), O2/O3 (V, VA), O4 (distortion),
`lifts-add-no-unipotent-divisibility`, `bffhz-closures-cannot-create-gl-n-q`,
`proper-semisimple-cat0-groups-contain-no-gl-2-q`, P_n closure, and natural-action kills (which do not apply to wild
embeddings).

**M1 — twisted Brin–Thompson / nV with Kojima–Sheng towers plus prime dilations.** Class T.
- *Ingredients.* Q ≤ nV for n ≥ 2 (Kojima–Sheng arXiv:2603.18410v3). `gl-n-q-generated-by-gl-n-z-and-prime-dilations`
  (624b0aee3) gives GL_n(Q) = ⟨GL_n(Z), e_p⟩ with commuting e_p.
- *Design.* Take SV_Γ with Γ ⊇ GL_n(Z) f.p. of type (A); this carries SL_3(Z) with no nV question. Build commuting
  elements e_p in SV_Γ that realize the dilation relations on a Kojima–Sheng tower, i.e. the relations of the
  generation lemma.
- *Obstruction status.* Survives all landed obstructions: nV and SV_Γ are not RF, not VA, and their elements are
  not globally linear, so the natural kills do not apply.
- *Decisive tests, both repo nodes:*
  - `bs12-embeds-in-brin-thompson-2v` (OPEN), constrained by the ESTABLISHED
    `bs12-images-in-nv-have-logarithmic-table-length` and
    `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`;
  - `almost-automorphism-conjugate-to-proper-power-is-equicontinuous` (ESTABLISHED) for V_d / almost-automorphism
    hosts.
- *Gap.* No lane has read these four nodes: gq-bt-kojima's and gq-nv-obstruct's boards are still empty.

**M2 — graphs of groups over nontrivial RF edge groups.** Class E.
- *Ingredients.* Q = Z_(ℓ)[1/ℓ], so SL_2(Q) = SL_2(Z_(ℓ)) *_I SL_2(Z_(ℓ)) with I the Iwahori (Ihara/Serre).
  SL_n(Q) acts on the ℓ-adic building with vertex groups SL_n(Z_(ℓ)). These are RF, since they lie in SL_n(Z_ℓ), so
  O1 does not bite at vertex level. The action is not proper, so the proper-CAT(0) kill does not apply. BFFHZ closures
  have trivial or free edges, so `bffhz-closures-cannot-create-gl-n-q` does not apply either. gq-typeA-bffhz spark
  (a) says the same.
- *Needs.*
  - (i) SL_n(Z_(ℓ)) ∈ B_A or in an fp simple group. This is countable and not f.g., so it is itself open.
  - (ii) A BLIW-type permanence for this tree or building. The repo has `bh-embeddability-survives-decidable-edge-hnn`
    (OPEN), the natural home.
- *Owner.* gq-infinite-primes has this decomposition but asks for a partner, and none has answered.

**M3 — ring hosts R ⊇ Q built from an inverse number (carry) operator.** Class U, then fp.
- *Ingredients.* gq-deep-ring-1 (Toeplitz u, u*, d = diag(1/(k+1))) and gq-malcev-ring (Leavitt x_i, y_i and
  D = 1/(1+#leading ones)) both give an explicit **f.g.** ring R ⊇ Q, hence an explicit f.g. E_N(R) ⊇ GL_n(Q).
  `leavitt-unit-groups-over-every-field-are-simple-mod-scalars` gives a simple countable Λ = L_Q(1,2)^x/Q^x
  containing GL_∞(Q).
- *Why it survives.* The obstructions are about hosts, not about R. `infinite-field-leavitt-units-are-not-finitely-generated`
  and gq-deep-ring-1's integral-forms obstruction only kill f.g. subrings of K⊗B_0. The carry operator is not of that
  form.
- *Why it matters.* This is the only line with an actual f.g. construction containing GL_n(Q), and the best G′
  (Problem 2.7, "natural") candidate.
- *Needs.* A finite presentation of R and of St_N(R), a K_2 computation, and simplicity of PE_N(R).

**M4 — ample groupoids / expanding-map groups (COLD, untried).**
- *Idea.* Topological full groups of the ×p groupoids on solenoids, in the spirit of Nekrashevych's finitely presented
  groups of expanding maps (survey ref [Nek2]; Matui's fp simple groups of Cuntz–Krieger groupoids). Q^x acts by
  expanding automorphisms on the solenoid dual to Q, and Q by translations.
- *Status.* No lane touches it. It escapes the natural kills only if the Q-action is wild, so this needs care.

**M5 — contracting RSGs / the rational group R, and outer extensions.** Class T.
- *Open questions.* Does a full contracting RSG, or R, contain (Q,+)? (gq-map S5 and S6; gq-lit-arxiv says nobody has
  asked.) The outer-extension form (`decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`) collapses for
  simple SL_m(Q) to "SL_m(Q) ≤ fp Q ↪ Out(S)" and so connects to S5 (Out(V) ⊂ R).
- *Probably dead for n ≥ 3* by §2 G1 below. Test that first.

## 2. Gaps

**G1 — the missing ABSTRACT obstruction (answers heretic H3): FW for SL_n(Q), n ≥ 3.**
- *What the repo already has.* `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` and
  `fw-subgroups-of-eventually-similar-groups-virtually-embed` (both ESTABLISHED) say that FW subgroups of RN /
  eventually-similar hosts virtually embed in finite products of local vertex groups. Survey Remark 4.12 is the
  cube-complex version.
- *What FW would give.* If SL_n(Q), n ≥ 3, has property FW (every commensurated subset transfixed, equivalently
  bounded orbits on CAT(0) cube complexes), then it has no proper finite-index subgroups, so SL_n(Q) itself lands in a
  vertex group. With RF local groupoids this contradicts O1. That kills, for **every** embedding, not only natural
  ones: RN groups, RSGs with synchronous or RF local actions, germ extensions with cube complexes, and every host whose
  relevant stabilizers are RF.
- *Where to look.* First check Cornulier arXiv:1302.5982 for FW of SL_n over fields. Otherwise prove it: SL_n(Q) is
  boundedly generated by root subgroups (Q,+); each needs relative FW, e.g. uniformly over (SL_2(Z[1/m]) ⋉ Z[1/m]^2,
  Z[1/m]^2).
- *Why it's decisive.* It decides whether M1 (nV / SV_Γ) survives for n ≥ 3: do nV or SV_Γ act on CAT(0) cube
  complexes with RF or proper stabilizers? Nobody has this.

**G2 — hypotheses and landed lemmas no construction uses.**
- `gl-n-q-generated-by-gl-n-z-and-prime-dilations` (624b0aee3) → M1.
- `type-a-orbit-accumulation-forces-fg-nontrivial-germs` (ae52139fe): in any type (A) action the germ group at an
  accumulating point is f.g. and nontrivial. Nobody has combined it with O1 and divisibility, i.e. with what the germs
  of (Q,+) must be.
- `gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups` (ESTABLISHED): nobody asks which uniformity turns this into one
  host.
- The 2-transitive and sharply 2-transitive actions (PGL_2(Q) on P^1(Q); Aff(Q) on Q). The strong form of
  `pgl-q-projective-type-a-extension` needs only a finitely presented Γ ≤ Sym(P^{m-1}(Q)) containing PGL_m(Q) with
  f.g. point stabilizers. gq-houghton-q (Alt_fin form) and gq-typeA-projective (subgroup form Λ) should split
  explicitly.
- `permutational-host-forms-agree-for-countable-inputs` is the load-bearing equivalence for all type (A) lanes and is
  unreviewed.

**G3 — known cases never checked.**
- *Known fp simple groups containing BS(1,2)* (self-similar RN groups; Bartholdi–Šunik/Zaremsky), *Q* (VA, nV) and
  *SL_3(Z)* (Scott Sc(3)). Nobody asks for one fp simple group containing two of them at once. **Proposed ladder**
  (gq-heretic's minimal test):
  1. Q ⋊_{×2} Z;
  2. Q ⋊ Z^k (k primes);
  3. Aff(Q);
  4. Aff(Q) together with SL_3(Z).
  Not all rungs are on a board yet.
- Witte Morris / Ghys (1-manifold actions of SL_3(Z) subgroups) is an import, not new (gq-deep-pp-2). Land it as a
  citation node.

**G4 — families never tried.**
- Ample groupoids / topological full groups (M4).
- Operator algebras: gq-cuntz-cstar has NO board.
- Cohomological / Brown-criterion finite presentation of an actual candidate (gq-pp-fp has no candidate).
- Abstract commensurators (Comm(SL_n(Z)) = PGL_n(Q) ⋊ Z/2 for n ≥ 3; Comm(Z^n) = GL_n(Q)): a natural G′ idea,
  sparked by gq-k2-q and gq-explicit-fp and taken by nobody. gq-explicit-2 has NO board.
- The adelic building / restricted product of Bruhat–Tits trees (median graph with stabilizers SL_2(Z); gq-sl2q
  spark). The action is non-proper, so it is a live E-type host shape.

## 3. Duplicated effort

- **D1: "natural piecewise hosts omit GL_n(Q)", proved ~6 times.**
  - Landed: `piecewise-commutative-linear-hosts-miss-linear-gl-n-q` (443aa4795),
    `fg-piecewise-linear-hosts-omit-natural-gl-n-q` (e0cfca2b7), `germ-extensions-omit-standard-gl-n-q`
    (4a58a2b5b).
  - In progress: gq-pp-psl2q's analytic-continuation result, gq-sl2q sig 1, and gq-pp-fp's first step.
  - Recommend: stop all further natural-action obstructions, and have gq-integrate cross-link `distinct_from`
    (fg-piecewise-linear and germ-extensions do not list each other).
- **D2: Aff(Q)/GL_2(Q) not in Brin's A / Aut(F).** This appears as `aff-q-does-not-embed-in-aut-thompson-f`
  (1d1ec4d78), in `gl-n-q-explicit-natural-fp-overgroup` Attempts 1, and in gq-pp-psl2q's spark. All three are
  subsumed by O4, since A ≤ VA. Keep them as independent proofs, but they are not new obstructions.
- **D3: cofinality and simplicity reductions, four nodes from three lanes:**
  - `gl-n-q-targets-are-cofinal-in-n` (typeA-design);
  - `sl-odd-q-simple-inputs-for-gl-n-q-root` (reform-countable);
  - `gl-n-q-root-needs-only-nontrivial-psl-maps` (borel-q);
  - `sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially` (reform-countable).

  The borel-q node and the sl-odd-q node do not list each other in `distinct_from`. gq-borel-q never started its
  Curtis–Tits assignment.
- **D4:** gq-deep-ring-1's construction ≈ gq-malcev-ring's (a number or carry operator in a Leavitt/Toeplitz ring).
  gq-deep-ring-1's obstruction generalizes part 3 of `infinite-field-leavitt-units-are-not-finitely-generated`.
- **D5:** gq-union-obstruct's planned tree and product-of-trees kills ≈ `gl-n-q-fixes-a-vertex-in-free-splittings`
  (typeA-bffhz) plus `proper-semisimple-cat0-groups-contain-no-gl-2-q` (heretic).
- **D6: VA lanes after O4.** gq-va-gl2's first step *is* O4. gq-q-in-germs is VA anatomy, now low value.
  gq-germ-necessary overlaps gq-germ-design (the normal-germ SL_3(Z) node).
- **D7: four lanes converge on Aff(Q) and BS(1,2) in nV** (affq, va-affq, bt-kojima, nv-obstruct). Three of the four
  boards are empty.

## 4. Status honesty and process

- About 15 load-bearing ESTABLISHED nodes are "lane-proved, not refereed", while all three referees sit idle with no
  requests. The rules only require referees for stepping stones, but the obstructions now steer the whole swarm.
- gq-calibrator has landed no calibration artifact.
- Boards still missing: gq-cuntz-cstar, gq-explicit-2. Boards still empty: bt-kojima, nv-obstruct, affq,
  ring-fp-simple, obstruction-miner, bhm-pattern, heis-q, houghton-q, q-in-germs, tbar-lift-n, rn-varying-degree.
- The Kourovka 14.10 text has not been read at source (gq-transfer calls it a trust surface; gq-explicit-fp needs it),
  and neither has Brin 1996's description of A (gq-explicit-fp needs it).

## 5. Suggested reassignments (proposals to team-lead)

**M1: nV / SV_Γ with prime dilations.**
- **gq-bt-kojima:** BS(1,2) ≤ 2V constructively on a Kojima–Sheng tower. Read the four repo nodes in M1 first; the
  first test is the log-table-length constraint.
- **gq-nv-obstruct:** SL_3(Z) ≤ nV (Zaremsky 2.19(c)/(d)). Also: do nV and SV_Γ act on CAT(0) cube complexes with
  RF or proper stabilizers? That links to G1.
- **gq-affq:** the G3 ladder Q ⋊_{×2} Z → Q ⋊ Z^k → Aff(Q) inside some SV_Γ, using the sharply 2-transitive action
  on Q, or gq-typeA-alt's single-coordinate root lemma.
- **gq-scott-union** (done) with **gq-k2-q** (done): the presentation-level M1 target, i.e. an fp group containing
  GL_n(Z) and commuting e_p with the generation-lemma relations.

**G1: the abstract obstruction.**
- **gq-obstruction-miner:** FW for SL_n(Q), n ≥ 3 (Cornulier first).
- **gq-va-gl2** (VA done by O4): apply FW-transfer via `fw-subgroups-of-eventually-similar-groups-virtually-embed`
  to RN groups, RSGs and germ-extension cube complexes.
- **gq-q-in-germs:** switch to M5 (is Q in R, Out(V), or a contracting RSG?). Test it against G1 first.

**M2: graphs of groups over nontrivial edges.**
- **gq-union-obstruct** (planned kills duplicate D5): partner gq-infinite-primes on BLIW-type permanence with
  non-f.g. RF vertex groups (`bh-embeddability-survives-decidable-edge-hnn`).
- **gq-sl2q:** the Ihara amalgam SL_2(Q) = SL_2(Z_(ℓ)) *_I SL_2(Z_(ℓ)) and the adelic-building median graph. Drop
  sig 1 (D1).
- **gq-typeA-bffhz** (done): its own spark (a), HNN over nontrivial f.g. edge groups with growing multipliers
  inside B_A.

**M3: ring hosts.**
- **gq-malcev-ring:** owns the carry-operator ring construction and E_N(R) ⊇ GL_n(Q) (the G′ candidate).
- **gq-deep-ring-1:** owns the general integral-forms obstruction, and embedding R in a finitely presented ring
  (Bokut, EMN).
- **gq-en-ring:** St_N(R) and K_2 finite presentation for that R.
- **gq-pp-fp** (no pp candidates left): Brown-criterion specialist for M1 and M3 candidates.

**M4: ample groupoids and expanding-map groups.**
- **gq-solenoid** (done; knows the adelic models): topological full groups of ×p groupoids on solenoids.
- **gq-cuntz-cstar:** if alive, joins M4 through the Cuntz–Krieger groupoid dictionary.

**G′ (Problem 2.7).**
- **gq-explicit-2:** abstract commensurators (Comm(SL_n(Z)), Comm(F) of Burillo–Cleary–Röver).
- **gq-explicit-fp:** stays on host classes, now pointed at M3.

**Stop or redirect (D1–D3).**
- gq-pp-psl2q's natural result is subsumed; gq-deep-pp-1 already adopted its abstract part.
- gq-borel-q: back to Curtis–Tits amalgam permanence, with no more cofinality nodes.
- gq-germ-necessary: coordinate with gq-germ-design, targeting aperiodic germ groups.

**Referees** (idle; review the load-bearing obstructions and reductions).
- **gq-referee-a:** `permutational-host-forms-agree-for-countable-inputs` and
  `type-a-orbit-accumulation-forces-fg-nontrivial-germs`.
- **gq-referee-b:** `lifts-add-no-unipotent-divisibility`, `germ-extensions-omit-standard-gl-n-q` and
  `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`.
- **gq-referee-c:** `gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups`,
  `sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially` and `bffhz-closures-cannot-create-gl-n-q`.

**Literature, calibration and graph health.**
- **gq-lit-arxiv:** the Kourovka 14.10 text at source; Cornulier FW for SL_n over fields.
- **gq-lit-hosts:** the Brin 1996 description of A.
- **gq-calibrator:** land the calibration artifact now, adding T10 "where does SL_3(Z) sit?".
- **gq-integrate:** cross-link `distinct_from` for the D1 and D3 clusters.

**Rules.** Add to RULES §1:
- the root needs infinitely many n, so every construction must contain SL_3(Z);
- every construction names its class (U, E or T);
- no further natural-action obstructions.
