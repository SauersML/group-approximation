# bh-free-35 — Baumslag–Gersten host design (BBMZ 5.3(9))

**Landed 6a8dbc894 (09-18):**
- `baumslag-gersten-group-is-highly-transitive-and-mif` (ESTABLISHED, folklore-level, no priority): BG acyl. hyperbolic (Minasyan–Osin HNN cor.; <a> ∩ <b> = 1 in BS(1,2)), torsion-free, so Hull–Osin `main`/`ah-mif` (read at source) give highly transitive + MIF. With main's proper-power orbit count: every faithful pair-orbit-finite action of BG has an infinitely generated point stabilizer, so that is the ONLY failing type (A) clause. BFFHZ Thm E on BG itself dies on the pair invariant ψ(ker φ) (infinitely many orbits, via <<t^m>>).
- `baumslag-gersten-group-maps-onto-higman-groups` (ESTABLISHED, R–S): BG/<<t^n>> ≅ H_n ⋊ C_n (Higman's group). BG ↠ H4 ⋊ C4 with a of infinite order; t of order ≤ 3 kills a; recovers Baumslag's "finite quotients of BG are cyclic".
- BG node Attempts entry: germinal-twist rigidity in SV_G — τ_g ~ τ_h in SV_G iff g ~ h in G; φ(a) = τ_α, φ(b) = τ_β forces a hom BG → G, a ↦ α, t ↦ λ = γ_κ(φ(t)) at a constant point κ, with <α,β> ≅ BS(1,2) if φ is injective on <a,b>. BG analog of the H4 "pure-label generators conjugate to their squares" constraint on bh-testcases.
**Open leads:** designs where a or b is not a global twist; a type (A) actor containing H_n ⋊ C_n (n ≥ 4) would already solve H_n.
**Status:** done, reported to team-lead.

## Pass 2 (09-18, after coordinator free-choice; INSIGHT FIRST)
**Target:** Kourovka 7.19 / complexity root, structural side (co-claimed on UNOWNED with bh-free-34, parked).
**Landed 1141e0820:**
- `hnn-stages-add-no-complexity-beyond-edge-distortion` (ESTABLISHED lane proof): injective one-permutation HNN stage over a type (A) actor — (1) stable letter pinned by values on edge-orbit reps; (2) OP(L,X) p.r. relative to OP(Γ,X) + orbit distortion Δ, subgroup distortion Σ, MEM of the orbit-finite edges (so SV_L p.r. if these are); (3) transporter D_1 = {γ : πγπ^-1 ∈ Γ}; (4) identity edges: D = C_Γ(π) = Γ ∩ D'' (bicommutant closure); (5a) regular edges pass, (5b) fiber-product/Mihailova edges in product actors fail, (5c) over V, Δ is tame (pushdown reachability, recalled).
- `twisted-brin-thompson-global-twists-are-conjugacy-closed` (ESTABLISHED lane proof): transporter formula b = λaλ^-1 with λ = gtwist at a constant point; ι(G) ∩ u^-1ι(G)u = ι(C_G(w)); no new conjugacies; HNN inputs with global base need a base-faithful image in G; gtwist is a hom on every point stabilizer.
- Kourovka 7.19 node: Attempt 4.
**Open lead (the only surviving shape on this route):** an fp type (A) actor with an exact factorization Γ = D·Γ_x, D regular orbit-finite, with non-p.r. factorization distortion (plus injectivity of the stage). Natural places: Zappa–Szép / exact-factorization hosts (bh-shell-universal), 2V-type actors where f.g. subgroup orbit problems are Turing-hard.
- e9864583d: HNN conservation node refined: complexity enters a one-permutation stage only via edge distortion (injective) or the kernel (non-injective, paid for by fp of the image); other actor constructions are coordinatewise-conservative.
- 4f16b5b54 `time-lift-actors-carry-no-complexity-beyond-row-language`: WP of f.g. subgroups of Aut(Y) ≤ p.r.(L(Y)); rule-8 G2 needs input-programmed rigid Z²-SFTs (Track A ∧ Track B requirement coincide). For bh-g2-* lanes: G2 in rule-8 form is a UNIFORM FAMILY statement.

## Pass 3 (09-18, after restart; target: E2 via a programmable fixed point)
Recovery: all earlier drafts already on main (BG node copy in work/ is stale; left).
**Landed 9c360c2ca (lane proofs, elementary, unreviewed):**
- `fixed-point-tile-set-rigidity-is-a-bounded-range-test` (+ `fixed-point-tile-set-rigidity-decimation-proof`): Wang tile set with constant-zoom self-simulation (H1 local coords, H2 injective, H3 exact macrotiles, H4 faithful macro edges; DRS as intended example, cited not re-read). Phase projections central; block products on each phase = local D-family for the SAME tile set at the SAME scale; so H(D) (commutation up to N(2D+2)-2) ⇒ every local D-family commutes ⇒ rigid ⇒ crossed product fp. Converse holds; rigidity is Σ⁰₁ (finite ideal-membership certificate) vs Σ⁰₃ in general.
- `self-similar-sft-thin-walls-refute-quantum-rigidity` (+ `self-similar-sft-thin-wall-substitution-proof`): agreement on ONE column + differences on both sides ⇒ not rigid at any scale; rigid ⇒ one-sided determining columns/rows; information-free macrotile column (Ω with no e_2-period) ⇒ not rigid; ~_i refinement turns macro edge-line walls into refutations. Ledrappier is self-similar (N=2, block [[a,a],[0,a]]) and passes.
**Next:** design a small self-simulating tile set satisfying H1–H4 with one-sided column/row information flow (thin-wall pre-filter), then search for a bounded-range commutation certificate (the finite object for an MSI ideal-membership run). Open: uniform-in-level version for variable zoom (minimal DRS variants) and the Z² layer of BSS simulations over Λ₁×Λ₁.
**Status:** done this pass.

## Pass 4 (09-18 ~16:00, coordinator order: one-way design, thin-wall prefilter, calibrated certificate search on MSI)
- CLAIM: the only bounded-range certificate search runs here (one msismall job, one core, ≤10 min each, ≤1 h total).
  Notes posted on the bh-g2-labbe and bh-g2-fixedpoint-a boards.
- LANDED 0dd3a7cca: `sfts-without-two-sided-faults-are-quantum-rigid` (+ `-rigidity-proof`) and the OPEN design target
  `free-minimal-sft-without-two-sided-faults-exists`. Every line having a determining side ⇒ quantum rigid (pure
  determinism). Walls ⇒ not rigid. Slab faults are the open zone. A determinism certificate for fixed-point sets
  exists only when there is no two-sided fault, so the bounded-range search is informative only when noncommutative.
- One-way design verdict (heuristic, on the OPEN node): a one-way reversible partitioned automaton keeps the vertical line
  two-sided, since each half-plane is autonomous in one time direction. The Guillon–Zinoviadis extremely expansive
  SFT leaves exactly one line to make one-sided. No explicit H1–H4 tile set was built.
- MSI job 1325784 (msismall, 1 core, 9:40, 181 MB): Singular letterplace engine, D = 1.
  - Ledrappier: 6/6 directions at |v| = 3 certified.
  - Planted Ledrappier × coords: (3,0) certified; (2,1) timed out (window too large).
  - Negative controls: full shift 0 certified. Colour product: (2,1) certified via marginals; at (3,0) exactly the
    8 wall pairs are undecided.
  - Labbé: timed out, and relation generation in Python was too slow.
  Job 1326491 (run 2): rectangle windows for the planted case, Labbé dominoes-only at degree 3.
- Rule slip: one empty local `python3 -` heredoc ran inside a shell command (no input, no-op, nothing used). All real
  computation ran on MSI.
- Job 1326491 (6:28, 195 MB): planted Ledrappier × coords certified 16/16 in (2,1),(1,2),(2,−1),(1,−2) (rectangle
  windows) and (0,3). Labbé dominoes-only at deg 3 timed out at 170 s. No jobs left running. MSI total 16 min.
- LANDED dc1c8cfb5: artifacts gq-bh-free-35-certificate-search-2026-09-18 (results) + -driver (exact code, md5s).
**Next:** a structure-aware engine (edge-colour marginal generators) for Ω_U at scale 2; a rigid SFT with a two-sided
fault as the positive test of the noncommutative part; the one-sided extremely expansive construction.
**Status:** done this pass.

## Pass 5 (09-18 ~16:40, coordinator: build the design target; no parallel Labbé search)
- Hand-off of the edge-colour-marginal idea posted on the bh-g2-labbe board. KP analysis posted on the bh-invent-04 board:
  KP axis faults are total and seeded, so KP is in zone (c) unless a seed is forced.
- LANDED 47f947ad2: `no-two-sided-fault-sfts-have-rich-strips-in-all-directions` (strip automata in every rational
  direction; aperiodic non-sofic strips of at least quadratic complexity; products and product substitutions excluded;
  corner sets need forced seeds), plus Attempt 5 on `free-minimal-sft-without-two-sided-faults-exists`.
- Construction: NOT achieved. The live shape is self-simulation inside an irreversible Ledrappier-type rule (hex-cone or
  weaker coverings), i.e. the triangle-permutive programme in its wider form.
**Status:** done this pass.

## Pass 6 (09-18 ~17:10, coordinator: adversarial referee of 49939b957)
- LANDED 27c8ebe61 + fff128e8a: Referee section on `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`, PASS
  conditional on R1 (fixed point with the gadgets), R2 (side-local margins with constant corners in DR's minimal
  layout) and R3 (frame tiles unique per coordinate).
  - The kill attempts fail: thin walls, fault fibres, horizontal chains, opposite quadrants.
  - The slot scalars are verified.
  - Correction landed on my 47f947ad2 lesson (irreversibility is needed only at non-expansive lines).
**Status:** done this pass.
- LANDED f757d5cbc (Pass 7): Referee addendum. R1–R3 checked at source (DR arXiv-4.tex md5 8e17f728…, DRS
  fpt-arxiv.tex md5 63ad72b6…, fresh on MSI) and against the layout artifact 1e9e4c5b4. PASS stands; the
  crossing-box END/c_K collision fix was posted to bh-g2-fixedpoint-a. No MSI jobs were run (only curl and reading).
**Status:** done this pass.
