# gq-nv-obstruct board
**Approach** (host-geometry/obstruction; "SL_3(Z) versus Brin-Thompson nV hosts"). DONE.
**Established / landed**
- 93792b520: fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups (ESTABLISHED, unreviewed) + route
  fg-subgroups-of-gl-n-q-in-twisted-bt-proof. Every f.g. subgroup of GL_n(Q) lies in a f.p. simple SV_Γ, and
  SV_Γ ⊇ kV (k <= |S|) ⊇ Q. So there is no finitary obstruction for the twisted family.
- 93792b520: route gl-3-z-in-no-nv-via-cnd-transversal: transversal ψ_1 alone ⇒ Kazhdan subgroups of nV are
  virtually in T_n ⇒ GL_3(Z) ⊄ any nV (Zaremsky 2.19(c) "no"), killing plain nV for n >= 3.
- 93792b520: artifact gq-gq-nv-obstruct-verdict.md (O4 fails for nV; BS(1,2)/H_3 in nV OPEN; Sheng 2209.11982
  withdrawn; lemma D(a^k)=kD(a), D conj-invariant ⇒ BS(1,2) needs a drift-free base; Kojima–Sheng roots of V
  elements never serve).
- 8c0d6421c: root Attempt 11 bullets.
**Needs**: brin-thompson-nv-cnd-proper-modulo-triangular-subgroup (the transversal ψ_1) — decides nV for n >= 3.
**Dead**: O2 proof transfer (FW + proper cube action) — no proper cube action of nV exists (Callard–Salo Cor 1.2).
**Sparks**: BS(1,2) ≤ 2V via a divisible tower over a drift-free (Callard–Salo-type) element instead of t×id.
- 4bfc08e51: route kazhdan-finiteness-in-nv-via-cnd-transversal — ψ_1 (transversal) alone ⇒ every Kazhdan
  subgroup of nV finite (conjugate by coordinate permutations; ∩ of triangular subgroups = V^n; Farley).
  ψ_1 ⇔ cnd proper modulo V^n. Refutation test: a relative-(T) subset off finitely many cosets of V^n.
  Attempt bullet added to brin-thompson-nv-cnd-proper-modulo-triangular-subgroup. ψ_1 itself NOT proved.
  Review requested from gq-referee-a/b.
- gq-referee-a PASS (d89c65d4d) on both conditional routes; its note is recorded in gl-3-z route (72eed2899).
  gq-referee-b PASS (0c5ef12bf); both recorded + BHV Thm 2.12.4 citation (1b7325977). ψ_1 itself still OPEN.
- 9e5998ab5: odometer hole (some-brin-thompson-element-factors-onto-an-odometer) NOT decided.
  odometer-factor-witnesses-mix-coordinates (EST): no power of a witness in any conjugate of T_k (so k>=2, V impossible).
  brin-thompson-first-return-maps-lie-in-kv (EST): bounded-return inducing stays in kV up to brick-local conjugacy
  → SMART overhead can be induced away. Next: SMART substitution from Callard–Salo e-print (distortion-1-smart.tex).
- 37c1222a1 + 53c161235: smart-level-zero-return-map-factors-onto-3-adic-odometer (OPEN, proof claimed, referees a/b)
  + route odometer-factor-via-smart-level-zero-return-map → odometer hole. SMART moves nest by b→bdp,d→dbq,p→bqp,q→dpq;
  induced on level-0 configs, phase is local ⇒ Z/2×Z_3 factor. MSI check: gap ≤ 6, unique desub 8 levels, 0 phase conflicts.
- be2fe0964: SMART odometer claim ESTABLISHED (referee-a 6000c8af8 + referee-b 628a5c79d PASS; proof route landed,
  bounded returns proved directly, 8-state coding). Odometer hole ESTABLISHED (k=2, m=3). Renormalization of U open.
- 9fadf5ac6: smart-induced-map-has-brick-local-height-3-renormalization (OPEN, proof claimed; referees a/b; gq-affq MSI check)
  φ = delete the cell next to the head (4 local cases) on A = first Y-points of level-1 moves; ⇒ bs13-embeds-in-brin-thompson-3v
  via route bs13-in-3v-via-smart-renormalization (renormalization node unreviewed). BS(1,2) not addressed.
- d4064ce79: smart-induced-map-has-brick-local-height-3-renormalization ESTABLISHED (referees a 12b5beb4a, b b6d33ae8e,
  c 894d10d19 PASS; gq-affq MSI 55k checks; gq-lit-arxiv no priority threat e78b09c00) ⇒ bs13-embeds-in-brin-thompson-3v ESTABLISHED.
- 97129d9a8 + 6b732bfb2: BS(1,2) — binary-SMART search NOT found (artifact gq-gq-nv-obstruct-binary-smart-search.md).
  Exhaustive RTM searches ≤ 4+4 states: ternary counters or binary with linear overhead; 8+8 binary symmetric
  (partial): Jacobsthal timing but every candidate = bounded binary skeleton + linear walk. Conjecture: TM format
  forces the walk ⇒ try kV-native insert/delete bases.
- 4eb6fec15: crossing-move-hierarchies-have-odd-branching (EST, elementary): crossing-only one-head hierarchies branch oddly;
  binary needs returns (Jacobsthal C→→C→R_R, R_R→C←C→) turning one short. Full symmetric 8+8 binary class: only skeleton+walk.
- 2f98d9966: targeted binary-timing scan (4+4/3 full, 8+8/2 slice, 6+6/3 2 of 9 slices): 5 machines with bounded per-type
  overhead; induced ⇒ exact 2-adic Y-counts + bounded gaps (≤221) but mod-8 phase NOT local (radius ≤15). No BS(1,2) base.
  [WITHDRAWN: the phase counts were a hash bug (c3c2266d0); the gaps are not bounded, M° grows +6/level (30841be4c).]
- c3c2266d0: renormalization-return-times-tend-to-zero-adically (π continuous, π mod m^j at radius D+(j−1)P,
  returns T^{n_i}y→y force n_i→0 in Z_m); SMART calibration n ≡ 0 mod 729; M° returns n = 29·2^m+4 (radius ≤ 18).
  77962be45 + 2944807e2: referee-b PASS (fba51b1a0) + referee-a PASS (d4e505ddd) ⇒ ESTABLISHED.
- 30841be4c: complete 6+6/3 scan (185.8M machines, 1.54M binary-timing): the bounded-junction filter on every
  candidate's zero-overhead Y leaves 1,053 at 3.2e7 steps, and ALL have a Y-gap head range growing 1–2 cells/level
  (hidden carry sweep). M°'s gap grows +6/level. Phase is often local on walk machines (returns ≡ 0 mod 2^14 at
  radius 10), so in this class 2 fails on bounded returns, not recognizability. Artifact §3f; bs12 Attempts.
- 1d6017048: return-time lemma Calibration: M° example marked withdrawn in place (30841be4c); SMART calibration and statement unchanged.
- 89ff8c89d: fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups — bh-referee-c PASS-with-fixes (4933b62e6); F1 applied as item 3
  (finite H: pass to H × Z = ⟨diag(H,1), diag(I_n,2)⟩ ≤ GL_(n+1)(Q), so the host always contains kV, 2V, Q).
**Status 2026-09-18:** IDLE until the coordinator messages. The "no binary SMART" theorem is OPEN. MSI: no lane processes; lane dir gqsrc/gq-nv-obstruct 992 MB (outputs only) KEPT per coordinator: raw evidence for 30841be4c; deletion is the user's call.
