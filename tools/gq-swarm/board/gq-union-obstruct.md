# gq-union-obstruct board — DONE
**Approach** (obstruction-miner, family E): necessary conditions on any overgroup of U_m GL_n(Z[1/m!]) = GL_n(Q).
**Established** (all agent-verified only, not refereed; elementary; no priority claimed):
- sl-n-q-lies-in-finite-residual-of-every-overgroup (+ -proof) — c7caf5b8c. Every finite-index subgroup of every
  overgroup contains SL_n(Q); finite residual of GL_n(Q) = SL_n(Q). Exact form of O1.
- divisible-elements-act-elliptically-on-trees (+ -proof) — ec44ffb17. Roots of infinitely many orders => elliptic;
  (Q,+) fixes a vertex or exactly one end; RF vertex stabilizers => root groups parabolic.
- gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings (+ -proof) — ec44ffb17. GL_n(Q) <= PGL_(n+1)(Q) faithful on
  p-adic building vertices; PGL_2(Q), Aff(Q) faithful on T_(p+1); O1 tree clause is rooted-only; one prime carries
  all divisibility; the action is not type (A).
- no-q-in-tree-product-actions-with-finite-stabilizers (+ -proof) — ec44ffb17, revised 55a810cde. No (Q,+) with finite
  vertex stabilizers on a product of trees (complements proper-semisimple-cat0-groups-contain-no-gl-2-q).
- artifact research/artifacts/gq-gq-union-obstruct.md; root Attempts item 12 — 55a810cde.
**Needs:** none. **Dead:** none.
**Sparks (free):** S1 f.g. subgroups of the Neretin group of T_(p+1) containing PGL_2(Q) (Bruhat–Tits + V-type
simplicity) — for gq-solenoid / gq-adelic / gq-rn-varying-degree. S3 uniform root-length bound for e_12(1/m).
**Pass 2 (2026-09-18, team-lead target: adelic median graph, split with gq-sl2q — they own construction + Aut(X) + orbits):**
- sl-2-q-root-group-is-parabolic-in-every-prime-factor (+ -proof) — f98aabbc7. U fixes one end per factor, no vertex;
  Stab = B(Q); Busemann B(Q) -> ⊕_p Z, kernel ±U; depth Ω(m!), displacement 2Ω(m!); isometric hosts: |u(1/m!)| >= 2Ω(m!)/C.
- fg-restricted-product-actions-have-finite-support (+ -proof) — f98aabbc7. fg coordinatewise ⇒ finite support; no
  coordinatewise thickening hosts adelic SL_2(Q)/GL_n(Q)/Aff(Q); monomial hosts: primes in finitely many σ-orbits,
  |u(1/m!)| >= π(m)/s.
- artifact §7 + root Attempts item 20 — f98aabbc7. (P) not refuted; Boone–Rogers uniformity route recorded as the gate.
