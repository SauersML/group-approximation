# bh-invent-15 (inventor lane: geometric route)
**Landed:** b40a89028 `hard-cusps-are-canonical-and-flux-free` (lane proof, not reviewed).
- Cusp normal form: a free cocompact cusp of a Cantor action is (P × Cantor)^+, which depends only on P.
- Commutant: for one-ended P, germs commuting with P = Homeo_P(Y) ≅ C(K,P) ⋊ Homeo(K), with no flux. For P = Z there are two independent end germs (Houghton flux).
- Every infinite f.g. simple group is one-ended.
- Right multiplication Ψ_a gives germ group S × Z at the engine's cusp.
**Gate:** the geometric route does not bypass (IE). (RB) and (IE) are one local model. Interface (RB′): a finite-type (BHM-good) base carrying one right multiplication Ψ_a at each cusp, but not S.
**For bh-synth-lead:** Reid's group is the only fluxed case, so a negative answer there does not transfer. Flux-free test: the engine of B = F or V.
**Dead:** one-step geometric quotients (finite small cancellation, finite Dehn filling) as simple hosts; they stay acylindrically hyperbolic.
Status: done (one-shot).

**Round 2 (coordinator: flux-free test for F, V; align with IE′ and seed orbit):**
- Landed bb487abce `stabilizer-engines-are-fp-only-over-isolated-groups` (lane proof, not reviewed; REFEREE REQUESTED, gq-referee-a).
  - F_B or D(F_B) fp ⇒ B isolated in the space of marked groups.
  - So Reid's group is not fp, engines of RF groups are not fp, and engines of infinitely presented simple S are not fp.
  - This invalidates `simple-inputs-have-finitely-presented-stabilizer-engines`, and Track C is circular.
- B = F and B = V are isolated, so the flux-free test is NOT decided (and is irrelevant for BH).
- Alignment: the canonical cusp is the emitter K = S⁺ (the bottom of bh-invent-13's family), NOT the isolated-seed SFT. The approximation argument is why the emitter fails and why the seed object (IE′)/(★𝒞) is forced.
- Next test: does the transfer argument extend to finite-type blow-ups, i.e. can isolated-seed rigidity be approximated?

**Round 3 (coordinator: can isolated-seed rigidity be approximated? feeds CAP):**
- Landed c90fc9348 `seeds-never-survive-marked-approximation` (lane proof, not reviewed). No: over an fp group, no proper approximant carries ANY p-configuration.
- A seed = relative isolation, which for seeded groups ⟺ fp; it replaces finite discriminability.
- So approximation obstructions cannot reach seed engines. CAP needs a non-local argument.
- Open, for bh-star-a: does fp + seed (no rigidity) force a solvable WP?
- Track C residue for bh-emitter-b: does Γ̂_L carry a free p-configuration with converging language?

**Round 4 (coordinator: fp + seed with no rigidity ⇒ solvable WP?):**
- Landed a9187d6d4 `seeded-groups-have-solvable-word-problem` (lane proof, not reviewed; Jeandel's method localized to the seed cylinder). YES: recursively presented + seed ⇒ decidable WP, and y_* is computable.
- CAP is not decided; it = a uniform bound on the seed-collapse function κ. Sent to bh-star-a.

**Round 5 (coordinator: can κ grow fast for rigid seeds?):**
- Landed b970e40ae `seed-collapse-is-bounded-by-forcing-radius-and-dehn`, which also sharpens the CAP remark in a9187d6d4.
- Result: log T_WP ≲ κ ≲ |Ball(R)|·δ(O(R)); the witness radius is constant.
- Fast κ comes only from the forcing radius R or the Dehn function δ. Distortion (BG) gives fast δ but polynomial WP, so no ¬CAP content.
- The ¬CAP target is a linear-forcing rigid seed on a machine-simulating tower (the seed-tower team). CAP is still open.

**Round 6 (seed tower):** landed 3379f8c7c (rope obstruction + build order); appended to board/seed-tower.md.

**Round 7 (seed tower step 1):** landed 5a72aa6a9: S_M in C, a linear-radius numeral reader, and gate (RR) open.

**Round 8:** 27b0124da: option (b) refuted, the uncoupled reader is not rigid, new gate (RR′) is chain coupling.

**Round 9:** coupled reader landed; linking + pointwise rigidity proved; (C_D) for one idempotent is open.
