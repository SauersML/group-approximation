# bh-g1-simulation (gate E1: existence)

**Status (09-18 ~16:40):** landed f9ae89eb9 and 695a89096 (lane proofs at design level, unreviewed).
- f9ae89eb9: decidable-groups-carry-flexible-free-subshifts (route identifier-markers-give-decidable-free-subshifts) proves (D) (bh-g1-universal-point) and decidable-groups-have-universal-hyperaperiodic-points (route universal-hyperaperiodic-points-via-decidable-free-subshifts) for every fg decidable group.
- The chain: Clapham envelope A; (D) or (U)+(H) on A; (M2) on A*Z; minimal free SFT on (A*Z)×Z². So P1 holds for all decidable inputs. For GL_n(Q), take A = St_10(R_L).
- Review-critical: lemma (E) of identifier-markers-give-decidable-free-subshifts; the free-product lemmas (bh-g1-effective, bh-g1-universal-point); the keyed-slot DR adaptation.
- Shared with bh-gln-tracka and bh-g1-universal-point by SendMessage and board.
- Next: red-team lemma (E) on groups with deep pockets (Cleary–Riley type); then E2 for the lift (RS node).


**Status (09-18 ~15:30, relaunched after the restart):** landed 695a89096 (lane proofs, unreviewed).
- free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2: PROVED at design level, via route keyed-diversification-slots-give-plane-constant-minimal-lifts. It is (M1) for free inputs, with all of Λ₀×Z² acting freely.
- minimal-free-sft-overgroups-exist-iff-m2-overgroups-exist: P1 ⟺ decidable-groups-embed-in-fp-groups-satisfying-m2, input by input. The converse uses Jeandel 1501.06831, read at source.
- minimal-free-sft-via-m2-overgroups-and-keyed-plane-lifts: a route to P1 with ONE open premise (the M2 overgroup).
- Notes appended to the M1 node (Attempt 4), the P1 node (reduction) and the plane-tuple crux (bypassed for free Y).

**Answer to the directive.**
- Λ₁'s self-simulability can be arranged free (Λ₁×F₂ is a BSS product), but it is no longer needed.
- Simulation cannot produce (M2): every minimal free SFT already is an (M2) instance. So (M2) is the irreducible content of E1.
- The lift to an SFT is solved over Λ₀×Z² for free inputs, not over Λ₁×Λ₁.

**Open / next.**
- (1) Review the keyed-slot design against DR §3.2/§5 frames (p1)–(p4), especially border slots straddling infinite faults.
- (2) E2 for these lifts is RS (plane-constant-simulation-computation-layers-are-quantum-rigid). The floating locus is forced, so bounded determination is impossible.
- (3) E1 = M2: attack decidable-groups-have-universal-hyperaperiodic-points (bh-g1-effective / bh-g1-universal-point).
- (4) Transfer keyed slots to BSS Q:minimal over non-amenable squares (free inputs)? Not needed for P1.

Earlier landings: 05f066167 (simple subgroups act trivially on equicontinuous factors; MSS route; P1 attempts). Sources are in $GQ/src/bh-g1-simulation/ (BSS, DR, Jeandel TeX).

## Older notes
# bh-g1-simulation (gate G1(g): coupled simulation over Λ_0 x Z^2 and Λ_0 x F_2)

Landed 05f066167 (lane proofs, unreviewed):
- simple-subgroups-act-trivially-on-equicontinuous-factors: ESTABLISHED. m.a.p. subgroups act trivially on MEFs, so free minimal actions of such groups are never almost automorphic, and functional couplings kill the input.
- nonamenable-products-have-minimal-sft-extensions-of-free-inputs: OPEN. BSS Q:minimal, restricted, with design constraints.
- minimal-free-sft-via-minimal-self-simulation-of-squares: route, P1 ⟸ (M2) + MSS for Λ_1 x Λ_1.
- Attempt on P1 (with a source correction: BSS exclude F_k x Z), Attempt 3 on M1.
- Artifact: research/artifacts/gq-bh-bh-g1-simulation.md. Sources (BSS, DR, Jeandel TeX) are in $GQ/src/bh-g1-simulation/.

Common crux in every setting: a minimal, relationally coupled field of hierarchy phases over a group containing the input.
For bh-g1-rigidsim: rigidity has to hold across that phase coupling, and part 1 of the lemma says the input direction is invisible to equicontinuous parses.
Next leads:
- G1-geom: a minimal paradoxical SFT on a non-RF non-amenable group; start by proving BSS's F_2 tile set M is minimal.
- Phase-field couplings R_s that are not graphs, tested on F_2 x F_2.

[from bh-openq-papers, 11:40] Literature at source (landed 84c5e8d9a, 348d2c736): Aubrun–Bitar–Huriot-Tattegrain arXiv:2204.11492 l.755 — "There exists a minimal strongly aperiodic SFT on F_n × Z" (Labbé's expansive-direction Z² shift transported along a finite-type flow on the F_n tree); also unimodular GBS and BS(1,n). Node `free-times-z-carries-a-minimal-free-sft`. Rigidity not addressed. For M2: Álvarez López arXiv:1807.09256 gives computable free strongly repetitive points with computable central modulus on every decidable group (see M2 node Attempt 7); only the global/seam modulus remains.

**From bh-g2-fixedpoint-b:** cc93f9797 path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is. ABHT's minimal free SFT on F_n×Z is quantum rigid ONLY IF its horizontally expansive Z² fibre (Labbé–LMM X_0) is: a fold lemma via a 1-Lipschitz pullback, which also covers Busemann transplants. The converse is open (path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid); its missing step is centrality (C). So a win on the Z² gate for an expansive-direction minimal free shift would transfer to F_n×Z, modulo (C).

[from bh-gln-tracka, 09-18 ~16:20] M2 on St_10(R_L), coordination note.
- I did NOT find a (U)+(H) point or an M2 witness for St_10(R_L). Constraints recorded:
  - m.a.p. (quasisimple, PE_10 simple): no almost-automorphic witness and no almost-automorphic coupling;
  - (FA): no tree skeleton;
  - the central K_2 ≅ Q^× (with an involution) must act freely.
- For the GROUP route only, there is an alternative that skips M2 (9d121fa9cc `end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups`). A tree end shift with fg stabilizers is a minimal topologically free SFT, but it needs fp RF vertex groups containing Z_(S), and never St_10(R_L).
- So for GL_n(Q), the universal-point attack on M2 stays the main line, and I am not duplicating it.

**From bh-g2-fixedpoint-b (09-18 ~17:40): the downhill tool, for (★′) on (Λ₀∗Z)×Z².** Landed df763a98d `downhill-centrality-needs-no-data-rigidity`; see also 4c2d76fe4 and 755489fe5.
- **Downhill lemma.** Take a causal layer with a ONE-predecessor rule c(z) = β(p, c(z·u_p)) (seeds elsewhere), where the offset u_p is read off a flow. Suppose the flow marginals commute with each other and with the data, and a potential δ drops on "toward" steps while "away" steps force the target's flow letter. Then the flow is central, with NOTHING assumed about the data your slots read.
- **Consequence.** The seeded direction is rigidity-neutral. A seeded transport coding is rigid ⟺ its input layer is. Minimality holds under boundary completeness: every unseeded completion is a limit of seeded ones.
- **To use it.** Check the one-predecessor rule and the potential δ for your keyed-slot layer against its tree direction. Then E2 = rigidity of the crossing-wire fibre plus the input the slots read.
- **Warning.** Relational (non-graph) couplings of seeded phases split or kill minimality (755489fe5).
