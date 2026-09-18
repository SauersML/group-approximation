# gq roster (70 lanes), 2026-09-17 — assignment per lane (name = SendMessage address)

## Support (10)
- gq-map — Build the cone map: every Cairn node/tool relevant to G (hosts, germ extensions, shells, type (A), twisted
  Brin–Thompson, Leavitt/rings, Steinberg/K_2, self-similar affine). For each, say whether O1–O3 kill it for GL_n(Q)
  and what it could still contribute. Land artifact gq-gq-map-cone.md within ~60 min; update once later.
- gq-lit-arxiv — Priority/literature: has anyone (2023–2026) embedded GL_n(Q) itself (or SL_n(Q), Aff(Q), U_3(Q)) in a
  f.p. simple group, or answered Problem 2.7 / Kourovka 14.10? arXiv listing/abstract searches, Kourovka latest
  edition, authors' pages (Belk, Hyde, Matucci, Zaremsky, Bleak, Bridson, Mikaelian). Report threats to team-lead
  at once. Afterwards serve priority checks on request.
- gq-lit-q-embeddings — Extract the exact mechanism of every known explicit embedding of (Q,+): Belk–Hyde–Matucci
  (Q ≤ T̄, Bull AMS 2022), Kojima–Sheng (Q ≤ 2V), Mikaelian, Johnson/Higman. What in each supplies divisibility; which
  generalize to Q^n, Aff(Q), U_3(Q), GL_2(Q). Artifact with verbatim statements.
- gq-lit-hosts — Extract usable theorems with verbatim hypotheses: BHM finite germ extensions (arXiv:2407.03149,
  Thm 2.1 and the VA proofs), BBMZ rational similarity groups, Zaremsky twisted Brin–Thompson finite presentation
  (arXiv:2405.18354), BFFHZ (arXiv:2503.21882, type (A) constructions, universality), Lodha–Moore / Monod piecewise
  projective groups. Artifact; answer other lanes' "what exactly does theorem X require" questions.
- gq-calibrator — For every approach on the boards, test it first against O1–O3, distortion (unipotents of
  GL_2(Z[1/2]) are exponentially distorted), property (T)/FW of SL_3(Z), and "does it use anything Q has that
  Z[1/m] lacks?" Post verdicts on the lanes' boards via SendMessage; land an artifact of calibration worlds.
- gq-referee-a — Adversarial referee, proof-gap lens. Prepare (read RULES, root, the key host theorems), then end
  your turn; you will be messaged with review requests. Each review: artifact gq-referee-a-<id>.md, verdict PASS/FAIL
  with the exact failing step; SendMessage the author and team-lead.
- gq-referee-b — Adversarial referee, citation/hypothesis-match lens (every cited theorem read at the source, every
  hypothesis checked). Same protocol as gq-referee-a.
- gq-referee-c — Third referee for anything settling G, G' or a stepping stone: independent re-derivation plus the
  calibration test. Same protocol.
- gq-critic — Completeness critic. After ~2 h of boards exist: what known case was never checked, which hypothesis
  never used, which families never tried. Land artifact gq-gq-critic.md; SendMessage team-lead one list of gaps.
  Then end; you will be messaged for later passes.
- gq-integrate — Graph health. Only lane allowed to run `bin/cairn check` (at most once per pass). When messaged:
  check, fix lint in gq-landed nodes (via the lander), wire new routes to the root, and land a status artifact
  gq-gq-status.md. First pass when messaged by team-lead; end your turn between passes.

## A. Germ extensions / VA-type hosts (7)
- gq-va-gl2 — Does GL_2(Q) (or SL_2(Q), or Aff(Q)) embed in VA or in another BHM finite germ extension of V? n = 2 is
  not excluded by O2. Find an embedding or an obstruction.
- gq-germ-design — Design a finite germ extension of V (or of nV / twisted Brin–Thompson) whose germ groups carry
  GL_n(Q) pieces; verify BHM Thm 2.1's hypotheses for finite presentation, and simplicity.
- gq-tbar-lift-n — Generalize Q ≤ T̄: lifts of piecewise-affine/projective groups of the n-torus or of solenoids to
  R^n; aim at Q^n ⋊ GL_n(Z), then more of GL_n(Q); finite presentation of the lifted groups.
- gq-solenoid — GL_n(Q) = Aut of the solenoid (A/Q)^n and acts on the finite adeles A_f^n (one-point
  compactification is Cantor-like). Build a V-like group of locally affine homeomorphisms of an adelic Cantor model
  containing GL_n(Q); decide finite generation/presentation.
- gq-germ-necessary — Necessary conditions: in any f.p. group of Cantor homeomorphisms containing GL_n(Q), what must
  germ groups look like (divisibility forces what)? Obstruction lane; kills or sharpens family A.
- gq-q-in-germs — Locate exactly where Q sits in VA (which germs, which part of A) and whether U_3(Q) or Aff(Q) can
  sit there the same way.
- gq-va-affq — Stepping stone Aff(Q) = Q ⋊ Q^x into VA or a VA-type germ extension.

## B. Type (A) actions / twisted Brin–Thompson (7)
- gq-typeA-design — Check that the repo's host equivalences (type (A) ⇔ Alt_fin host ⇔ …) hold for countable,
  non-f.g. inputs such as GL_n(Q); state the weakest sufficient statement for G as a Cairn claim + route.
- gq-houghton-q — Houghton-type f.p. permutation groups containing Alt_fin(X) and an affine/linear action of
  GL_n(Q) (X = Q^n, P^{n-1}(Q), or a thickening).
- gq-typeA-projective — GL_n(Q) is 2-transitive on P^{n-1}(Q). Find a f.p. overgroup with a type (A) action
  extending it (f.g. stabilizers, finitely many pair orbits); the stabilizers are the hard part.
- gq-typeA-bffhz — Adapt how BFFHZ built type (A) actions for Aut(F_n) to GL_n(Q) or to an overgroup.
- gq-typeA-alt — Freedom lane in family B: any type (A)/twisted Brin–Thompson idea not on another board.
- gq-bt-kojima — Extend Kojima–Sheng's Q ≤ 2V: Aff(Q), U_3(Q), GL_2(Q) inside nV or a twisted Brin–Thompson group.
- gq-nv-obstruct — Obstructions for nV and twisted Brin–Thompson hosts: does SL_3(Z) embed in nV? Decide whether
  family B can hold GL_n(Q) for n >= 3.

## C. Piecewise projective (5)
- gq-pp-psl2q — Piecewise PSL_2(Q) homeomorphisms of RP^1 (Monod-type H(Q), Thurston PIP): subgroups containing
  PSL_2(Q); finite generation/presentation; relation to T ⊇ PSL_2(Z).
- gq-pp-lift — Lifts to R (T̄-style central extensions) to get SL_2(Q)/GL_2(Q) and divisibility from rotation-type
  torsion.
- gq-pp-higher — Piecewise-projective homeomorphisms of RP^{n-1} or spheres with rational data, containing
  PGL_n(Q); Thurston's Remark 5.5 question over Q.
- gq-pp-fp — Finite-presentation technology for piecewise-projective candidates (Lodha–Moore, Burillo–Lodha–Reeves,
  Brown's criterion) applied to the candidates of gq-pp-psl2q / gq-pp-lift / gq-pp-higher.
- gq-pp-simple — Simplicity/commutator structure of those candidates (Higman–Epstein), and adding V-type pieces.

## D. Rings, Leavitt, Steinberg (9)
- gq-ring-fp-simple — A finitely presented simple ring containing Q (char-0 case of algebra Boone–Higman):
  literature (Bokut, Evans–Mandelberg–Neff) and constructions.
- gq-ring-leavitt — Purely infinite simple rings with M_n(L) ≅ L: find a f.g./f.p. subring of L_Q(1,2) (or similar)
  containing Q, and a f.p. simple group inside its unit group containing GL_n(Q).
- gq-leavitt-units — Unit and elementary groups of Leavitt algebras over Z, Z[1/m], Q: what is known about finite
  presentation and simplicity (the repo imports the F_2 case); extend.
- gq-steinberg-q — Steinberg presentation of SL_n(Q), n >= 3, with K_2(Q) (Tate); relative Higman-type or HNN
  constructions exploiting it; aim at G' first.
- gq-en-ring — E_n(R) for f.p. rings R ⊇ Q: finite presentation (St_n + K_2), normal subgroups for simple R, a route
  "f.p. simple R ∋ Q ⇒ G".
- gq-malcev-ring — Explicit natural f.g./f.p. rings containing Q (Mal'cev, Bokut), aiming at natural ones for G'.
- gq-ring-alt — Freedom lane in family D.
- gq-cuntz-cstar — Operator-algebra transplant (COLD family): Cuntz algebras, their unitary and algebraic
  analogues, K-theory; is there a Cuntz-type f.g. *-ring containing Q with a usable unit group?
- gq-k2-q — K_2 and Steinberg groups over Z[1/m], uniformly in m; what a uniform host for the chain
  GL_n(Z[1/m!]) needs.

## E. Unions, Scott/Röver–Nekrashevych, adelic (6)
- gq-scott-union — One f.p. simple group containing a compatible ascending chain GL_n(Z[1/m!]) (Scott Sc(n) for
  GL_n(Z); Zaremsky's affine hosts for each m). Infinite branching / all-primes constructions.
- gq-rn-varying-degree — Almost-automorphism groups of non-regular (spherically homogeneous, all-primes) trees and
  their Röver–Nekrashevych analogues; finite presentation.
- gq-union-obstruct — What any f.p. group containing ⋃_m GL_n(Z[1/m!]) must have (non-RF divisible structure, germ at
  infinity); rules out naive unions; sharpens E.
- gq-bhm-pattern — Abstract the BHM pattern (Q as an ascending union realized by roots in a f.p. group via torsion
  and a central extension) into a general union-embedding criterion; apply to GL_n(Q).
- gq-adelic — With gq-solenoid: V-like groups over the adeles containing GL_n(Q); split work with it on the boards.
- gq-union-alt — Freedom lane in family E.

## F. Stepping stones (6)
- gq-affq — Aff(Q) = Q ⋊ Q^x into a f.p. simple group, any method.
- gq-heis-q — U_3(Q) and U_n(Q) (divisible nilpotent) into a f.p. simple group.
- gq-borel-q — Borel B_n(Q) into f.p. simple groups, then GL_n(Q) through Curtis–Tits / BN-pair amalgam
  presentations and permanence of embeddability under those amalgams.
- gq-sl2q — SL_2(Q) and PSL_2(Q) (n = 2), all methods; coordinate with family C.
- gq-infinite-primes — GL_n(Z[1/P]) for infinite computable prime sets P: when it helps, and whether it is
  equivalent to the Q case.
- gq-countable-fields — GL_n(K) for other countable fields (F_p(t), Q̄): is some K easier (char p kills O1's
  divisibility)? Transfer ideas back to Q.

## G. Reformulation and roles (5)
- gq-reform-countable — Countable-input versions of the repo's Boone–Higman reformulations for H = GL_n(Q); the
  weakest sufficient statement; land as claims/routes.
- gq-explicit-fp — Problem 2.7 directly: an explicit natural f.p. group containing GL_n(Q), simplicity not required.
- gq-inverter — Role inverter: the biography of "GL_n(Q) embeds in no f.p. simple group" (what it forces, e.g. BH
  false); contradict it or turn it into a construction recipe.
- gq-heretic — Role heretic: name three unstated assumptions of the popular approaches (Cantor-set hosts,
  V-commutator simplicity, tree coordinates, …) and deny each.
- gq-obstruction-miner — Find the invariant most dead approaches hit (divisibility vs finite presentation,
  distortion, FW); kill a class or find the gate.

## H. Deep freedom lanes (12)
- gq-deep-va-1, gq-deep-va-2 — germ/VA line, any idea not on another board.
- gq-deep-ring-1, gq-deep-ring-2 — ring/Leavitt/Steinberg line.
- gq-deep-pp-1, gq-deep-pp-2 — piecewise projective/lift line.
- gq-deep-typeA-1, gq-deep-typeA-2 — type (A)/twisted Brin–Thompson line.
- gq-deep-adelic-1 — adelic/solenoid line.
- gq-deep-free-1, gq-deep-free-2, gq-deep-free-3 — any approach no board is running.

## I. Explicit and transfer (3)
- gq-explicit-2 — Second lane on Problem 2.7.
- gq-transfer — If G falls: what else follows (countable subgroups of GL_n(Q), GL_n(Q̄), countable char-0 linear groups
  with solvable WP), which printed questions it answers (Kourovka 14.10 numbering and status), exact wording.
- gq-writeup — Running "state of the attack" artifact from boards and landings (no claims of its own); after any
  referee-PASSed result, a clean write-up skeleton of it.

## BH swarm (09-18 ~08:00), wave 1
- bh-map — subgraph map of BH on main: status table, equivalences, live routes and gates, frontier, BBMZ Problem 5.3 / named-problem status; artifact only.
- bh-lit — literature 2022–2026 on BH and fp simple embeddings; exact statements; flag anything that supersedes or duplicates repo nodes.
- bh-shell-universal — `perfect-decidable-inputs-have-fp-shell-envelopes` / `decidable-inputs-have-fp-shell-envelopes`: the universal shell route.
- bh-typeA-universal — BH via type (A)/BFFHZ actions for arbitrary decidable inputs (`boone-higman-via-bffhz-action-image` and neighbors).
- bh-mcg — mapping class groups.
- bh-outfn — Out(F_n) (Aut(F_n) permutational BH is on main; check exactly what is established).
- bh-one-relator — one-relator groups (all have solvable WP by Magnus).
- bh-cat0 — CAT(0) groups (and what cubulation/linearity already gives).
- bh-linear-fields — fg linear groups over arbitrary fields (transcendental char 0, char p).
- bh-solvable — fg solvable / elementary amenable groups with solvable WP.
- bh-refute — red team: necessary conditions for subgroups of fp simple groups beyond solvable WP; any counterexample mechanism, calibrated against known theorems.
- bh-permanence — closure of BH under amalgams, HNN, extensions, wreath products; equivalence reductions.
## BH swarm wave 2 (09-18)
- bh-3manifold — all compact 3-manifold groups.
- bh-self-similar — automaton / self-similar groups beyond contracting.
- bh-kazhdan-inputs — sharpen and attack the equivalent forms of BH on main.
- bh-cool — striking explicit constructions (universal families in one explicit fp simple group, short explicit hosts).
- bh-referee-c — third referee, end-to-end hypothesis checks for class-level BH claims.
- (continuing) gq-infinite-primes — computable detector K_2(R_L) ≅ Q^× (shell gate 1 (ii)); gq-k2-q — G_3 when Kolster arrives; gq-typeA-design — St_N(R_L) shell instance; gq-referee-a/b — reviews.
## BH swarm wave 3 (09-18 ~08:45)
bh-shell-arith, bh-shell-kazhdan, bh-shell-germ, bh-higman-classic, bh-ck-kernel, bh-algebra, bh-groupoid, bh-near-actions, bh-typeA-oligomorphic, bh-logic, bh-hhg, bh-amenable, bh-lattices, bh-artin, bh-critic.
## BH swarm wave 4 (09-18 ~08:55)
bh-relhyp, bh-free-extensions, bh-graphical-sc, bh-kourovka, bh-bbmz-problems, bh-universal, bh-testcases, bh-integrate, bh-writeup; bh-linear-fields rotated to Thompson-like groups (target already established as finitely-generated-linear-groups-satisfy-boone-higman, ff3174b2a).
## BH swarm wave 5 (09-18 ~09:10, free lanes): bh-free-01..15; bh-preprints (deep recent-preprint review); bh-palomar-plan (Palomar megasubmission plan); bh-verify-{metabelian,artin,linear}.
## BH swarm wave 6 (09-18 ~09:20): bh-openq-papers, bh-openq-lists (literature open-question hunters → board/UNOWNED.md); bh-free-16..28 (cool solves; 21 automatic groups, 22 fp RF groups, 23 BBMZ-hyperbolic Qs, 24 Kac–Moody Q3.6/FFKLZ Q2.4).
## Palomar BH megasubmission (09-18 ~09:55; user: one combined config, yaml switch now WIP, integrate with bh-met chain, only our solved results, include lean-eval higman_infinite_simple)
bh-pal-surface (challenge/solution/config/yaml/gate), bh-pal-integrate (bh-met integration, root wiring, gap-lane proposal), bh-pal-scope (list+sizing of our solved results), bh-pal-steinberg (St_10(R_L) ⊇ GL_n(Q)), bh-pal-leaneval (higman_infinite_simple; user submits), bh-pal-t3-scout (linear-groups Lean coverage map). Lean lander: gqland-lean.sh.
## Wave 7 (09-18 ~11:30, "more agents lfg"): bh-free-29..46 (Houghton lifting, GL_n(Q) fresh eyes ×2, BH first principles ×3, Kazhdan construction, Baumslag–Gersten, BBCMP Q1.15 cubulated, Kourovka open items, Nowak Torelli, U_3(R_L), Out(F_n) direct host, surface groups in V, 5 fully free); bh-houghton-morse, bh-houghton-presentation; bh-pal-wire, bh-pal-kourovka59, bh-pal-kourovka61.
## Wave 8 (09-18 ~12:00, "massive solves"): bh-free-47..60 (Houghton lifting positive+counterexample, H4 amalgam host, nV periodic groups, automatic E-conditions, one-ended hyperbolic RSG, algebra gate counterexample, MCG train-track gates, Lagrangian Thompson group, 5 fully free).
