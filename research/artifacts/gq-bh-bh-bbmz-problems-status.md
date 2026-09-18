# Named Boone–Higman problems: status on main and swarm staffing (09-18)

Lane `bh-bbmz-problems` (BH swarm), 2026-09-18. Main was read at `54c5d8424`.

**Sources.**
- `bh-survey-open-cases-status-2026-09-12.md` (the survey read page by page);
- `gq-bh-bh-lit-survey.md` (bh-lit, with question wording);
- `gq-bh-bh-map-subgraph.md` §3 (bh-map, with Problem 5.3 status).

This file does not re-derive the Problem 5.3 table. It adds three things:
1. staffing in the current swarm;
2. every other named question these papers raise, with its node on main;
3. this lane's new results.

The earlier artifacts hold the verbatim wording. Statuses are the node's own bold
line. "Lane proof" means not independently reviewed.

## 1. Survey arXiv:2306.16356v3, Problem 5.3 (status per bh-map §3), with staffing

| Item | Status on main | Owner in the BH swarm |
|---|---|---|
| (1) braid | settled, BFFHZ (literature import) | none needed |
| (2) MCG | open for closed genus ≥ 3 (`closed-surface-mapping-class-groups-satisfy-boone-higman`) | bh-mcg, bh-hhg |
| (3) Aut/Out(F_n) | Aut settled; Out(F_n), n ≥ 3, open (`out-free-groups-satisfy-boone-higman`) | bh-outfn |
| (4), (8) BS(m,n), free-by-cyclic | settled, BLIW (literature import) | none needed |
| (5) GL_n(Q) | open, excluded from this lane | gq lanes |
| (6) free Burnside | `free-burnside-groups-satisfy-boone-higman` OPEN, opened at `54c5d8424` by another lane; §4 below adds Attempt 1 | unowned beyond this attempt |
| (7) f.p. metabelian | ESTABLISHED on main, internal review only; literature open (BHM 2407.03149 l.272); bh-lit flag F1 | bh-solvable |
| (9) one-relator | OPEN | bh-one-relator |
| (10) CAT(0) | OPEN; two-tree and Euclidean×tree cases landed (lane) | bh-cat0, bh-lattices |
| (11) automatic | OPEN (`automatic-groups-satisfy-boone-higman`) | **unowned** |
| (12) f.p. RF | OPEN (`fp-residually-finite-boone-higman`) | **unowned** |
| (13) Artin | spherical, B̃_n, C̃_n, Ã_n, triangle and even-FC types on main (partly lane proofs); D̃_n, Ẽ_{6,7,8}, F̃_4 and general types open | bh-artin; bh-verify-artin (50dd7b24d) is checking the claims |

## 2. The survey's other named items

| Item | Node on main | Status |
|---|---|---|
| Problem 2.7 / Kourovka 14.10(c): explicit fp overgroup of GL_n(Q) | `gl-n-q-explicit-natural-fp-overgroup` | ESTABLISHED. It is an explicit construction; whether it is "natural" is a matter of taste. |
| Question 4.7: one-ended hyperbolic groups in V; closed surface groups | none (the "Question 4.7" hits on main belong to another paper) | open, unowned |
| Remark 5.5: PIP homeomorphism groups of spheres | Attempt 5 of the closed-surface MCG node | open |
| Question 5.6: fp groups into type F∞ groups | `every-finitely-presented-group-embeds-in-an-f-infinity-group` (and its F_3 version) | open claim nodes, with equivalent forms recorded |

## 3. BBMZ, hyperbolic groups, arXiv:2309.06224

| Question | Node on main | Status |
|---|---|---|
| Q1.1: hyperbolic ⇒ contracting RSG? | `hyperbolic-groups-embed-in-contracting-rsgs` records only embedding | open, no node |
| Q1.2: full contracting RSGs of type F∞? | none | open |
| Q1.3: fp subgroups of R_{Γ,E} into oligomorphic fp subgroups | none | open |
| Q1.4: fp RSG ⇒ fp full closure? | none | open |
| Q1.5: every decidable fp group into an fp oligomorphic group with fg stabilizers (universal type-(A)-style BH) | route family under `boone-higman-via-permutational-boone-higman` | open; bh-typeA-universal, bh-typeA-oligomorphic |
| Q1.6: every fp simple group into an fp simple twisted Brin–Thompson group | none directly | open (see below) |

**Resolution of bh-lit flag F3.** FWZ arXiv:2603.24687 does not answer Q1.6.
- Its groups SV_G for non-faithful actions are only *relatively* simple (Theorem A,
  as imported in `abstract-btb-pairs-fp-and-relatively-simple-citation`).
- The v2 HTML never refers to BBMZ-hyperbolic Q1.6 or Zaremsky Q5.13; checked by
  fetch today.
- Its own positive statement is Theorem C, "BH ⇒ relative PBH".

For an fp simple G, a genuine answer needs the kernel removed: some type-[A_2] actor
H ⊇ G whose kernel meets G trivially and has H/K finitely presented
(`abstract-btb-simple-quotient-fp-gate`). That is exactly what
`a2-kernel-removal-iff-image-satisfies-pbh` analyses: removal is possible iff the image
satisfies PBH. So Q1.6 for G follows from G ∈ B_A, i.e. from Zaremsky Q5.13(ii).

## 4. Zaremsky arXiv:2405.18354, BFFHZ arXiv:2503.21882, FFKLZ, FWZ

| Question | Node on main | Status |
|---|---|---|
| Zaremsky Q5.13(i): every fp simple group has a type (A) action? | `fp-simple-type-a-actions-iff-finite-bi-index-subgroups` (equivalent form) | open |
| Zaremsky Q5.13(ii): every fp simple group in B_A? | `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh` (equivalent to BH ⇒ PBH) | open |
| BFFHZ Q3.1: graph products of PBH groups | `pbh-class-closed-under-graph-products` (56d98e4fb) | **answered YES on main** (lane proof, not reviewed; priority search partial) |
| BFFHZ Q3.2 | `bffhz-q32-for-fp-simple-groups` | open; necessary conditions landed (recursive and finitely based mixed identities) |
| BFFHZ Q3.3 | `bffhz-q33-is-normal-finite-generation-of-mixed-identities` (reformulation), `thompson-t-mixed-identities-are-not-finitely-normally-generated` | **answered NO (lane proof, 09-18)**: T is a counterexample at every rank, see §7 item 4 |
| BFFHZ Q3.4: fp simple into fp simple MIF | `fp-simple-mif-embedding-via-permutational-boone-higman` (route) | open; reduced to two symbolic-dynamics premises |
| BFFHZ Q3.6: fp simple Kac–Moody groups highly transitive? MIF? PBH? | `fp-simple-kac-moody-lattices-are-mif` (literature import), `fp-simple-kac-moody-lattices-satisfy-pbh` (ESTABLISHED), `fp-simple-kac-moody-lattices-are-highly-transitive` (OPEN) | MIF yes, PBH yes, highly transitive open. Caprace–Hume 1408.6117 covers only *orthogonal forms*, not Γ(F) itself (checked by arXiv search). |
| FFKLZ 2506.02319 Q2.4 | none | open, unowned |
| FWZ Q5.7, Q5.9 (relPBH ⇒ PBH?) | `a2-*` nodes; `a2-pair-with-non-removable-kernel-exists` OPEN | open |

## 5. This lane's results

1. **BFFHZ Question 3.3** (`bffhz-q33-is-normal-finite-generation-of-mixed-identities`,
   lane proof, elementary). For finitely presented G:
   - Q3.3 at rank k says exactly that the k-variable mixed identities J_k(G) are normally
     finitely generated in G∗F_k.
   - It descends to every lower rank, through the retraction killing the extra letters,
     which maps J_k onto J_j.
   - It forces J_1, …, J_k to be finitely based over overgroups and, with solvable word
     problem, recursive.
   - MIF groups satisfy it trivially.

   So a single fp simple group with non-finitely-based J_1 answers both Q3.2 (every n ≥ 2)
   and Q3.3 (every k) negatively. The open case is non-MIF groups such as T, where the
   question is whether J_1(T) is normally finitely generated in T∗Z.
2. **Problem 5.3(6), Attempt 1** (on `free-burnside-groups-satisfy-boone-higman`).
   - B(m,n) can never be its own type (A) or [A_2] actor, because it is not finitely
     presented. FWZ Theorem B: SV_G is fp iff G ↷ S is [A_2], and [A_2] requires G of
     type F_2.
   - So the node's first lever should read: does some *finitely presented overgroup* of
     B(2,n) admit a type (A) action?
   - Any such overgroup is non-residually-finite (Zelmanov), not hyperbolic, and not
     cubulated, so no host on main qualifies.
   - One real attempt found no candidate actor; stalled there.
3. **Checked, no result:** Q3.6 (highly transitive). Acylindrical hyperbolicity would give
   high transitivity via Hull–Osin, but it is known only for orthogonal forms (Caprace–Hume),
   not for the fp simple lattices Γ(F).

## 6. Unowned named items (for team-lead)

- 5.3(11) automatic;
- 5.3(12) fp residually finite;
- survey Q4.7 (surface groups and one-ended hyperbolic groups in V);
- BBMZ-hyperbolic Q1.1–Q1.4;
- FFKLZ Q2.4;
- BFFHZ Q3.3 for T (normal finite generation of J_1(T)).

## 7. Update (09-18, later): Q3.3 answered, Q4.7 reduced

4. **BFFHZ Question 3.3 has a negative answer**
   (`thompson-t-mixed-identities-are-not-finitely-normally-generated`, lane proof, not
   reviewed). For every n ≥ 1, the mixed identities of Thompson's T are not finitely
   normally generated in T∗F_n. The proof has three parts:
   - **Localization.** Take any mixed identity w of T. Every homeomorphism of the Cantor
     set supported in a small enough neighbourhood of a generic point satisfies w. The
     reason is that inside such a neighbourhood the word collapses to P^s, and s = 0
     because an infinite-order t ∈ T supported there must satisfy w.
   - **Separation.** Thompson's V (which contains T) breaks the circle's cyclic order at
     every scale. A three-arc identity with constants inside a tiny cone U fails for some
     P ∈ V supported in U, by a generic-trajectory argument.
   - **Conclusion.** A finite set W of identities is killed by x ↦ P, but some other
     identity is not, so it does not normally generate J_1. Descent handles every rank.

   Q3.2 for T stays open: substitution instances escape the localization.
5. **Survey Q4.7 reduced and the RAAG route to V killed** (610442438):
   - `closed-hyperbolic-surface-groups-embed-in-thompson-v` (OPEN);
   - `cocompact-fuchsian-groups-embed-in-v-all-or-none`: the question is one question for
     the whole commensurability class, e.g. π_1(Σ_2) or Δ(2,3,7);
   - `raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group`: RAAGs inside V are
     products of free groups, and no one-ended hyperbolic group virtually embeds in one.
