# Boone–Higman swarm: state of the attack (09-18, first full summary)

Lane `bh-writeup`, 2026-09-18, written from the node texts on main at `f2fbbe643`
(09:44 CDT). About 226 BH-lane landings are covered. Each entry's status is quoted
from the node's own first status line.

**How to read the statuses.**
- *Lane proof* means that the lane that wrote the proof is the only one that has
  checked it.
- *Internal check* means another swarm lane re-derived it (bh-verify-*, bh-free-10/11,
  bh-referee-c).
- *Referee a/b* means the swarm's gq-referee-a (proof gaps) or gq-referee-b
  (citations) passed it.
- None of this is external review. The user waived referee passes as a landing gate
  on 09-18, so **most entries below are unreviewed lane proofs**.
- **Priority checks were arXiv-only** (API, listings, HTML). MathSciNet and Google
  Scholar were not reachable, so no entry claims novelty. An expert read is needed
  before any external claim.

The root `boone-higman-conjecture` stays **OPEN**. No route to it has every
requirement established.

## 1. Named or printed open problems answered on main

| Problem (source) | Answer | Node | Status |
|---|---|---|---|
| Kourovka 17.59 (Kohl): is CT(Z) the group of RCWA permutations of Z fixing N_0 setwise? | **Yes** | `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` | lane proof; the 21st issue (2026) lists it unsolved |
| Kourovka 17.60 (Kohl): are the CT_P(Z) pairwise non-isomorphic? | **Yes**, for all sets P of odd primes, finite or infinite | `ct-p-z-groups-are-pairwise-nonisomorphic` (supersedes the \|P\| = \|Q\| partial node) | lane proof; a second proof with a different invariant is in `gq-bh-bh-free-11-ct-p-z-second-proof.md` |
| Kourovka 17.61 (Kohl): is CT_P(Z) finitely presented for finite P? | **Yes**: CT_P(Z) is the full group of an explicit one-vertex (\|P\|+1)-graph, simple and of type F_∞ | `ct-p-z-is-a-one-vertex-k-graph-full-group` | lane proof; Li, Matui and FKPS inputs read at source |
| BFFHZ (2503.21882) Q3.1: graph products of PBH groups are PBH? | **Yes**, over finite graphs, plus retract amalgams X *_C (C × K) | `pbh-class-closed-under-graph-products` | lane proof; two internal re-checks (bh-free-10, bh-free-11) found no gap |
| BFFHZ Q3.3: is (G ∗ F_n)/J_G finitely presented for f.p. simple G? | **No**: Thompson's T fails at every rank n | `thompson-t-mixed-identities-are-not-finitely-normally-generated`, with the reformulation `bffhz-q33-is-normal-finite-generation-of-mixed-identities` | lane proofs |
| Zaremsky 2405.18354 Q5.13(i) and BFFHZ Q3.4, instance: Lodha's f.p. simple circle group S | **Positive instance**: S acts on P^1(Q) with type (A), transitively on ordered pairs, so SV_S is f.p. simple and S is PBH | `lodha-simple-circle-group-has-a-type-a-action` | lane proof. Also new Q3.4 census lines for circle PL groups T(l;A,P), V-type PL groups V(l;A,P), Stein V-groups |
| LISW (2510.01952) Q1.11: every f.g. linear group into a f.g. self-similar group? | **Yes, even a f.p. one**, over any field | `fg-linear-groups-embed-in-fp-self-similar-groups` | lane composition of main's linear chain, not reviewed as a composition. LISW Q1.10 (quasi-retracts) stays OPEN |
| Zaremsky, Oberwolfach Report 26/2018 Q110: Higman's group into Lodha–Moore groups or Monod's H(R)? | **No**: every homomorphism is trivial | `higman-group-embeds-in-no-lodha-moore-or-monod-group` | corollary of the 09-13 node `higman-group-embeds-in-no-piecewise-analytic-circle-group`; lane proof |
| BBMZ-hyperbolic (2309.06224) Q1.4, contracting case | **Yes** for contracting RSGs | `contracting-rsgs-have-fp-full-closures` | lane proof. The general Q1.4 (`fp-rsgs-have-fp-full-closures`) stays OPEN |
| BBMZ-hyperbolic Q1.1, freely decomposable case | **Yes** for free products of hyperbolic groups and for virtually freely decomposable hyperbolic groups | `free-products-of-hyperbolic-groups-are-contracting-rsgs`, `virtually-free-product-hyperbolic-groups-are-contracting-rsgs` | lane proofs. The general Q1.1 stays OPEN |
| BBMZ-hyperbolic Q1.5 and Q1.6 | **Reformulated**: Q1.5 ⇔ PBH; Q1.6 ⇔ BFFHZ Q3.4 | `bbmz-oligomorphic-and-twisted-questions-are-pbh-forms` | referee a PASS |

**Literature lists these as open; main marks them ESTABLISHED.** Each is either a new
theorem or an error, and each has had only internal checks.
- **BBMZ survey Problem 5.3(7), f.p. metabelian groups** (`fp-metabelian-groups-satisfy-boone-higman`).
  - Reviewed internally on 09-13 (`review-metabelian-bh-2026-09-13.md`).
  - On 09-18 bh-verify-metabelian re-derived the chain end to end: PASS modulo standard
    inputs.
  - BHM 2407.03149 (l.272) and arXiv through 2609.01868 still list it as open.
- **Every f.g. linear group over any field** (`finitely-generated-linear-groups-satisfy-boone-higman`,
  a new union node at ff3174b2a).
  - bh-verify-linear: PASS for both characteristics.
  - The literature reaches only f.g. subgroups of GL_n(Q) (Zaremsky 2405.09722 Thm 1.2).
  - The one idea not found in the literature is the parameter-coordinate self-similar
    action of R^N ⋊ E_N(R), over R = Z[1/m][s] and F_p[s].
- **Spherical Artin groups of exceptional type** (`spherical-artin-groups-satisfy-boone-higman`).
  - This is part of 5.3(13). BFFHZ say it "remains open for the exceptional type
    spherical Artin groups".
  - bh-verify-artin gives PASS, *conditional on* the linear chain.
- **Euclidean types B̃_n and C̃_n** (PBH form).
  - BFFHZ list Euclidean types other than Ã_n as open.
  - bh-verify-artin gives PASS. These rest on published theorems (BFFHZ Thm A,
    Charney–Crisp, Li–Roushon) plus short arguments.

## 2. New host constructions and classes embedded

All entries below are lane proofs, not reviewed, unless marked otherwise.

**Hosts.**
- `cantor-cover-germ-extension-of-v-is-fp-simple`: the full germ extension of V by all
  germs commuting with its dyadic germs is f.p. simple and contains the lamplighter
  C(C,Z) ⋊ V and Q. It is a Cantor analogue of Belk–Hyde–Matucci's VA, and may
  coincide with a known group.
- `one-fp-simple-group-contains-every-brin-thompson-subgroup`: the group DV_F contains
  every subgroup of every nV. The host is Belk–Zaremsky's, and no priority is claimed.
  `circulant-graph-wreath-products-satisfy-boone-higman` puts Z wr_Γ Z, for cofinite
  connection sets, into DV_F.
- `periodic-germ-extensions-of-v-are-virtually-simple` (F_∞, with a simple commutator
  subgroup), `two-radix-odometer-host-is-f-infinity-with-fg-charge-kernel`, and
  `odometer-2v-orbit-action-is-type-a`. The last makes the twisted Brin–Thompson group
  of 2V_τ f.p. simple, with BS(1,2) having a base of infinite entropy.
- `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`: central Z-extensions of
  subgroups of V, when the class dies on the action groupoid, embed in the F_∞ simple
  group 2V_τ.
- Non-simple overgroups, for context:
  - `elementary-shift-group-contains-every-integral-linear-group`: E(Z) ⋊ Z, a
    three-generated group containing every integral linear group.
  - `finitary-steinberg-extensions-by-oligomorphic-actions-are-fp`: a f.p. group
    containing every GL_n(Z).
  - A single f.p. *simple* host for all integral linear groups remains OPEN
    (`one-fp-simple-group-contains-every-integral-linear-group`).

**Classes (embed in a f.p. simple group, or lie in B_A).**
- *Free-group extensions.* Ascending HNN extensions of f.g. free groups:
  `ascending-hnn-of-free-groups-satisfy-boone-higman`, which is F_∞ simple.
  - One-relator groups meeting the Sapir–Špakulová or Brown criteria follow:
    `almost-all-one-relator-groups-satisfy-boone-higman`. The generic statement is not
    new.
  - Free-by-virtually-free groups follow from Bux–Llosa Isenrich–Wu:
    `free-by-virtually-free-groups-satisfy-boone-higman`.
  - Generalized BS groups over closed surface groups:
    `surface-generalized-bs-groups-satisfy-boone-higman`.
  - Free-by-B_A and surface-by-B_A extensions:
    `free-by-pbh-and-surface-by-pbh-groups-lie-in-type-a-class`,
    `free-kernel-extensions-stay-in-the-permutational-class`.
- *CAT(0) and lattices.* Groups acting geometrically on (hyperbolic plane) × tree
  (referee a PASS), (symmetric space) × tree, and products with a tree factor
  (referee a+b PASS). Irreducible tree lattices with just-non-compact closures, via
  Bader–Shalom. Arithmetic Lie lattices have faithful Hecke members in their BS class
  (referee a PASS). Tree lattices split into irreducible blocks.
- *Artin groups.*
  - Forest Artin groups, and triangle-free all-3 Artin groups.
  - Reductions: to free-of-infinity groups, along folding separators, through hub cones.
  - `euclidean-artin-toric-commensurability`: A(X̃) ∈ B_A iff the toric Weyl complement
    group of X is.
  - `weyl-toric-arrangements-b-d-e-f-are-not-fiber-type` shows toric bundles cannot
    reach D̃_n, Ẽ_{6,7,8} or F̃_4.
- *Automaton and self-similar groups.*
  - `lift-presented-automaton-groups-satisfy-boone-higman` (referee a+b PASS), with
    spinal and finitary extensions.
  - Eventually periodic Grigorchuk groups G_ω. All G_ω lie in one-point germ
    extensions of V.
  - Grigorchuk's f.p. amenable group, and a bounded action for the spine-Grigorchuk
    group.
  - Linear-activity automata can have Nekrashevych groups that are not f.p.
- *Amenable and dynamical.*
  - Topological full groups of primitive aperiodic substitution subshifts, and of
    their products.
  - The SMART trace full group, a Juschenko–Monod group, inside 2V.
  - Sturmian Juschenko–Monod groups when the quadratic field has a unit of norm −1.
  - Quadratic-irrational interval exchange groups and rectangle exchange groups.
- *Piecewise groups.*
  - Dyadic-slope PL groups with rational breakpoints.
  - Piecewise PSL_2(Z) groups with rational and quadratic breakpoints.
  - Lodha–Moore groups, inside Lodha's S.
  - Houghton groups, inside V (standard).
- *Other.*
  - The free center-by-metabelian group of rank 2 (PBH, via a new 4×4 linear
    representation). Rank ≥ 4 is linear iff residually finite.
  - F.g. residually finite soluble groups of finite rank (PBH).
  - Fiber-type toric and elliptic arrangement groups.
  - Relatively hyperbolic groups re-embedded with f.p. simple peripherals.

## 3. Reductions of Boone–Higman

**Houghton-like envelopes (Mallery–Zaremsky).**
- `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`: for n ≥ 2 the germ
  group of H_n(E_ν(P)) is f.p. exactly when the near-shift group R_ν is. Referee a PASS
  for items 1–4.
- `free-shift-houghton-like-envelopes-are-not-fp`: free-shift enumerations pass the
  germ gate but never give f.p. envelopes. This **refutes** the lifting claim
  `houghton-like-envelopes-lift-finite-presentation-from-germs`.
- The route `decidable-inputs-have-fp-houghton-like-shift-envelopes` stays OPEN; a
  witness ν must carry near relations.

**Shell gates.**
- `genuine-action-shell-envelopes-generalize-the-regular-shell`: shells work for any
  action with infinite supports.
- `eventually-periodic-genuine-shell-actions-give-fp-envelopes`: these give f.p.
  envelopes, and exist **exactly for virtually abelian inputs**, including one-ended Z^2
  with window 0. This is a calibration and a ceiling, not new BH.
- Nodes that pass the germ gate:
  - `twisted-genuine-shell-actions-pass-both-germ-gates` (endomorphism twists);
  - `fp-window-group-makes-shell-germ-group-fp`;
  - `finite-index-odometer-near-shift-groups-pass-the-germ-gate`;
  - `finite-index-in-a-kernel-fg-near-host-passes-both-germ-gates`.
- Obstructions for one-ended and rigid inputs:
  - `one-ended-near-regular-actions-have-a-realization-defect`;
  - `one-ended-schreier-orbits-force-index-zero`;
  - `fw-inputs-admit-no-twisted-normalizing-genuine-shell-action`.
- The St_N(R_L) shell instance (gq lanes), which contains every GL_n(Q):
  - K_2(R_L) ≅ Q^×, and this isomorphism is computable on Steinberg words.
  - So the word-problem gate reduces to injectivity of K_2(N,R_L) → K_2(R_L), i.e.
    vanishing of the stabilization kernel. That is OPEN.

**Index sets (bh-logic, lane proofs).**
- `boone-higman-is-equality-of-two-sigma-3-index-sets`: BH holds iff EMB = DEC, and DEC
  is Σ_3-complete.
- `embedding-in-fp-simple-groups-is-sigma-3-complete`: unconditionally, EMB is
  Σ_3-complete, already for embedding in the single group DV_F.
- `common-decidable-hosts-iff-uniform-word-problem`: a class has a common decidable
  host iff its word problem is uniform.
- `simplicity-of-finite-presentations-arithmetical-position`: simplicity of finite
  presentations lies in Π^0_2 and is Σ^0_1-hard.
- OPEN: `boone-higman-uniform-in-word-problem-algorithms`, and
  `fp-embeddability-index-set-is-sigma-3-complete` (proved under the weaker hypothesis
  MH).

**Algebra gate.**
- `germ-steinberg-algebras-over-v-are-fg-central-simple`, used by the route
  `boone-higman-via-germ-steinberg-algebra-presentation`.
- `shell-germ-algebra-fp-forces-bounded-germ-presentation`.
- OPEN: `shell-germ-steinberg-algebra-is-finitely-presented` and
  `shell-germ-algebra-fp-forces-fp-germ-group`.
- `field-representable-algebras-have-fp-simple-envelopes`, and char-p rational function
  fields in f.p. simple algebras.

**Permanence.**
- `bh-class-free-products-iff-joint-embedding-and-free-z`: the BH class is closed under
  free products iff f.p. simple groups have the joint embedding property (OPEN) and
  U ∗ Z embeds.
- `bh-class-decidable-amalgams-from-free-products-and-hnn`.
- `bh-class-finite-extensions-reduce-to-finite-simple-wreaths`.
- `rel-hyperbolic-bh-permanence-implies-free-product-closure`.
- PBH is equivalent to embedding in f.p. dense Cantor actors, or in full Cantor hosts.
- The countable-input form is equivalent to BH (referee-c PASS).

## 4. Separators and red-team results

A disproof of BH is exactly a subgroup-closed class containing every f.p. simple group
but missing some decidable f.g. group.
- `bh-separators-must-omit-nested-decidable-hosts` (referee a+b PASS):
  - every separator must omit a simple Kazhdan FA decidable group lying inside a f.p.
    decidable group;
  - hereditary decision-problem separators are dead.
- `coarse-embeddability-separates-boone-higman` (referee a PASS): BH fails if every f.p.
  simple group coarsely embeds in Hilbert space. Its witness is
  `decidable-group-with-coarsely-embedded-expanders-exists` (referee a PASS).
- `baum-connes-with-coefficients-separates-boone-higman`: the same shape, for BCC. The
  heredity input is cited, not re-read.
- `decidable-graphical-non-exact-groups-exist`: Osajda's constructions with solvable
  word problem.
- Complexity:
  - `small-cancellation-groups-realize-every-wp-complexity`: no single decidable group
    contains them all;
  - `finite-k-graph-full-groups-have-exponential-word-problem`: finite k-graph full
    groups are not universal hosts;
  - `bhm-corollary-hosts-over-v-are-cover-centralizer-groups`: BHM Cor. 2.10 cannot
    carry BH.
- Rigidity inside germ extensions of V:
  - `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`;
  - `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group`;
  - `kazhdan-subgroups-of-almost-v-have-no-central-v-elements`;
  - `deligne-lattice-in-almost-v-sits-in-one-germ-group` (referee a PASS).
- Torsion (the Burnside side of 5.3(6)), none bounded-exponent:
  - the full-shift topological full group is torsion locally finite and residually
    finite;
  - torsion subgroups of almost-automorphism groups are residually finite;
  - periodic subgroups of circle and tree-product groups are finite;
  - 2-dimensional CAT(0) product groups are torsion locally finite.
- `bg-in-isometric-brick-hosts-needs-unbounded-exponents` (referee a+b PASS):
  Baumslag–Gersten in nV-type hosts.
- `lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction`.
- `relative-finite-discrimination-forces-solvable-word-problem`.
- **Prediction** (`gq-bh-bh-refute-frontier.md`): if BH holds, a single f.p. simple
  group exists that is non-exact, not coarsely embeddable, fails BCC, contains an
  infinite f.g. bounded-exponent group, and has word problem beyond any given recursive
  bound. Each property is a separate OPEN node.

## 5. Corrections and refutations

**Refuted by swarm nodes.**
- `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic` is **REFUTED as stated**:
  type-preserving groups never give primitive matrices. It is repaired by
  `rs-strip-tail-transitivity-forces-primitive-transition-matrices` and a certificate
  for seven explicit CMSZ groups.
- `houghton-like-envelopes-lift-finite-presentation-from-germs` is **REFUTED** (§3).
- `fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers` is **REFUTED** by
  `v-and-a-homeomorphism-never-generate-a-free-product`: ⟨V, t⟩ is never V ∗ ⟨t⟩.

**Superseded or duplicate.**
- `ct-p-z-isomorphism-type-remembers-the-number-of-primes` is superseded by the full
  Kourovka 17.60 answer.
- `fp-simple-groups-can-contain-infinite-finite-exponent-groups` is marked DUPLICATE.

**Literature status corrected.**
- `fp-simple-group-with-commutator-width-at-least-two` was answered by Caprace–Fujiwara
  (2010) before the AIM list recorded it.
- bh-lit flag F3 is resolved: FWZ 2603.24687 does not answer BBMZ-hyperbolic Q1.6.

**Wording and status fixes.**
- referee-c, char-two linear node: its conditionality belongs in the status line, and
  two nodes misstate Zaremsky.
- referee-c, GL_n(Q)-in-twisted-BT node: the title holds only for infinite H.
- Stale "not reviewed" lines on the char-p PBH and self-similarity nodes were fixed
  (ff3174b2a).
- Trust notes now say that every elementary-group host can take N ≥ 5, where the
  refereed rank-five proof replaces the unread Krstić–McCool import.

**Hygiene, open.** `gq-bh-bh-kourovka-problems.md` (item 7.19) lists "automatic" among
the BH classes on main, but `automatic-groups-satisfy-boone-higman` is OPEN. The
artifact's owner should fix it.

## 6. Sharpest open questions (from the nodes; ranked by reach × impact)

1. **External verification** of §1's "literature lists open" block, and of the Kourovka
   and BFFHZ answers. This check is in reach, and it decides whether main already holds
   answers to several printed problems.
2. **One-ended shell success**: a one-ended input that is not virtually abelian, with
   f.p. E_ν. SL_3(Z) is the calibration input (critic U1). Also St_N(R_L)'s gate:
   vanishing of the stabilization kernel.
3. **Joint embedding for f.p. simple groups** (`fp-simple-groups-have-the-joint-embedding-property`),
   which by §3 is equivalent to free-product closure of the BH class.
4. **Single test groups**, each with most host families already dead:
   - Higman's H4 (`higman-group-satisfies-boone-higman`);
   - Baumslag–Gersten;
   - B(2,665), for 5.3(6);
   - Deligne's lattice;
   - Osajda's decidable non-exact group.
5. **Named classes still open**:
   - Out(F_n), 5.3(3): `out-free-groups-virtually-embed-in-aut-free-groups`. The
     abelian level virtually splits; the class-2 obstruction is one quadratic equation;
     class ≥ 2 is open.
   - Closed MCG, 5.3(2): `closed-mcg-virtually-embeds-in-fp-full-cantor-group`. Any
     nV host must also contain braid groups.
   - One-relator groups, 5.3(9).
   - CAT(0) groups, 5.3(10).
   - Automatic groups, 5.3(11).
   - F.p. residually finite groups, 5.3(12).
   - Euclidean Artin groups D̃_n, Ẽ_{6,7,8} and F̃_4, now a question about toric complement
     groups.
6. **Kourovka 17.57**, reduced to local rigidity of normalizers of CT(Z).
7. **BFFHZ Q3.2 for T**, and **Q3.6**: high transitivity of Kac–Moody lattices.
