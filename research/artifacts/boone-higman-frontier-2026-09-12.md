# Boone–Higman: literature frontier, 2026-09-12

Lane `bh-lit-map`, Boone–Higman swarm. Statements were read from the source
PDFs, extracted on MSI (`/scratch.global/sauer354/bhlit`), or from arXiv
abstract pages where marked. This is a bounded search: arXiv abstract pages,
the survey's own list, four full PDFs, and targeted web searches.

**Conjecture** (Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356v3 abstract):
"A conjecture of Boone and Higman from the 1970's asserts that a finitely
generated group G has solvable word problem if and only if G can be embedded
into a finitely presented simple group." Only the embedding direction is open.
Its converse is Proposition 3.1 of the survey: "Every finitely presented simple
group has solvable word problem."

## 1. Sources read

| Source | Version read | What it settles |
|---|---|---|
| BBMZ, *Progress around the Boone–Higman Conjecture*, arXiv:2306.16356 | v3, 22 May 2025; to appear in EMS Surveys in Mathematical Sciences | Theorem 5.1 (known classes), Problem 5.3 (open list), Remark 5.4 (updates) |
| Zaremsky, *Embedding finitely presented self-similar groups into finitely presented simple groups*, arXiv:2405.09722 | v2, 21 Jan 2025 | Thm 1.1 (fp self-similar), Thm 1.2 (f.g. subgroups of GL_n(Q)) |
| Belk–Matucci, *Boone–Higman embeddings for contracting self-similar groups*, arXiv:2405.10234 | v1, 16 May 2024 | contracting self-similar groups, short proof |
| BBMZ, *Hyperbolic groups satisfy the Boone–Higman conjecture*, arXiv:2309.06224 | v3, 20 Aug 2025 (abstract page); Duke Math. J. | hyperbolic groups, via contracting rational similarity groups |
| Bux–Llosa Isenrich–Wu (BLIW), *On the Boone–Higman Conjecture for groups acting on locally finite trees*, arXiv:2408.05673 | v2, 24 Jan 2025 (abstract page) | all Baumslag–Solitar groups, all free(f.r.)-by-cyclic groups, Euclidean triangle Artin groups |
| Belk–Fournier-Facio–Hyde–Zaremsky (BFFHZ), *Boone–Higman embeddings of Aut(F_n) and mapping class groups of punctured surfaces*, arXiv:2503.21882 | v2, 14 Apr 2025 | Aut(F_n) and consequences; permutational BH (PBH) |
| Fournier-Facio–Wu–Zaremsky (FFWZ), *Abstract twisted Brin–Thompson groups*, arXiv:2603.24687 | v2, 2 Apr 2026 (abstract page; Lemma 5.5 / Question 5.9 already audited in `boone-higman-2026-08-30-literature-and-level-audit.md`) | every fp simple group embeds in an fp abstract twisted BT group |
| Belk–Bleak, *Embedding hyperbolic groups into finitely presented infinite simple groups*, arXiv:2306.14863 | v1 | expository |
| Mikaelian, *An explicit algorithm for the Higman Embedding Theorem*, arXiv:2507.04347 | v8, 3 Jun 2026 (abstract page) | explicit Higman embedding; no simple target |

No 2026 preprint proving a new Boone–Higman class turned up, apart from this
repository's own positive-characteristic result.

## 2. Classes known to satisfy Boone–Higman

Survey Theorem 5.1, verbatim: "The following groups embed into finitely
presented simple groups:
(1) The groups GLn(Z).
(2) Virtually nilpotent and virtually polycyclic groups.
(3) Right-angled Artin groups.
(4) Coxeter groups.
(5) Limit groups.
(6) Graph braid groups.
(7) Fundamental groups of compact 3-manifolds that admit a Riemannian metric
of nonpositive curvature.
(8) Fundamental groups of finite-volume hyperbolic 3-manifolds.
(9) One-relator groups with torsion.
(10) Countable abelian groups.
(11) Countable locally finite groups.
(12) Contracting self-similar groups and finitely presented self-similar groups.
(13) Hyperbolic groups."

The survey's mechanism is embedding in GL_n(Z) (Scott 1984, Theorem 4.8), or
virtually in a RAAG and hence in SL_n(Z) (Hsu–Wise). Remark 5.2: every RAAG
embeds in 2V (Salo), so items (3)–(9) all lie in the single fp simple group 2V.
Item (10) is Belk–Hyde–Matucci 2023 (Theorem 4.11).

Added since v1, all verbatim unless marked:
- **Zaremsky Thm 1.1:** "Every finitely presented self-similar group embeds in
  a finitely presented simple group, and hence satisfies the Boone–Higman
  conjecture."
- **Zaremsky Thm 1.2:** "Every finitely generated subgroup of GL_n(Q)
  satisfies the Boone–Higman conjecture." The same paper says "now we know they
  all satisfy the Boone–Higman conjecture" of S-arithmetic groups in
  characteristic 0. The proof goes through a criterion (Example 4.7) for GL_n(R)
  to embed in an fp self-similar group, for rings R "with certain properties".
- **BLIW abstract:** "we prove the Boone--Higman Conjecture for all
  Baumslag--Solitar groups and for all free(finite rank)-by-cyclic groups". The
  survey's Remark 5.4 adds "Euclidean triangle Artin groups".
- **BFFHZ Theorem A:** "For each n, the group Aut(F_n) embeds in a finitely
  presented simple group, and hence satisfies the Boone–Higman conjecture." It
  holds in the permutational form, with the simple group a twisted
  Brin–Thompson group.
- **BFFHZ Corollary B:** mapping class groups of surfaces of finite type with
  non-empty boundary or a puncture; the braid groups B_n; Artin groups of types
  B_n = C_n, D_n, I_2(m) and Ã_n; loop braid groups, extended loop braid groups,
  ribbon braid groups.
- **BFFHZ Corollary D, from the abstract:** "finitely presented twisted
  Brin–Thompson groups are universal among finitely presented simple groups
  that are highly transitive."
- **BFFHZ abstract:** "satisfying the permutational Boone–Higman conjecture is
  closed under free products." They cite [Zarb] for stability under
  commensurability and direct products.
- **FFWZ abstract (paraphrase):** every fp simple group embeds in an fp
  *abstract* twisted Brin–Thompson group. If Boone–Higman holds, a related
  characterization of solvable word problem inside twisted BT groups also holds.
- **This repository, reviewed** (`research/artifacts/review-boone-higman-leavitt-tensor-hosts-2026-09-12.md`,
  be6dc41fc): every f.g. linear group over a field of characteristic p with
  transcendence degree ≤ 2 embeds in an fp simple Leavitt tensor unit group,
  modulo scalars at odd p. It rests on Khanh arXiv:2609.08428v1, which is
  unrefereed. None of the sources above states any positive-characteristic
  linear class.

## 3. Open classes named by the survey

Problem 5.3, verbatim: "Prove the Boone–Higman conjecture for:
(1) Braid groups.
(2) Mapping class groups of surfaces.
(3) The groups Aut(Fn) and Out(Fn).
(4) Non-solvable Baumslag–Solitar groups BS(m,n), for example BS(2,3).
(5) GLn(Q).
(6) Free Burnside groups B(m,n) with solvable word problem.
(7) Finitely presented metabelian groups.
(8) Free-by-cyclic groups.
(9) One-relator groups (without torsion).
(10) CAT(0) groups.
(11) Automatic groups.
(12) Finitely presented residually finite groups.
(13) Artin groups with solvable word problem."

Status after Remark 5.4 (v3) and Zaremsky v2:

| Item | Status |
|---|---|
| (1) braid groups | SETTLED (BFFHZ) |
| (4) Baumslag–Solitar | SETTLED (BLIW) |
| (5) GL_n(Q) | SETTLED (Zaremsky Thm 1.2) |
| (8) free-by-cyclic | SETTLED (BLIW) |
| (2) mapping class groups | open for closed surfaces of genus ≥ 3 |
| (3) Out(F_n) | open for n ≥ 3; Aut(F_n) done |
| (6) free Burnside groups with solvable word problem | OPEN |
| (7) fp metabelian groups | OPEN |
| (9) torsion-free one-relator groups | OPEN |
| (10) CAT(0) groups | OPEN |
| (11) automatic groups | OPEN |
| (12) fp residually finite groups | OPEN |
| (13) Artin groups | open for exceptional spherical types, and for Euclidean types other than Ã_n and the triangle cases |

Related open questions:
- **Survey Problem 2.7:** an explicit natural fp group containing GL_n(Q).
- **Survey Question 5.6:** does every fp group embed in a type F∞ group?
- **Survey Remark 5.5:** the route to mapping class groups of closed surfaces
  through PIP homeomorphisms of spheres (Thurston's question).
- **Already audited in Cairn:** FFWZ Question 5.9 (finitely normally generated
  kernels); BFFHZ Questions 3.2–3.3.
- **Not listed by the survey,** but not covered by any theorem above either:
  f.g. linear groups in characteristic 0 beyond GL_n(Q), i.e. over number fields
  or transcendental extensions. Whether Zaremsky's Example 4.7 criterion reaches
  them was not checked here.

## 4. Algebra analogues

- **Survey §3, verbatim:** "analogs of the Boone–Higman theorem have been
  proven for lattice-ordered groups [63] and left-orderable groups [21, 52], as
  well as certain other algebraic structures such as rings of characteristic p,
  magmas, loops, and lattices [57], but the corresponding statement for
  semigroups appears to be much more difficult [84]."
  - [21] is Bludov–Glass, Proc. LMS 99 (2009).
  - [52] is Darbinyan–Steenbock, J. LMS 105 (2022).
  - [57] is T. Evans, K. I. Mandelberg, M. F. Neff, *Embedding algebras with
    solvable word problems in simple algebras—some Boone–Higman type theorems*,
    Studies in Logic 80 (1975) 259–277.
- **Scope caution:** "the Boone–Higman theorem" here is the survey's Theorem 3.6
  / 3.8 form: embedding in a (computably presented, or finitely generated)
  simple subalgebra of a finitely presented algebra. It is NOT the
  finitely-presented-simple-envelope statement. The EMN primary text was
  paywalled (HTTP 403) and was not read.
- **Belyaev (1976–78), secondary source only:** an analogue of Higman's
  embedding theorem for associative algebras over a field that is a finite
  extension of its prime subfield (reported in a Bokut–Chen Gröbner–Shirshov
  survey). The primary was not read.
- **Not found:** any theorem embedding every associative algebra with solvable
  word problem in a *finitely presented simple* algebra. Cairn's premise
  `decidable-group-algebras-have-fp-central-simple-hosts` goes beyond the
  published algebra analogues found here.

## 5. Per-lane notes

| Lane | Already known, don't re-prove |
|---|---|
| char p, all degrees | No published positive-characteristic linear class; ours (be6dc41fc) is outside the survey list. EMN [57] "rings of characteristic p" is only a BH-theorem analogue. |
| char 0 linear | GL_n(Z) (Scott 1984); f.g. subgroups of GL_n(Q), including S-arithmetic groups in char 0 (Zaremsky Thm 1.2, Example 4.7 criterion); virtually polycyclic groups and everything virtually in a RAAG (survey Thm 5.1). Update from lane `bh-char-zero-linear` (103b2b683, 51d7bbe89): algebraic char-0 fields are done by restriction of scalars into GL_{nd}(Q) plus Zaremsky Thm 1.2 (`algebraic-linear-groups-satisfy-boone-higman`, no novelty claimed); the Example 4.7 criterion stops at transcendence degree 0 (`affine-self-similar-coordinate-rings-are-one-dimensional`); L_A(1,2)^× is never simple over a f.g. char-0 domain (`char-zero-leavitt-unit-groups-have-congruence-kernels`). Open: positive transcendence degree, e.g. SL_3(Z[t]) and f.g. subgroups of GL_n(Q(t)) (root `char-zero-linear-groups-satisfy-boone-higman`). |
| decidable algebra hosts | See §4; no fp simple envelope theorem for algebras found. |
| twisted Brin–Thompson | Belk–Zaremsky 2022 twisted BT groups (survey Thm 4.13); BFFHZ Thm A, Cors D and F; PBH closed under commensurability, direct products and free products; FFWZ abstract twisted BT groups. |
| geometric new class | §2 and §3: hyperbolic groups, RAAGs, Coxeter groups, limit groups, NPC and finite-volume hyperbolic 3-manifolds, one-relator groups with torsion, BS groups, free-by-cyclic groups, groups acting on locally finite trees (BLIW method), Aut(F_n), braid groups, punctured mapping class groups are DONE. Open targets: closed-surface MCGs (g ≥ 3), Out(F_n), CAT(0), automatic, torsion-free one-relator, fp metabelian, Burnside with solvable WP, fp residually finite groups, remaining Artin groups. |
| Leavitt path / Steinberg | Hosts used in the literature: V and nV (Salo: 2V contains all RAAGs), Scott groups Sc(n), Röver–Nekrashevych commutator subgroups (Zaremsky), rational similarity groups (BBMZ), twisted BT groups. No Leavitt unit group host appears in these sources. |
| complexity obstruction | Survey §4: no fp simple group contains every fp group with solvable word problem, because of the uniform word problem. |

New citation claims landed with this artifact:
`hyperbolic-groups-satisfy-boone-higman`,
`baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman` and
`aut-free-groups-satisfy-permutational-boone-higman`, each with a citation route.
