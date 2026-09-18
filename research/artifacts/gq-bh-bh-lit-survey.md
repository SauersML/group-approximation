# Boone–Higman literature 2022–2026: theorems, repo mapping, named open problems

Lane `bh-lit` (BH swarm), 2026-09-18. Target root: `boone-higman-conjecture`.

**Method and limits.** arXiv listing, abstract and HTML pages fetched 2026-09-18
(arXiv full-text search "Boone-Higman", newest hit arXiv:2609.01868 of 2026-09-01;
Zaremsky's author listing, newest 2608.25614). Theorem wording below is what the
HTML/abstract fetch returned; a fetch can paraphrase, so treat the quotes as
checked against the rendered page, not against the PDF. The local TeX of
Belk–Hyde–Matucci (`$GQ/src/bhm/bhm-2407.03149v1.tex`) was grepped directly. No
MathSciNet or zbMATH. Earlier repo reads are reused and cited:
`bh-survey-open-cases-status-2026-09-12.md` (survey read page by page),
`gq-gq-lit-arxiv-priority.md`, `gq-gq-lit-hosts.md`.

## 1. Papers and main theorems

| arXiv | Authors (date) | Main theorems (as returned) | Repo nodes |
|---|---|---|---|
| 2306.16356 | Belk–Bleak–Matucci–Zaremsky, survey (v3 2025-05-22) | Problem 5.3 (13 classes), Problem 2.7, Q4.7, Rem 5.4, Rem 5.5, Q5.6; see §3 | `boone-higman-conjecture`, class roots listed in §2 |
| 2306.14863 | Belk–Bleak (2023) | methods for hyperbolic groups into fp infinite simple groups | superseded by 2309.06224 |
| 2309.06224 | BBMZ (2023) | Thm A: "Every hyperbolic group embeds as a subgroup of a finitely presented simple group." Thm B: "Every full, contracting RSG is finitely presented." Thm C: every contracting RSG embeds in an fp simple group. Cor D: every contracting self-similar group does. Thm E: every hyperbolic group embeds in a full contracting RSG. | `hyperbolic-groups-satisfy-boone-higman` (+ `-citation`), `hyperbolic-groups-embed-in-contracting-rsgs` |
| 2405.10234 | Belk–Matucci (2024) | Thm 1: "Every contracting self-similar group embeds into a finitely presented simple group." (Prop 3: RN groups act oligomorphically on orbits; Lemma 4: germ groups at rational points virtually cyclic; Prop 6: finite-set stabilizers f.g.) | `local-boone-higman-conjecture` |
| 2405.09722 | Zaremsky (2024; Bull. LMS 2025) | Thm 1.1: "Every finitely presented self-similar group embeds in a finitely presented simple group." Thm 1.2: "Every finitely generated subgroup of GL_n(Q) satisfies the Boone–Higman conjecture." Ex 4.7: R^n ⋊ GL_n(R) for rings with a finite-index principal ideal J, ⋂J^k = 0. | `rational-linear-groups-satisfy-boone-higman`, `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, `polynomial-linear-groups-satisfy-boone-higman-via-zaremsky` |
| 2405.18354 | Zaremsky (2024) | Thm A: SV_G is fp iff the action is of type (A) (faithful, G fp, point stabilizers f.g., finitely many orbits on 2-subsets). Cor B: subgroups of groups with a type (A) action satisfy BH. Conj 5.1 (permutational BH). Q5.13. | `boone-higman-type-a-class-closed-under-finite-extensions`, type (A) nodes |
| 2407.03149 | Belk–Hyde–Matucci (2024) | Thm 1.1 (F∞ criterion for finite germ extensions), Thm 2.1 (level n), Cor 2.10, Thm 1.3 (G′ simple), Thm 1.6: every countable abelian group embeds in an fp simple group (VA, 2-generated, F∞, simple). Line 272 of the TeX: "the Boone--Higman conjecture remains open for the class of finitely generated metabelian groups". | `boone-higman-via-shell-germ-stabilizers`, `bhm-singfix-condition-forces-fp-germ-groups`, `germ-complex-and-bux-gonzalez-morse-inputs` |
| 2408.05673 | Bux–Llosa Isenrich–Wu (2024) | Thm A: BH for (1) Baumslag–Solitar groups, (2) free-by-cyclic groups, (3) Leary–Minasyan groups, (4) Euclidean triangle Artin groups. Thm B (10.5): G acting faithfully cocompactly on a locally finite tree with fp edge stabilizers embeds in an fp simple group. Thm C (11.1): if some nontrivial H ∈ BS_G acts faithfully on its Bass–Serre tree, every K ∈ BS_G embeds in an fp simple group. | `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`, `bliw-locally-finite-tree-theorem-b-citation`, `bs-free-by-cyclic-boone-higman-citation` |
| 2503.21882 | Belk–Fournier-Facio–Hyde–Zaremsky (2025) | Thm A: Aut(F_n) embeds in an fp simple twisted Brin–Thompson group. Cor B: MCGs of surfaces with nonempty boundary, punctures, or genus ≤ 2; braid groups; Artin types B_n = C_n, D_n, I_2(m), Ã_n; loop/ribbon braid groups. Thm C: for f.g. G with solvable WP, PBH ⟺ embeds in fp twisted BT ⟺ embeds in fp simple highly transitive ⟺ embeds in fp simple MIF group. Cor D, Thm E, Cor F (PBH closed under free products). | `aut-free-groups-satisfy-permutational-boone-higman` (+ `-citation`), `punctured-surface-mcgs-satisfy-permutational-boone-higman`, `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh` |
| 2506.02319 | Fournier-Facio–Kropholler–Lyman–Zaremsky (2025; v2 2026-02-27, to appear Publ. Mat.) | Thm 1.1: for G in the class HF (includes finite-vcd groups and **all countable linear groups**) acting oligomorphically on an infinite set, some nonempty finite subset has stabilizer not of type FP∞. Thm 1.2: B ≀_S G (B infinite) and ˢV_G are not FP∞. Cor 1.6: simple Burger–Mozes Γ gives ˢV_Γ fp but not FP∞. | `permutational-boone-higman-closed-under-wreath-products` (only). See flag F4. |
| 2510.01952 | Llosa Isenrich–Schesler–Wu (2025) | For f.g. linear G over Q, a simple group Γ with the same finiteness properties as G, with G a quasi-retract; simple FP∞ not fp groups. No new BH class (the simple groups are not fp). | `linear-groups-quasi-retract-of-simple-citation`, `lisw-theorem-1-4-citation` |
| 2512.18943 | Brothier–Seelig (2025) | infinite family of F∞ simple groups acting on the circle with no piecewise affine/projective actions. No BH content. | none (not needed) |
| 2603.24687 | Fournier-Facio–Wu–Zaremsky (2026) | Thm A (relative simplicity of abstract twisted BT groups), Thm B (fg ⟺ [A_1], fp ⟺ [A_2], F∞ ⟺ [A_∞]), Thm C: "If a group satisfies the Boone–Higman conjecture then it satisfies the relative permutational Boone–Higman conjecture." Abstract: every fp simple group embeds in an fp abstract twisted BT group. Q5.7, Q5.9. | `bh-implies-relative-pbh-citation`, `boone-higman-implies-relative-permutational-bh`, `abstract-btb-pairs-fp-and-relatively-simple-citation`, `a2-*` nodes |
| 2605.20564 | Hyde–Skipper–Zaremsky (2026) | action graphs of f.g. subgroups of V on Cantor orbits are quasi-trees; F-like groups embedded in V are semiconjugate to the line action; the Stein group F_{2,3} does not embed in V. | `stein-group-f23-does-not-embed-in-thompson-v-citation` |
| 2609.01868 | Almeida–Dantas–de Oliveira-Tosti (2026-09-01) | for G non-torsion contracting, under conditions V_m(Z^d ≀_X G) is fp and virtually simple; Z^d ≀_X G embeds in an fp simple group. | cited by `boone-higman-conjecture`, `baumslag-char-zero-metabelian-group-satisfies-boone-higman`, `free-solvable-groups-satisfy-permutational-boone-higman` |
| 2201.00711 | Zaremsky (2022) | fp groups with oligomorphic actions of the right kind embed in fp simple groups (twisted BT) | `twisted-brin-thompson-wp-equals-actor-orbit-problem` |

No 2025–2026 preprint found that settles any item of survey Problem 5.3 beyond
Remark 5.4 (BFFHZ, BLIW). No paper found that settles GL_n(Q) itself, closed-surface
MCGs of genus ≥ 3, Out(F_n) for n ≥ 3, one-relator, CAT(0), automatic, fp residually
finite, free Burnside, or Question 5.6. The search is bounded (abstract-level arXiv
search plus author listings; no citation databases).

## 2. Flags for the coordinator

**F1. The repo marks three published open problems as ESTABLISHED, by internal
lane proofs; no paper settles them.** Each rests on repo-internal reviews only.
They are either new theorems or errors, and both matter. A literature/priority
search found no prior proof (bounded search).
- `fp-metabelian-groups-satisfy-boone-higman` — ESTABLISHED 2026-09-13 through
  `fp-metabelian-bh-via-quasi-linear-pbh`, one internal PASS
  (`review-metabelian-bh-2026-09-13.md`). Open in the literature: survey Problem 5.3(7)
  and BHM 2407.03149 line 272 ("remains open for the class of finitely generated
  metabelian groups").
- `spherical-artin-groups-satisfy-boone-higman` (plain form, all types incl.
  E_6–E_8, F_4, H_3, H_4) — ESTABLISHED 2026-09-12 via
  `char-zero-linear-groups-satisfy-boone-higman`. Open per BFFHZ 2503.21882 ("remains
  open for the exceptional type spherical Artin groups") and survey Rem 5.4. Also
  `e-type-artin-groups-satisfy-permutational-boone-higman` is ESTABLISHED in the
  repo (permutational form).
- `char-zero-linear-groups-satisfy-boone-higman` (every f.g. linear group in
  characteristic 0) and `positive-char-linear-groups-satisfy-boone-higman` —
  ESTABLISHED 2026-09-12, resting on `polynomial-linear-groups-satisfy-boone-higman`
  (Zaremsky Thm 1.1 applied to R^n ⋊ E_n(Z[1/m][t_1..t_k]), plus finite presentation of
  E_n over polynomial S-integers). Not a listed survey problem, but literature
  coverage stops at f.g. subgroups of GL_n(Q) (Zaremsky Thm 1.2; the paper does not
  claim other fields).
- Also repo-only: `b-tilde-artin-groups-satisfy-permutational-boone-higman`,
  `c-tilde-artin-groups-satisfy-permutational-boone-higman` (Euclidean types the
  survey and BFFHZ list as open).
Recommendation: these are the highest-value verification targets in the whole BH
graph. They deserve a fresh adversarial proof-gap review, a primary-source check of
every import (Suslin/van der Kallen stability for E_n(Z[1/m][t]), Vaserstein, the
Kochloukova–Sidki-type self-similarity, Zaremsky Thm 1.1 hypotheses), and a
MathSciNet-level priority check before any external claim.

**F2. No repo node found that calls open something a paper settled.** The
survey's own open list is out of date against BFFHZ/BLIW, and the repo already
tracks that (`bh-survey-open-cases-status-2026-09-12.md`).

**F3. FWZ 2603.24687 bears on BBMZ-hyperbolic Question 1.6 and Zaremsky Q5.13(ii).**
Its abstract: every fp simple group embeds in an fp *abstract* twisted BT group.
Whether that answers Q1.6 ("... a finitely presented (simple) twisted Brin–Thompson
group?") depends on whether "abstract" twisted BT groups count; not decided here.

**F4. FFKLZ Thm 1.1 applies to GL_n(Q) (a countable linear group).** Any oligomorphic
action of GL_n(Q) on an infinite set has a finite subset whose stabilizer is not FP∞.
This does not exclude a type (A) = [A_2] action (which needs only f.g. point
stabilizers and finitely many orbits on 2-subsets), but it excludes type [A_∞]
actions and hence F∞ twisted BT hosts built from an oligomorphic action of GL_n(Q)
itself. Not yet recorded on `gl-n-q-in-permutational-boone-higman-class`.

## 3. Named open problems (exact wording as returned; source)

Survey arXiv:2306.16356v3 (verbatim from the page-by-page read in
`bh-survey-open-cases-status-2026-09-12.md`):
- **Problem 5.3.** "Prove the Boone–Higman conjecture for: (1) Braid groups. (2) Mapping
  class groups of surfaces. (3) The groups Aut(F_n) and Out(F_n). (4) Non-solvable
  Baumslag–Solitar groups BS(m,n), for example BS(2,3). (5) GL_n(Q). (6) Free Burnside
  groups B(m,n) with solvable word problem. (7) Finitely presented metabelian groups.
  (8) Free-by-cyclic groups. (9) One-relator groups (without torsion). (10) CAT(0)
  groups. (11) Automatic groups. (12) Finitely presented residually finite groups.
  (13) Artin groups with solvable word problem."
  Literature status: (1), (4), (8) settled; (2) settled except closed genus ≥ 3;
  (3) settled for Aut, open for Out(F_n), n ≥ 3; (13) open for exceptional spherical and
  Euclidean types other than Ã_n and triangle types. Repo status: see F1.
- **Problem 2.7** (explicit natural fp overgroup of GL_n(Q); = Kourovka 14.10(c), per
  `gq-gq-lit-arxiv-priority.md`); p. 7: "it remains an open question whether GL_n(Q)
  embeds into a finitely presented simple group."
- **Question 4.7** (fragment): "Do any one-ended hyperbolic groups embed into V? ...
  closed hyperbolic surface?"
- **Remark 5.5**: PIP homeomorphism groups of spheres (Thurston) — f.g.? fp simple?
- **Question 5.6**: "Does every finitely presented group embed as a subgroup of a type
  F∞ group?"

BBMZ, Hyperbolic groups, arXiv:2309.06224:
- **Q1.1** "Is every non-elementary hyperbolic group isomorphic to a contracting RSG?"
- **Q1.2** "Do full, contracting RSGs have type F∞?"
- **Q1.3** "Does every finitely presented subgroup of the rational group R_{Γ,E} embed in a
  finitely presented subgroup whose action on some orbit in E is oligomorphic and has
  finitely generated stabilizers of finite subsets?"
- **Q1.4** "If G is a finitely presented RSG, then must the full closure of G also be
  finitely presented?"
- **Q1.5** "Does every finitely presented group with solvable word problem embed in a
  finitely presented oligomorphic group with finitely generated stabilizers?"
  (a universal type (A)-style form of BH; relevant to lane bh-typeA-universal)
- **Q1.6** "Does every finitely presented simple group embed in a finitely presented
  (simple) twisted Brin–Thompson group?" (see F3)

Zaremsky, arXiv:2405.18354:
- **Conjecture 5.1 (PBH)** "A finitely generated group has solvable word problem if and
  only if it embeds in a group admitting an action of type (A)."
- **Q5.13** "(i) Does every finitely presented simple group admit an action of type (A)?
  (ii) Does every finitely presented simple group embed in a group admitting an action
  of type (A)?" (repo: `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`)

BFFHZ, arXiv:2503.21882:
- **Q3.1** "Let G be a graph product over a finite graph such that each vertex group
  satisfies PBH. Does G satisfy PBH?"
- **Q3.2** "For G a finitely presented simple group and n ≥ 2, is the quotient of
  Aut_G(G∗F_n) by the kernel of its action on Hom_G(G∗F_n,G) finitely presented?"
- **Q3.3** "For G a finitely presented simple group, is the quotient of G∗F_n by the
  Jacobson radical J_G(G∗F_n) finitely presented?"
- **Q3.4** "Does every finitely presented simple group embed in a finitely presented
  simple MIF group?" (repo: `fp-simple-mif-embedding-via-permutational-boone-higman`,
  OPEN)
- **Q3.6** "Are finitely presented simple Kac–Moody groups highly transitive? Are they
  MIF? Do they satisfy PBH?"
- (Q3.5 was not returned by the fetch; not transcribed.)
- Stated open: MCGs of closed surfaces of genus ≥ 3; exceptional spherical Artin types;
  Euclidean Artin groups other than Ã_n.

FFKLZ, arXiv:2506.02319:
- **Q2.4** "Does there exist a group G satisfying the hypotheses of Lemma 2.3 (with S
  infinite) that does not contain a copy of Thompson's group F?"

FWZ, arXiv:2603.24687:
- **Q5.7** whether every fp abstract twisted BT group sharply embeds in (G, ker(G↷S)) for
  some type [A_2] action (paraphrase returned).
- **Q5.9** whether (relPBH) ⇒ (PBH), and whether (relBH) ⇒ (BH) (paraphrase returned;
  repo `a2-*` nodes quote the TeX, lines 1339–1346).

BHM, arXiv:2407.03149 (TeX line 954): whether VG has the Haagerup property (remark,
not a numbered question).

Kourovka: 14.10(a) (Q; answered naturally by BHM, Bull. AMS 2022) and 14.10(c)
(GL_n(Q)); entry text not re-read here (v46 HTML too long, per the earlier lane).

## 4. What this means for lane targeting (lane remark, not a claim)

- The literature's open BH classes that the repo also has OPEN: GL_n(Q) itself;
  closed-surface MCGs of genus ≥ 3; Out(F_n), n ≥ 3; torsion-free one-relator; CAT(0);
  automatic; fp residually finite; free Burnside B(m,n); non-spherical, non-Ã Euclidean
  and general Artin groups with solvable WP (repo covers B̃_n, C̃_n; D̃_n, Ẽ_{6,7,8}, F̃_4
  open); plus BBMZ Q1.2, Q1.5, Q1.6, Zaremsky Q5.13, BFFHZ Q3.1–3.4, 3.6, survey Q5.6,
  Q4.7, Rem 5.5.
- The single most consequential action is F1: independent re-verification of the
  repo's metabelian, char-0/char-p linear and spherical-Artin claims. If they hold,
  they resolve survey Problem 5.3(7) and the spherical part of 5.3(13).
