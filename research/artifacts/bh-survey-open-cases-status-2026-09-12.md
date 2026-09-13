# Boone–Higman survey open cases: status in Cairn at the live tip

Lane `bh-survey-open-cases`, 2026-09-12.

- **Tip read:** `0a9c95f79`. Each status below is the bold status line of the
  node body, not `FRONTIER.md`.
- **Source:** Belk–Bleak–Matucci–Zaremsky, *Progress around the Boone–Higman
  conjecture*, arXiv:2306.16356, read from the PDF page by page (pp. 1–24).
  This is the version whose Remark 5.4 cites BFFHZ [11] and Bux–Llosa
  Isenrich–Wu [40]; `boone-higman-frontier-2026-09-12.md` §3 calls it v3.
- **Literature check:** arxiv.org listing and abstract pages, fetched locally on
  2026-09-12. The arXiv API and search pages answer "Rate exceeded." from MSI,
  but e-print downloads from MSI work. The newest Boone–Higman hit is
  2609.01868.

## 1. Survey wording

**Problem 5.3 (p. 17, verbatim).** "Prove the Boone–Higman conjecture for:
(1) Braid groups. (2) Mapping class groups of surfaces. (3) The groups Aut(F_n)
and Out(F_n). (4) Non-solvable Baumslag–Solitar groups BS(m,n), for example
BS(2,3). (5) GL_n(Q). (6) Free Burnside groups B(m,n) with solvable word
problem. (7) Finitely presented metabelian groups. (8) Free-by-cyclic groups.
(9) One-relator groups (without torsion). (10) CAT(0) groups. (11) Automatic
groups. (12) Finitely presented residually finite groups. (13) Artin groups
with solvable word problem."

**Footnotes.**
- **Footnote 9, on (7):** every f.g. metabelian group embeds in a finitely
  presented one (Baumslag, Remeslennikov). Such groups have solvable word
  problem; this fails in derived length three [69].
- **Footnote 10, on (13):** whether all Artin groups have solvable word problem
  is open. It is known for right-angled, spherical [54] and Euclidean [85]
  types.

**Remark 5.4 (p. 18).**
- **Bux–Llosa Isenrich–Wu [40]:** all Baumslag–Solitar groups and all
  free-by-cyclic groups, so (4) and (8) are fully handled. They also do the
  Euclidean triangle Artin groups.
- **BFFHZ [11]:** all Aut(F_n). This covers braid groups, mapping class groups
  of surfaces with nonempty boundary or at least one puncture, and Artin groups
  of types A_n, B_n = C_n, D_n, I_2(m) and Ã_n.
- **Verbatim:** "Item (2) remains open for mapping class groups of closed
  surfaces of genus 3 or greater, item (3) remains open for Out(F_n) for all
  n ≥ 3, and item (13) remains open for many classes of Artin groups, including
  those of exceptional spherical type and those of Euclidean type other than the
  Ã_n and triangle cases (C̃_2 and G̃_2)."

**Other named questions.**
- **Remark 5.5 (p. 18):** mapping class groups of closed surfaces act by PIP
  homeomorphisms on the Thurston boundary, a sphere of dimension 6g − 7. Thurston
  asked whether the groups of PIP homeomorphisms of higher-dimensional spheres
  are f.g. If they are finitely presented and simple, that gives a Boone–Higman
  embedding.
- **Question 5.6 (p. 18, verbatim):** "Does every finitely presented group embed
  as a subgroup of a type F∞ group?" It follows Leary [83, §21].
- **Question 4.7 (fragment, from the earlier read):** "Do any one-ended
  hyperbolic groups embed into V? ... closed hyperbolic surface?"
- **p. 7, after Corollary 3.5 (verbatim):** "it remains an open question whether
  GL_n(Q) embeds into a finitely presented simple group."
- **Problem 2.7:** an explicit natural finitely presented group containing
  GL_n(Q), as transcribed in `boone-higman-frontier-2026-09-12.md` §3.

## 2. Status table

"None needed" means the item is settled. "Unstaffed" means no live lane; the
live lane names come from the coordinator directive of 2026-09-12.

| Item | Status now | Cairn node → body status at `0a9c95f79` | Staffing |
|---|---|---|---|
| 5.3(1) braid groups | settled, BFFHZ [11] | `aut-free-groups-satisfy-permutational-boone-higman` → ESTABLISHED (literature import) | none needed |
| 5.3(2) mapping class groups | settled with a puncture or boundary, and for closed genus ≤ 2; open for closed genus ≥ 3 | `punctured-surface-mcgs-satisfy-permutational-boone-higman` → ESTABLISHED (literature import); `closed-surface-mapping-class-groups-satisfy-boone-higman` → OPEN, Attempts 1–5 (the BFFHZ method, covering lifts, a punctured host, linear hosts, PIP) | unstaffed; the earlier lane was not resumed |
| 5.3(3) Aut(F_n), Out(F_n) | Aut settled [11]; Out open for n ≥ 3 | `out-free-groups-satisfy-boone-higman` → OPEN; `out-free-groups-virtually-embed-in-aut-free-groups` → OPEN; `aut-out-free-abelianized-extension-splits-rationally` → ESTABLISHED | live: `bh-out-fn-into-aut-fm` (artifact `bh-out-fn-into-aut-fm-2026-09-12.md`: not settled) |
| 5.3(4) BS(m,n) | settled [40] | `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman` → ESTABLISHED (literature import) | none needed |
| 5.3(5) GL_n(Q) | f.g. subgroups settled (Zaremsky arXiv:2405.09722, Thm 1.2, as imported). Not re-checked against that paper here: does the countable group GL_n(Q) itself embed? That is the p. 7 question. | `rational-linear-groups-satisfy-boone-higman` → ESTABLISHED (literature import) | none |
| 5.3(6) free Burnside B(m,n) | open; the survey gives no further input on p. 17 | no Boone–Higman node. The `fpbs-burnside-*` and `restricted-burnside-*` nodes are about cost and approximation, not embeddings. | unstaffed |
| 5.3(7) fp metabelian | open | `fp-metabelian-groups-satisfy-boone-higman` → OPEN; `baumslag-char-zero-metabelian-group-satisfies-boone-higman` → OPEN; `global-field-soluble-linear-products-satisfy-boone-higman` → ESTABLISHED (soluble groups linear over number fields and over char-p fields of transcendence degree ≤ 1) | covered by an earlier lane; no live lane |
| 5.3(8) free-by-cyclic | settled [40] | same node as (4); `virtually-free-by-cyclic-groups-satisfy-boone-higman` → ESTABLISHED | none needed |
| 5.3(9) torsion-free one-relator | open | `one-relator-groups-satisfy-boone-higman` → OPEN; `magnus-hnn-permanence-forces-one-relator-boone-higman` → ESTABLISHED (conditional theorem); `baumslag-gersten-group-satisfies-boone-higman` → OPEN (landed `c6d492eb1`) | live: `bh-baumslag-gersten`; earlier lane artifact `one-relator-boone-higman-2026-09-12.md` |
| 5.3(10) CAT(0) | open | no node. `bh-type-a-permanence-2026-09-12.md` §1: the rational-embedding preprint of Belk–Bleak–Chatterji–Matucci–Perego gives no finite presentation of the full groups. | unstaffed |
| 5.3(11) automatic | open | no node; same note. Contains E_6–E_8 Artin groups and closed-surface mapping class groups. | unstaffed |
| 5.3(12) fp residually finite | open | `fp-residually-finite-boone-higman` → OPEN; route `fp-rf-boone-higman-via-fp-self-similar-overgroups` | unstaffed; the earlier lane was not resumed |
| 5.3(13) Artin groups | open for exceptional spherical types, and for Euclidean types other than Ã_n, C̃_2, G̃_2 | §3 below | unstaffed; lane `bh-artin-solvable-wp` was not resumed |
| Remark 5.5, PIP groups | open | Attempt 5 of the closed-surface node | unstaffed |
| Question 5.6, fp ⊂ type F∞ | open | no node | unstaffed |
| Question 4.7, one-ended hyperbolic groups in V | open | no node | unstaffed |
| p. 7 and Problem 2.7, GL_n(Q) | see 5.3(5) | `rational-linear-groups-satisfy-boone-higman` | none |

Not in the survey, but open or active in Cairn:

| Item | Cairn node → body status | Staffing |
|---|---|---|
| char-0 linear groups | `char-zero-linear-groups-satisfy-boone-higman` → OPEN; `algebraic-linear-groups-satisfy-boone-higman` (number fields) → ESTABLISHED; `positive-char-linear-groups-satisfy-boone-higman` → ESTABLISHED (2026-09-12); `leavitt-subalgebra-linear-groups-satisfy-boone-higman` → ESTABLISHED (conditional on the imported finite presentation) | live: `bh-sl3-zt-host`, `bh-number-field-linear`. The number-field node already reads ESTABLISHED at this tip. |
| finite direct products of BH groups | `boone-higman-closed-under-finite-direct-products` → OPEN. The type (A) class is closed under products: `boone-higman-type-a-class-closed-under-finite-extensions`, credited to Zaremsky arXiv:2405.18354 Prop. 5.6. | live: `bh-simple-products-embed` |

## 3. Item (13) by type

| Type | Status | Source or node |
|---|---|---|
| A_n, B_n = C_n, D_n, I_2(m) | settled | BFFHZ Cor. B, via `aut-free-groups-satisfy-permutational-boone-higman` |
| F_4, H_3, H_4 | reduce to E_6–E_8 | Crisp 1999, as quoted in Paris arXiv:0711.2372 §6; `spherical-artin-boone-higman-reduces-to-e6-e7-e8` (conditional reduction) |
| E_6, E_7, E_8 | open | `e-type-artin-groups-satisfy-permutational-boone-higman` → OPEN; `spherical-artin-groups-satisfy-boone-higman` → OPEN. Linear over Q(x,y) (`spherical-artin-groups-are-linear-over-q-x-y`), so they fall inside the char-0 question. |
| Ã_n | settled | BFFHZ Cor. B |
| C̃_n, all n | settled in Cairn | `c-tilde-artin-groups-satisfy-permutational-boone-higman` → ESTABLISHED (A(C̃_n) ≤ B_(n+2)). The survey still lists n ≥ 3 as open. |
| Ã_2, C̃_2 = B̃_2, G̃_2 | settled | [40], Euclidean triangle groups |
| B̃_n, n ≥ 3 | settled in Cairn by this lane | `b-tilde-artin-groups-satisfy-permutational-boone-higman` → ESTABLISHED, landed `8bd8f63a9`. A(B̃_n) ≤ Aut(F_M) through the Li–Roushon fibration; see §4. The survey still lists it as open. |
| D̃_n, n ≥ 4 | open | no fibration with f.g. free fibres is known; see §4 |
| Ẽ_6, Ẽ_7, Ẽ_8, F̃_4 | open | no structural input found |
| other types with solvable WP (2-dim, large, FC, ...) | open in general | `admissibly-oriented-artin-groups-satisfy-boone-higman` → OPEN; `artin-groups-satisfy-boone-higman` → OPEN |

Blockers for B̃_n and D̃_n already recorded in `bh-artin-groups-2026-09-12.md` §5:
- **Cone points:** Allcock's orbifold models have them (index 2 for B̃_n, index
  4 for D̃_n).
- **Foldings go the wrong way:** C̃_n ↪ B̃_(n+1) ↪ D̃_(n+2).
- **No finite-index embedding of A(D_n) in A(B_n)** (b_1 transfer).
- **Perron–Vannier geometric representation** is faithful only for A_n and D_n.

## 4. Target chosen, and why

Unstaffed items ranked by how much existing Cairn machinery bears on them:

1. **(13), type B̃_n.**
   - **Input:** Li–Roushon, arXiv:2403.09533v2 (Bull. Sci. Math. 206 (2026),
     103760), prove A(B̃_n) virtually poly-free using a fibration whose fibres
     are punctured surfaces of finite type.
   - **Mechanism:** a normal free subgroup N of finite rank ≥ 2 has trivial
     centre, so g ↦ (conjugation by g on N, gN) embeds G in Aut(N) × G/N.
   - **Assembly:** combine this with
     `aut-free-groups-satisfy-permutational-boone-higman` and
     `boone-higman-type-a-class-closed-under-finite-extensions`. If a group
     commensurable with A(B̃_n) contains such an N with quotient in the type (A)
     class, then A(B̃_n) lies in that class.
   - **To check against the source:** the model space and its relation to
     A(B̃_n); the base group; exactness on the left.
   - **Outcome (2026-09-12): proved.**
     - All three points check out against the source.
     - The base group is the pure braid group P_(n+1), which lies in
       Aut(F_(n+1)).
     - Krasner–Kaloujnine inside Aut(F_M) replaces the finite-extension closure.
     - Nodes: `b-tilde-artin-complement-fibres-over-configuration-space`
       (literature import, landed `3f00db1ab`) and
       `b-tilde-artin-groups-satisfy-permutational-boone-higman` (landed
       `8bd8f63a9`).
     - Artifact: `bh-b-tilde-artin-2026-09-12.md`.
2. **(13), type D̃_n.** Same method, but no fibration is available.
   - Flechsig, arXiv:2305.04273, shows the pure orbifold braid sequence has a
     nontrivial kernel K. That corrects Roushon, arXiv:2006.07106, Thm 2.14.
   - Li–Roushon report that the earlier poly-free claims for B̃_n and D̃_n need a
     new proof; they supply one only for B̃_n.
3. **(2) closed-surface MCGs, and (3) Out(F_n).** Both are quotient-type
   problems. Out(F_n) is staffed, and every closed-surface attempt died.
4. **(12), (10), (11).** No Cairn host reaches them: see
   `complexity-bounded-host-classes-are-not-universal`, and there is no finite
   presentation of the rational full groups.
5. **(6) Burnside, Questions 4.7 and 5.6.** No Cairn machinery applies.

## 5. Post-survey literature read in this lane (abstract pages, 2026-09-12)

- **2609.01868:** a Boone–Higman family of wreath products Z^d ≀_X G over
  non-torsion contracting G. Settles no Problem 5.3 item.
- **2603.24687v2 (Fournier-Facio–Wu–Zaremsky):** abstract twisted Brin–Thompson
  groups. No new input class.
- **2605.20564:** F_{2,3} does not embed in V.
- **2503.21882v2 (BFFHZ):** Aut(F_n), with braid, loop braid and ribbon braid
  groups, non-closed surface MCGs, and certain Artin groups.
- **2405.09722 and 2405.18354 (Zaremsky):** fp self-similar groups embed in fp
  simple groups; the finite-presentation criterion for SV_G.
- **Also read, none settling a further Problem 5.3 item:** 2512.18943,
  2506.02319, 2408.05673, 2407.03149, 2405.10234, 2309.06224.
- **Artin structure:**
  - 2403.09533v2 (Li–Roushon), B̃_n virtually poly-free;
  - 2006.07106 (Roushon; its comments point to 2305.04273 for a correction);
  - 2305.04273 (Flechsig);
  - 2007.02779 (merged into 2006.07106).
- **Result of the check:** no paper found embedding A(B̃_n) or A(D̃_n) in a
  Boone–Higman group, or proving them linear.
