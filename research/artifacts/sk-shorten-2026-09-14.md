# sk-shorten: the shortest complete versions of the simple Kazhdan note (2026-09-14)

Lane sk-shorten. The user asked "how can we simplify? make it shorter? etc.?" Base: rev4.3 on main (696c4b602e, md5 0648e5f8…, 841 lines, 9 pp).
Every tier keeps every proof step of what it still claims. A dropped claim takes its proof and its bibitems with it. Nothing here is landed as tex; the drafts live in `sk2/lanes/sk-shorten/`.

## 0. Result

| tier | what changes | source lines | pages (MSI TL2025, 3 passes) | log |
|---|---|---|---|---|
| rev4.3 | as landed | 841 | 9 | 0/0/0 |
| 1 | all decided fixes, no reader loss | 864 | 10 | 0/0/0, 1 underfull |
| 2 | tier 1 minus the five sharpness/consequence remarks | 789 | 9 | 0/0/0, 1 underfull |
| **2b (recommended)** | tier 2 minus four low-value remarks | **750** | **8** | 0/0/0, 1 underfull |
| 3 | tier 2b minus the solvable-WP analogue, the universal host and the continuum clause | 658 | 7 | 0/0/0, 1 underfull |

- Log counts are errors/overfull/undefined. The one underfull box is the Champetier bibitem, as in rev4.3.
- For every tier, the cited keys equal the bibitems in both directions.
- Files and md5:
  - tier1.tex 10219fdc…
  - tier2.tex 9257e0ba…
  - tier2b.tex = short.tex feff6c2e…
  - tier3.tex e4219288…
- Generated from one marked source, `src2.tex`: blocks tagged DROP2, DROP3L, DROP3, ADD2, ADD3.

**Recommendation: tier 2b (8 pp).**
- It keeps both theorems and all three corollaries at full strength: the finite-simple-limit characterization, its solvable-word-problem analogue, the universal host, and the Turing degrees with the continuum of mutually non-embeddable G_X.
- It drops only remarks that no statement uses.
- Reaching 7 pp needs tier 3, which gives up the Boone–Higman–Thompson analogue and the universal host. Those are headline-level results, and the abstract would lose a sentence.

## 1. Tier 1: the decided fixes (no reader loss; +23 source lines, the page grows 9 → 10)
Applied from `sk2/rev44-fixes-perfect-{a,b,d}.md` and `-prior-art-3.md`:
- **perfect-a:**
  - U1: 1_V for the unit of A_V.
  - U2: lamps c; units v_1, v_2 in the Whitehead display.
  - U3 + R2: E_ij defined in its own sentence.
  - U4: X is a Cantor set (+1 line).
  - U5: "from the left" twice.
  - U6 + R1: exponent sum ℓ.
  - U7: "which no single recursive bound allows".
  - U8: G_Y with L(Y) recursive (Corollary 5).
  - U9: "cannot serve as such hosts".
  - T1 + PROSE-1: the double "by".
  - T2: "They asked".
  - T3: D ⊆ ℕ.
  - T4: commutator x.
  - T5: bound W.
  - T6: coordinate η.
- **perfect-b:**
  - BIB-1: Rădulescu volume title.
  - BIB-2: Margulis plural title plus translation.
  - Abstract: now states the solvable-WP analogue and the universal host (13 lines, as before).
  - PROSE-3.
- **perfect-d:**
  - R3: mechanism before the Stepanov alternative; "Our proof is direct" dropped.
  - R4: Questions open with the question.
  - R5: Theorem 2 without "matricial", and l.124 adjusted.
  - M1: LEF defined right after Theorem 1.
  - M2: [[T]]′ ≤ G_X moved to §2.
  - §3 order: framing → Cor 3–4 → what each property alone gives → main proof → one solvable-WP block → sharpness → Osajda.
  - Cut 1: half-line merged into the WP block.
  - Cut 2: the [[T]]′ intro sentence compressed.
  - Cut 4: "countably many" joined.
  - Renames.
- **prior-art-3:**
  - F1 (MUST): Neumann–Neumann credit at the wreath commutator, plus bibitem.
  - F2 (MUST): Darbinyan's half-line form, plus bibitem.
  - F4: "By a construction of Sacks".
- **Not applied:** perfect-d cut 3 (Theorem 1's EL_n sentence is kept); prior-art-3 F3 (optional non-LEF non-exact clause).

## 2. Ranked cuts (source lines include each removed bibitem)

| rank | cut | tier | lines | reader cost (one sentence) |
|---|---|---|---|---|
| 1 | Separable-factor count for L(G_X): §4 paragraph plus OzawaUniversal and NPS | 2 | −20 | Loses the operator-algebra corollary, that each separable II_1 factor holds countably many G_X; it is an application of Ozawa's argument, not needed by any statement. |
| 2 | SL_3(Z) ∉ G_X: paragraph plus CFKP | 2 | −18 | Loses the sharpness showing why lamplighter hosts are needed; nothing else uses it. |
| 3 | No decidable universal host: paragraph plus KMS and Rauzy | 2 | −15 | Loses the sharpness of Cor 4 on the word problem; Cor 4 itself stays. |
| 4 | [[T]]′ ≤ G_X: §2 paragraph, intro sentence, JuschenkoMonod | 2 | −13 | Loses the memorable fact that G_X contains the Juschenko–Monod amenable simple groups. |
| 5 | Osajda non-exact hosts: remark plus bibitem | 2 | −7 | Loses the C*-side contrast (non-exact yet R^ω-embeddable). |
| 6 | Kirchberg/LLP sentence in Brown's formulation | 2b | −8 | Loses the proof of Ozawa's LLP remark quoted in the intro. That remark stays cited to Ozawa p. 527, so no claim is lost. |
| 7 | Stepanov alternative plus ClarkEdie and Stepanov bibitems | 2b | −14 | Loses the credit that simplicity also follows from Stepanov's theorem; a referee may ask for it, since it is credit, not a claim. |
| 8 | Grigorchuk–Medynets decidability sentence plus GMpres | 2b | −8 | Loses the classical parallel for derived full groups; pure context. |
| 9 | "Quotients of hyperbolic Kazhdan groups, Kac–Moody lattices" sentence plus Gromov87 | 2b | −9 | Loses background on known simple Kazhdan groups. Caprace–Rémy stays cited in Questions and CFF in §3. |
| 10 | Solvable-WP analogue: Cor 3's second sentence, framing, half-line overgroup, WP transfer, BooneHigman, Thompson80, Darbinyan15 | 3 | −57 | Loses the Boone–Higman–Thompson analogue for LEF groups, the strongest structural addition of rev4.2. |
| 11 | Universal host: Cor 4's second and third statements plus proof lines | 3 | −11 | Loses "one host holds every recursively presented f.g. LEF group"; Cor 4 keeps only "every countable LEF group lies in such a group". |
| 12 | Continuum of mutually non-embeddable G_X: clause plus proof plus Odifreddi | 3 | −10 | Loses the non-embeddability upgrade; nonisomorphism would still follow from the degrees. |
| 13 | Abstract and roadmap follow each tier (automatic) | all | 0 | None. |

**Rejected cuts, which would lose proof steps or clarity:**
- the finite-models paragraph (each sentence carries a step);
- the Sturmian word-problem proof (the digit argument is already one sentence);
- the lamplighter model paragraph (the covariance display was requested by referee (a), U7);
- the background sentences on naming and Pestov–Kwiatkowska (printed motivation).

## 3. Where the page goes
- **Tier 1 grows by one page** because the fixes add credit: the Neumann–Neumann and Darbinyan clauses with 2 bibitems, the "Each property alone was known" framing, U4, and the Margulis translation.
- **Tier 2** recovers that page.
- **Tier 2b** gains a page beyond rev4.3 while keeping every headline result.
- **Tier 3** drops the last headline material, which costs about 1.9 pages of source.

## 4. Status
- Every block in the tiers comes verbatim from rev4.3 (reviewed by sk-rev4-referee-a/b, sk-rev42-referee, sk-perfect-a/b) or from the reviewed fix files. The exceptions are the new connective sentences:
  - "Each property alone was known."
  - "A half-line form of the Neumann–Neumann construction, used by Darbinyan to preserve solvable word problems, keeps it."
  - "This proves Corollaries 3 and 4." (tier 3 only)
  - The §3 opening "Kionke and Schesler asked which groups embed in finitely generated simple amenable groups".
- The compiled PDFs are on MSI in `/scratch.global/sauer354/sk/shorten/`.
