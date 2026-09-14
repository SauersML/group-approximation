# SK roster I: revision 4 referees (launched by main when rev4 is ready)

The target is `$SK/drafts/rev4.tex`, as reported ready by sk-editor-4: main names the md5 in the launch message, and you referee THAT file.
- Line numbers refer to that file.
- The decisions it implements are items 79–103 in `wip/simple-kazhdan-note/decisions.md` on main.
- Both rev3 referee reports are `research/artifacts/sk-rev3-referee-{a,b}-2026-09-13.md`.
- FALSE, never use: diag(a,a^{-1},1) as a homomorphism; the "double swap" γ ↦ (γ,γ^{-1}); Kirchberg Cor 1.2 item (v) as printed.

Label every finding ERROR / GAP / UNCLEAR / FREE STRENGTHENING / CUT, with verbatim before/after LaTeX and its cost in lines.
- Land `research/artifacts/sk-rev4-referee-<a|b|c>-2026-09-13[-partK].md` via skland.sh.
- SendMessage main at once on an ERROR or GAP.
- Final verdict to main, ≤ 60 lines.
- Referees do not read each other's reports before landing their own.

## sk-rev4-referee-a (correctness)
Re-derive every mathematical sentence by hand. Priorities:
- **Theorem 2**, the general engine: hypotheses, density patch, tower transvection with word length, level-ideal covering, LEF from the kernel of the ultraproduct map.
- **S1:** simplicity is proved first, and marked convergence plus N_k → ∞ follow from injectivity for every ω, with no nonvanishing lemma.
- **The headline:** configuration-space models ONTO M_N(F_2); the e_ij(1) commutator clause for the lamplighter ring (G1/F5); the Kazhdan constant transfer.
- **The universal host** and no decidable host.
- **The SL_3(Z) obstruction:** the Krylov count needs w ≥ 1.
- **[[T]]′ ≤ G_X** via diag(w_g,1,1).
- **The separable-factor paragraph:** distinct kernels, one alphabet.
- **Brown's formulation + Kirchberg** (Cor 1.2 (ii)⇒(i)).
- **Word problems** and the compressed Sturmian proof.

## sk-rev4-referee-b (credit, exposition, claims proved)
Check:
- that every claim of the title, abstract and theorem statements is proved or correctly cited in the text;
- every `\cite` key and locator;
- the credit additions: Clark–Edie-Michell Cor 4.6, Mal'cev, Coulon–Fournier-Facio Thm 1.5, Boone–Higman, Kionke–Schesler framing, Rauzy, KMS Thm 4.21, Ozawa 2004 Thm 2, NPS Thm 0.1, Alekseev–Thom §5, Cyr–Franks–Kra–Petite, Matui, Juschenko–Monod;
- that no sentence says "first", "answers Ozawa's question", "only known example", or claims to answer Kionke–Schesler's amenable question or CFKP 5.1–5.3;
- prose doctrine (RULES §6): so/then not hence, no metacommentary, American English;
- no Codex, OpenAI or Astra anywhere.

## sk-rev4-referee-c (length and elegance)
At the level of an Annals referee who wants the shortest complete paper. For every paragraph: does it earn its length? Deliver:
- a ranked CUT list with line savings, where each cut keeps every proof step a referee needs;
- the three sentences a reader remembers, and whether page 1 states the one idea;
- whether the section order serves the reader;
- whether the title and abstract match what is proved.

Do not propose new mathematics.
