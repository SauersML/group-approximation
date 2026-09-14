# Revision 4.2 changelog (sk-editor-5, 2026-09-13)

- **Base:** `sk/drafts/rev41.tex`, md5 b55c0d23b8c59e66d36df004a1df608b, 767 lines. This is main's landed rev4.1 at 37551fd939.
- **Outputs:**
  - `sk/drafts/rev42.tex` = C3 + C1 + S.
  - `sk/drafts/rev42-fq.tex` = the same plus the every-finite-field subsection.
- **Script:** `sk/lanes/sk-editor-5/apply42.py`. It applies eight exact replacements and asserts that each old string occurs exactly once.

## Sources
- **C3:**
  - `research/artifacts/sk-decidable-host-proposal-2026-09-13.md` P1–P4 and `research/artifacts/sk-decidable-host-2026-09-13.md` §§1–4;
  - review: sk-verify-14 part3, 91db46d85d (PASS, notes N1–N2);
  - sizing: sk-rev4-referee-c §C3.
- **C1:** `research/artifacts/sk-free-7-proposal-2026-09-13.md`; review: sk-verify-15 part1, 9b301bef72 (PASS). Locator per sk-verify-6 part6 and main: \cite[Chapter~V]{Odifreddi}, with no p. 462.
- **S:** `research/artifacts/sk-free-1-proposal-2026-09-13.md` Version S; review: sk-verify-15 part1 (PASS).
- **F_q:** `research/artifacts/sk-fq-port-proposal-2026-09-13.md` §b (0a77fefe9a); review: sk-verify-15 part4, 867eb089d0 (PASS-WITH-FIXES).

## Applied (rev41 line numbers; deltas approximate, in source lines)

| item | where | change | delta |
|---|---|---|---|
| C3 credit | l.304–310 | "It parallels the theorem of Boone and Higman …" → "Its second statement is the analogue for LEF groups of the theorem of Boone and Higman … in the form of Thompson's strengthening, where the simple group is finitely generated and has solvable word problem~\cite{Thompson80}." | +2 |
| C3 statement | Cor 3, l.312–317 | Appended verbatim: "It is LEF with solvable word problem if and only if this group can be chosen with solvable word problem." | +2 |
| C3 overgroup | new paragraph after l.354 | Half-line overgroup Δ = ⟨β, h_s⟩ on Γ×Z: [β,h_s] multiplies level 0 by s^{-1}; ball description; finite models on Q^{[-3r,3r]}×Z/5r via the transversal bijection κ intertwining the level shift θ, with ζvζ^{-1} = θ(v). Conjugation identity for \|ℓ\| ≤ r, multiplicativity, injectivity (5r > 2r, f determined on \|m\| ≤ 3r). "the rest of the proof applies to it." Letters β, h_s, κ, ζ, ψ, θ, ℓ avoid clashes with σ_n, τ_s, t_k, k, I. | +25 |
| C3 first statements | l.402–404 | "This proves Corollary 3 and the first statement of Corollary 4. For the second, …" → "This proves the first statements of Corollaries 3 and 4. For the second statement of Corollary 4, …". | 0 |
| C3 word problem | new paragraph before \end{proof} | WP(Δ) from WP(Γ) (exponent sums, values of f at change levels). WP(Λ) and the values of c from WP(Δ). Entries Σ p_ξ u_ξ with p_ξ polynomials in coordinates, as u_ξ e_U u_ξ^{-1} = indicator of {x(δ) = 1+c(δ)}. Full shift ⇒ finite check. Converse: f.g. subgroups keep solvable WP, and LEF passes to subgroups. | +21 |
| S | after \end{proof} of Cor 3–4 | "Applied to the finitely generated residually finite non-exact groups of Osajda~\cite{OsajdaRF}, Corollary~\ref{cor:lef} gives infinite simple Kazhdan LEF groups that are not exact, since exactness, that is, property~A, passes to subgroups." | +5 |
| slot | l.292–293 | rev42: the "% rev4.1 SLOT" comment is deleted ("leave no slots"). rev42-fq: replaced by the subsection. | −3 |
| C1 statement | cor:wp | "Every Turing degree occurs." → "Every Turing degree occurs, and there are continuum many groups $G_X$, none of which is isomorphic to a subgroup of another." | +1 |
| C1 proof | end of the proof of cor:wp | +3 sentences: WP only goes up along embeddings of f.g. groups; the antichain of size continuum~\cite[Chapter~V]{Odifreddi}; the groups G_{X_α} with α of these degrees. | +5 |
| bib | after NPS | Odifreddi (Vol. I, Stud. Logic Found. Math. 125, North-Holland, Amsterdam, 1989) and OsajdaRF (GAFA 28 (2018) 509–517, doi 10.1007/s00039-018-0432-4). | +7 |
| bib | after Thom | Thompson80 (details below). | +6 |
| F_q (rev42-fq only) | after Brown's formulation | §b of the sk-fq-port proposal, with F1 ("The transvections place the copy $S_V\cong\SL_d(\F_q)$ in $G$; …") and F2 ($Z(G)$ throughout for the center). "centre" → "center" (American English, RULES §6). W1 and W3 not applied. | +17 |

## Credit checks run by this lane
- **Thompson80 bibitem:**
  - zbMATH Zbl 0431.20030: "Thompson, Richard J. Embeddings into finitely generated simple groups which preserve the word problem. Word problems II, Stud. Logic Found. Math. Vol. 95, 401-441 (1980)."
  - Crossref: doi 10.1016/s0049-237x(08)71348-x, pages 401–441, 1980, publisher Elsevier, ISBN 9780444853431.
  - Printed without publisher or city; neither record states them.
- **Content of Thompson's theorem:** two printed secondary statements agree.
  - Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224, source l.145: "This was improved by Thompson to include that the simple subgroup can be taken to be finitely generated \cite{thompson80}".
  - Darbinyan–Steenbock, arXiv:2504.12707 pp. 1, 4, quoted in sk-answered-questions part2: "every finitely generated group G with decidable word problem Frattini embeds into a finitely-generated simple group H that also has decidable word problem" [Tho80].
- **OsajdaRF:** Crossref confirms GAFA 28(2), 509–517, 2018, author Osajda.

## Compile (MSI `/scratch.global/sauer354/sk/editor5`, texlive/2025, pdflatex ×3; md5 identical on both ends)

| file | lines | md5 | errors | overfull | undefined | underfull | pages | last page |
|---|---|---|---|---|---|---|---|---|
| rev42.tex | 840 | 45539a94772d569ac819dab9dae90941 | 0 | 0 | 0 | 1 (Champetier) | 9 | p.9: 47 text lines of about 79, refs [29]–[49] |
| rev42-fq.tex | 857 | ed1d4f82e4d183a50acec2285bff49e7 | 0 | 0 | 0 | 1 (Champetier) | 10 | p.10: 10 text lines, refs [45]–[49] |

- **Citations:** both files have 49 bibitems, all cited; Rauzy's \cite spans a line break. No undefined \ref.
- **Wording:** no Codex/OpenAI/Astra/Connes/"only known"/"hence"/"centre". "first" appears only in "first coordinate", "first statement(s)" and "apply the first".
- **References** start on page 8 in both files.

## Overflow (not cut, per main)
- rev42 is 9 pp, about 0.6 page over the 8-page budget. rev41's page 8 had 53 of about 79 lines, and rev42 adds about 73 source lines.
- The C3 overgroup paragraph runs 24 source lines and the WP transfer 20, against referee (c)'s target of at most 10 lines, because every proof step is kept:
  - ball description, conjugation identity, multiplicativity, injectivity;
  - WP(Δ), WP(Λ), the normal form of entries, the full-shift check, the converse.
- rev42-fq is 10 pp; its page 10 holds only 5 references.
