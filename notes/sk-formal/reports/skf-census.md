# Lane skf-census: sentence census of simple_kazhdan_sofic_group.tex

Target: origin/main's note at bf961c128 (340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99), per the 18:58 re-scope.

## Tooling

- `scripts/sk_sentence_census.py` is new. It imports `scripts/sentence_census.py` unmodified and keeps its keying
  (sha256 of the normalized sentence, first 12 hex digits), anchoring and join. Three changes:
  1. abbreviations are protected only at a word boundary, so "killed." and "trivial." end sentences;
  2. every display (`\[...\]`, `$$...$$`, math display environments) is its own row, text `[display] <body>`;
  3. each row records the lines where it starts and ends (`line`, `end`).
- Outputs: `metadata/SK_SENTENCE_CENSUS.tsv` (columns key, line, end, section, env, label, status, decls, sentence)
  and `.md`. The overlay is `metadata/SK_SENTENCE_MAP.tsv`, written only by `--merge`.
- The front matter and the bibliography are not rows, the same as in the non-MF census.
- Runs only on MSI, with python 3.11.

## How lanes key rows

Land rows in `metadata/sk-census-rows/<lane>.tsv` as `key<TAB>status<TAB>decls<TAB>note`.
- A 12-hex key from `SK_SENTENCE_CENSUS.tsv` always applies.
- `LINE:<n>@bf961c128` applies when line n meets exactly one row. If several rows meet it, it applies when exactly one
  starts there. A `\begin{...}` line resolves to the row that starts on the next line.
- A heading, bibliography or blank line has no row, so such keys are reported and skipped.
- These lines start two rows each, so key them by hash: 38, 70, 77, 131, 166, 171, 185, 206, 268.
- Statuses: formalized | partial | definition | structural | attribution | provenance | open. `open` is reserved for
  sentences that state an open question.

## Merge 1 (tex bf961c128)

124 rows (112 prose sentences, 12 displays):

| status | rows |
|---|---|
| unassigned | 105 |
| attribution | 9 |
| open | 8 |
| formalized | 1 |
| partial | 1 |

20 of 24 lane rows merged (skf-cite, skf-degrees). Not merged:
- skf-cite LINE:264, the heading `Origin and authorship`, and LINE:271, the bibliography;
- skf-cite LINE:268, which starts rows `56609be15469` and `a51fe087e1a2`;
- skf-degrees LINE:229, the section heading.

Grading issue for the owners: the 8 `open` rows (skf-degrees ×7, skf-cite ×1) are proved statements with no carrier
yet, not open questions. They should be `partial` with the residual named, or left unassigned.

Nothing keyed to b965d63ba had landed, so nothing needed superseding.
