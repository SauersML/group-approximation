# sk-typesetting proposal, part 2: rev3 check and bibliography order (2026-09-13, ~20:25)

Part 1 (landed 067c1208f9): `research/artifacts/sk-typesetting-proposal-2026-09-13.md` checked main's rev2 (e80dcf20a, md5 4ad49212…).
- Main's tex is unchanged as of tip 1db46142dd.
- This part checks rev3 in progress and adds P10 (bibliography order).
- It also corrects part 1's false "alphabetical order" line.

## 0. What was checked (sk-editor-3's rev3 in progress)
- `sk/drafts/rev3.tex` (19:55): 507 lines, md5 99aab8a5…
- A fresh join `cat rev3-partA.tex rev3-partB.tex rev3-partC.tex`: 530 lines, md5 316d5f57….
  - The parts are newer (20:00).
  - The join adds `\cite{MorseHedlund38}`, `\cite{Hedlund44}`, `\cite{GPS99,BezuglyiMedynets}`, an EJZ locator in the expander step, and wording changes.
  - Treat the join as the current rev3 until the editor re-assembles.
- Both variants: no Codex, OpenAI or Astra anywhere; every `\cite` preceded by `~`; every cited key has a bibitem and every bibitem is cited.

## 1. Compile evidence (MSI, texlive/2025, pdflatex 3 passes, `/scratch.global/sauer354/sk/sk-typesetting/`)

| file | md5 | ERR | OVF | UNF | UNDEF | pages |
|---|---|---|---|---|---|---|
| rev3.tex as assembled | 99aab8a5 | 0 | 0 | **2** | 0 | 6 |
| rev3 parts joined | 316d5f57 | 0 | 0 | **2** | 0 | 6 |
| rev3 as assembled + P1–P7, P9 | 722d46c4 | 0 | 0 | 0 | 0 | 6 |
| rev3 parts + P1–P7, P9 | b40c70b5 | 0 | 0 | 0 | 0 | 6 |
| rev3 parts + P1–P7, P9 + P10 | 708270ec | 0 | 0 | 0 | 0 | 6 |
| main rev2 + P1–P7, P9 + P10 | 899bca3e | 0 | 0 | 0 | 0 | 5 |

- The two underfull boxes in rev3 are the same as in rev2: the Brown and Ozawa bibitems, badness 1389 and 1132, caused by `\href{…}{arXiv:…}` ids that cannot break. P1 removes both.
- Bookmarks in rev3 (both variants): "4. Questions" > "Origin and authorship". So P7 still applies. After P7 "Origin and authorship" is a top-level bookmark.
- The typeset copies are in the lane dir: `main-typeset.tex` (rev2 with everything) and `rev3-cat-typeset.tex` (rev3 parts with everything).

## 2. Status of part 1's items in rev3
All items apply unchanged. The script in §4 matches patterns, not line numbers, so it survives re-assembly.
- **P1 `\arxiv` macro:** 4 hrefs in rev3 (AlekseevThom, Brown, KionkeSchesler, Ozawa preprint).
- **P2 Ozawa DOI last:** applies.
- **P3 MSC:** rev3's part join already reads `05C48, 16S35, 20E26, 20F10, 22D10, 37B10, 46L10`. The only change left is `22D10` → `22D55` (22D55 is "Kazhdan's property (T), the Haagerup property, and generalizations"; checked on zbMATH).
- **P4 `\keywords`:** absent in rev3; applies.
- **P5 `pdfkeywords`:** absent; applies.
- **P6 `\hfill$\square$` → `\qed`:** one occurrence (end of the proof of Theorem 1); applies.
- **P7 `\subsection*{Origin and authorship}` → `\section*{…}`:** applies.
- **P8:** still withdrawn. Crossref's title "…propertyT…" supports the italic `$T$`.
- **P9 POMI abbreviation:** applies.

## 3. P10 (new): the bibliography in true alphabetical order
- **The defect.** amsart's `thebibliography` prints entries in source order and numbers the citations in that order. The source order is not alphabetical:
  - In main (rev2) and in both rev3 variants, `GM` and `GMpres` (Grigorchuk–Medynets) precede `GPS` (Giordano–Putnam–Skau), but "Giordano" < "Grigorchuk".
  - In the rev3 parts, `Hedlund44` sits after `Matui`, and the order has `GPS99` after `GMpres`.
- **Correct order for rev3** (by first author surname, then year): AlekseevThom, BezuglyiMedynets, Brown, EJZ, GPS, GPS99, GM, GMpres, Hedlund44, Kassabov, KionkeSchesler, Kirchberg, Matui, MorseHedlund38, MorseHedlund, Ore, Ozawa, Pestov, Stepanov, Thom, VershikGordon, Wilson.
- **Correct order for rev2:** AlekseevThom, Brown, EJZ, GPS, GM, GMpres, Kassabov, Kirchberg, Matui, MorseHedlund, Ozawa, Pestov, Stepanov, Thom, VershikGordon.
- **Checked:**
  - Morse–Hedlund 1938 then 1940, and GPS 1995 then 1999 (same authors, ordered by year).
  - "Kionke" < "Kirchberg" and "Matui" < "Morse" were already right.
  - The compile after reordering is clean, and the `\bibcite` numbers in the .aux follow the new order.
- (c) 0 lines; the entries move. (d) The reader finds a reference where alphabetical order says it is, and the citation numbers increase along the bibliography as in any AMS paper.

## 4. The patch, to apply in one step
Run on the final rev3 source, in the lane dir or anywhere:
`perl patch3.pl < rev3.tex | perl order.pl > rev3-typeset.tex`. The scripts are in `sk/lanes/sk-typesetting/`. Each item is a no-op if already applied. P1–P9 (without P8) are regex substitutions; P3 maps 22D10 → 22D55, adds 46L10 if absent, and sorts the secondary codes.

patch3.pl (P1–P7, P9):
```perl
undef $/; my $t = <STDIN>; my @log;
sub note { push @log, $_[0]; }
if ($t !~ /\\newcommand\{\\arxiv\}/) { if ($t =~ s/(\\newcommand\{\\doi\}\[1\]\{[^\n]*\n)/$1\\newcommand{\\arxiv}[1]{\\href{https:\/\/arxiv.org\/abs\/#1}{\\nolinkurl{arXiv:#1}}}\n/) { note("P1 macro added"); } else { note("P1 MISS doi macro"); } } else { note("P1 macro already present"); }
my $n = ($t =~ s/\\href\{https:\/\/arxiv\.org\/abs\/([^}]*)\}\{arXiv:\1\}/\\arxiv{$1}/g); note("P1 arXiv hrefs replaced: " . ($n||0));
if ($t =~ s/(Internat\. J\. Math\. \\textbf\{15\} \(2004\), 501--530)\.\n(\\doi\{10\.1142\/S0129167X04002417\}\.)\nPreprint (\\arxiv\{math\/0306067\}) \(2003\)\./$1; preprint $3 (2003).\n$2/) { note("P2 Ozawa applied"); } else { note("P2 MISS Ozawa pattern"); }
if ($t =~ /\\subjclass\[2020\]\{Primary 20E32; Secondary ([^}]*)\}/) {
  my @c = map { s/^\s+|\s+$//gr } split /,/, $1; @c = map { $_ eq '22D10' ? '22D55' : $_ } @c; push @c, '46L10' unless grep { $_ eq '46L10' } @c;
  my %s; @c = sort grep { !$s{$_}++ } @c; my $new = "\\subjclass[2020]{Primary 20E32; Secondary " . join(', ', @c) . "}";
  $t =~ s/\\subjclass\[2020\]\{Primary 20E32; Secondary [^}]*\}/$new/; note("P3 subjclass -> $new");
} else { note("P3 MISS subjclass"); }
if ($t !~ /\\keywords\{/) { $t =~ s/(\\subjclass\[2020\]\{[^}]*\})/$1\n\\keywords{Property (T), sofic groups, hyperlinear groups, locally embeddable into finite groups, simple groups, minimal subshifts, expanders}/; note("P4 keywords added"); } else { note("P4 keywords already present"); }
if ($t !~ /pdfkeywords/) { if ($t =~ s/(pdfauthor=\{\\paperauthorname\})\}/$1,pdfkeywords={property (T), sofic groups, hyperlinear groups, LEF groups, simple groups, subshifts, expanders}}/) { note("P5 pdfkeywords added"); } else { note("P5 MISS hypersetup"); } } else { note("P5 already"); }
$n = ($t =~ s/\\hfill\$\\square\$/\\qed/g); note("P6 hfill-square replaced: " . ($n||0));
$n = ($t =~ s/\\subsection\*\{Origin and authorship\}/\\section*{Origin and authorship}/); note("P7 origin heading: " . ($n||0));
$n = ($t =~ s/Zap\. Nauchn\. Sem\. POMI/Zap. Nauchn. Sem. S.-Peterburg. Otdel. Mat. Inst. Steklov. (POMI)/); note("P9 POMI: " . ($n||0));
print STDERR join("\n", @log), "\n"; print $t;
```

order.pl (P10):
```perl
undef $/; my $t = <STDIN>;
$t =~ /(\\begin\{thebibliography\}\{99\}\n)(.*?)(\n\\end\{thebibliography\})/s or die "no bibliography\n";
my ($head, $body, $tail) = ($1, $2, $3);
my @e = grep { /\\bibitem\{/ } split /\n\s*\n/, $body;
my $i = 0; my @k;
for my $x (@e) {
  my ($auth) = $x =~ /\\bibitem\{[^}]*\}\s*\n?\s*([^\n]*)/;
  $auth =~ s/\\emph.*//; $auth =~ s/,.*//; $auth =~ s/\s+and\s+.*//;
  my @w = split /[~ ]+/, $auth; my $sur = $w[-1];
  my ($yr) = $x =~ /\((\d{4})\)/; $yr //= 9999;
  push @k, [$sur, $yr, $i++, $x];
}
my @s = sort { $a->[0] cmp $b->[0] or $a->[1] <=> $b->[1] or $a->[2] <=> $b->[2] } @k;
print STDERR "order: ", join(' ', map { ($_->[3] =~ /\\bibitem\{([^}]*)\}/)[0] . "(" . $_->[0] . ")" } @s), "\n";
my $nb = join("\n\n", map { $_->[3] } @s) . "\n";
$t =~ s/\\begin\{thebibliography\}\{99\}\n.*?\n\\end\{thebibliography\}/$head\n$nb$tail/s;
print $t;
```
- **Caveat for order.pl:** the sort key is the surname on the first author line after `\bibitem`, and entries must be separated by blank lines, as they are in rev2 and rev3.
- **After running:** check the printed order line. A bibitem whose author line starts with a prefix ("van", "de") would need a manual key; there is none now.

## 5. Outside this lane (one sentence each)
- `KionkeSchesler` has only the arXiv id. sk-panel-referee-2 found J. Comb. Algebra 2024 on Crossref (no volume or pages yet); sk-lit-locators owns that data.
- The new rev3 bibitems (BezuglyiMedynets, GPS99, Hedlund44, MorseHedlund38, Ore, Wilson) are formatted consistently: journal abbreviation, bold volume, year, pages, DOI. I did not check their data.

## Status
Typography only: no Cairn nodes and nothing queued for review.
