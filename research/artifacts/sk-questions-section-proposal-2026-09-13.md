# sk-questions-section: the Questions section for revision 4 (proposal, RULES §6)

Lane sk-questions-section (ROSTER-H, wave 10), 2026-09-13 ~22:00 CDT.

Base texts:
- landed rev3: main 9047d0d3c9, md5 274f19367f7f706b05c017af721c3884, `\section{Questions}` at l.406–420;
- rev4 draft: `sk/drafts/rev4.tex` (21:41, md5 eee41cb50790146c7b93d77beb794470), `\section{Questions}` at l.482–501.

## 0. Verdict
- **Keep three questions.** The rev4 draft's three are the right ones: finite presentation, sofic hosts, rigidity. Each is open after a bounded check (§4) and has a precise printed anchor or is the note's own.
- **Add one.** "Is every sofic infinite simple Kazhdan group LEF?" goes at the end of the first paragraph, at 0 net lines against the rev4 draft.
  - It names the one property a sofic answer to the first question must break: a finitely presented LEF group is residually finite.
  - It isolates the obstacle the host question also meets.
  - Every sofic infinite simple Kazhdan group on main is sofic because it is LEF.
- **Do not pose:**
  - MF of C*_r(G_X): decision 18.
  - C*-simplicity: sk-cstar-simple and sk-cstar-simple-2 may settle it; see O2.
  - Z² SFT soficity: decision 18.
  - LEF growth, number of generators, decidable hosts: narrower, or owned by live lanes (§5).
- **Optional O1 (+1 line):** "Does L(G_X) ≅ L(G_Y) imply G_X ≅ G_Y?", only if sk-strong-7's P1 (countable fibres of X ↦ L(G_X)) passes sk-verify-10 and goes in.

## 1. The text (a)

### 1.1 Current text, landed rev3 l.406–420 (verbatim)
```latex
\section{Questions}

A finitely presented LEF group is residually finite~\cite{VershikGordon},
and the infinite simple group $G_X$ is not, so $G_X$ is not finitely
presented. Finitely presented infinite simple groups with
property~\textup{(T)} exist~\cite{CapraceRemy}. Is there one that is
sofic, or at least hyperlinear? A positive answer would also answer Open
problem~6.1 of Alekseev and Thom~\cite{AlekseevThom}, which asks for
finitely presented sofic groups with property~\textup{(T)} that are not
residually finite.

If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. For topological full groups the converse
holds~\cite{GPS99,BezuglyiMedynets}. Does $G_X\cong G_Y$ imply that $X$ and
$Y$ are flip conjugate, or at least strongly orbit equivalent~\cite{GPS}?
```

### 1.2 Current rev4 draft, l.488–492 (the only lines this proposal changes, verbatim)
```latex
simple groups with property~\textup{(T)} exist~\cite{CapraceRemy}. Is
there one that is sofic, or at least hyperlinear? A sofic example would
also answer Open problem~6.1 of Alekseev and Thom~\cite{AlekseevThom},
which asks for finitely presented sofic groups with property~\textup{(T)}
that are not residually finite.
```

### 1.3 Proposed Questions section (replaces rev3 l.406–420, and rev4 draft l.482–501; 20 lines)
```latex
\section{Questions}

A finitely presented LEF group is residually
finite~\cite{Stepin,VershikGordon}, and the infinite simple group $G_X$ is
not, so $G_X$ is not finitely presented. Finitely presented infinite
simple groups with property~\textup{(T)} exist~\cite{CapraceRemy}. Is
there one that is sofic, or at least hyperlinear? A sofic example would
not be LEF, and it would also answer Open problem~6.1 of Alekseev and
Thom~\cite{AlekseevThom}, which asks for finitely presented sofic groups
with property~\textup{(T)} that are not residually finite. Is every sofic
infinite simple Kazhdan group LEF?

Is every finitely generated sofic group a subgroup of an infinite finitely
generated simple Kazhdan sofic group, as in Corollary~\ref{cor:lef}?

If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. For topological full groups the converse
holds~\cite{GPS99,BezuglyiMedynets}. Does $G_X\cong G_Y$ imply that $X$
and $Y$ are flip conjugate, or at least strongly orbit
equivalent~\cite{GPS}?
```
- Against the rev4 draft, only l.489–492 change: the "not be LEF" clause and the new question, reflowed into the same nine-line paragraph.
- It keeps both referee musts: a-U9 ("A sofic example would also answer") and the Stepin credit (decision 76, sk-verify-6 part 3 PASS).
- Cite keys used: Stepin, VershikGordon, CapraceRemy, AlekseevThom, GPS99, BezuglyiMedynets, GPS. All are in the rev4 draft bibliography (checked at landing, §6).

### 1.4 Optional O1 (only with sk-strong-7 P1 in the note; +1 line, appended to the last paragraph)
```latex
equivalent~\cite{GPS}? Does $L(G_X)\cong L(G_Y)$ imply $G_X\cong G_Y$?
```
- With P1, each isomorphism class of L(G_X) contains only countably many X.
- Main records the general Connes rigidity conjecture for ICC Kazhdan groups as refuted (`icc-property-t-not-w-star-superrigid`, 2026-08-19 ingestion). So the family question is the meaningful one. The note should not name the conjecture, since the refutation has no citable public source recorded on main.

### 1.5 Optional O2 (not recommended; only if both C*-simplicity lanes leave it open when rev4 lands)
```latex
Is $G_X$ C$^*$-simple?
```
- `C*_r(G_X)` already has a unique trace (`subshift-elementary-group-reduced-cstar-has-unique-trace`, via Breuillard–Kalantar–Kennedy–Ozawa, which the note does not cite).
- sk-cstar-simple has shown that every natural amenable test subgroup is not confined (unreviewed), so this may soon be a theorem and not a question.

## 2. Proof content of the factual sentences (b)
- **"A finitely presented LEF group is residually finite."** Node `finitely-presented-lef-groups-are-residually-finite`.
  - Take a ball containing the relators and a word for `g ≠ 1`. A local embedding of it into a finite group defines a homomorphism of the free group that kills the relators, so it factors through the group, and `g` survives.
  - Credit: Stepin 1984 and Vershik–Gordon 1997 p. 71–72 (sk-verify-6 part 3 PASS).
- **"The infinite simple group G_X is not [residually finite]."** A normal subgroup of finite index is `1` or `G_X`. Since `G_X` is infinite it is `G_X`, which contains every `g ≠ 1`.
- **"A sofic example would not be LEF."** The two previous items: finite presentation plus LEF would force residual finiteness.
- **Alekseev–Thom Open problem 6.1, verbatim** (arXiv:2608.05362 v1, Open problems section; sk-questions-ggt part 2; sk-lit-locators row 25 from the e-print source): "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?" A finitely presented infinite simple sofic Kazhdan group is such an example.
- **Caprace–Rémy.** Their arXiv source: "there exist infinitely many isomorphism classes of finitely presented infinite simple groups with Kazhdan's property (T)" (sk-rev3-referee-b, verified).
- **Flip conjugacy gives isomorphism.** Let `h: X → Y` be a homeomorphism with `h∘T = S^{±1}∘h`. Then `f u^j ↦ (f∘h^{-1}) u^{±j}` is a ring isomorphism `LC(X,F_2)⋊_T Z → LC(Y,F_2)⋊_S Z`, and `EL_3` of isomorphic rings are isomorphic. Check: `u^{±1}(f∘h^{-1})u^{∓1} = (f∘T^{-1})∘h^{-1}` when `h∘T = S^{±1}∘h`.
- **The converse for topological full groups.** Giordano–Putnam–Skau 1999 and Bezuglyi–Medynets 2008 (sk-panel-referee-4 B3; locators in rev3).
- **"Is every sofic infinite simple Kazhdan group LEF?"** Kazhdan groups are finitely generated, so "LEF" needs no extra hypothesis.
  - Model test: finite simple groups are excluded by "infinite".
  - `G_X` and the lamplighter hosts are LEF, so they are consistent with a yes.
  - The non-LEF simple Kazhdan groups `S_N` of `simple-kazhdan-linear-sofic-non-lef-group-exists` are only known to be linear sofic, so they are candidates for a no, not counterexamples.

## 3. Length (c) and trade-off (d)
- **(c)**
  - Against the rev4 draft: 0 lines (20 → 20).
  - Against landed rev3: +5 source lines (15 → 20). The rev4 draft's host question adds 3; the Stepin cite and the new question are absorbed by reflow.
  - O1 costs +1 line; O2 costs +1 line plus a bibitem if the unique-trace clause is kept.
- **(d)** At no length over the rev4 draft, the reader learns what a sofic answer to the first question must break (LEF). The same property separates every sofic simple Kazhdan group the note constructs from the ones the first two questions ask for. No new fact to trust beyond the Vershik–Gordon statement already cited.

## 4. Status table (e): open after a bounded check

| Question | Printed anchor | Cairn (on main) | Bounded check |
|---|---|---|---|
| f.p. infinite simple Kazhdan group, sofic or hyperlinear | Alekseev–Thom arXiv:2608.05362 Open problem 6.1 (verbatim, §2). Pestov–Kwiatkowska arXiv:0911.4266 p. 28 (sk-questions-ggt A1), "it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic": the note answers the f.g. form, and the f.p. form remains | `hyperlinear-fp-infinite-simple-kazhdan-group` OPEN; `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` OPEN; `km-246-lattice-is-sofic` OPEN | sk-fp-sofic-a: 3 web searches. sk-open-5: 3 searches plus arXiv:2604.19174. sk-fp-sofic-d: candidate scan (López Neumann 2101.09071, Amir–Lazarovich 2605.09493, Chatterji–Kassabov 2601.22907). This lane: 1 search on 2026-09-13 ("finitely presented infinite simple group sofic OR hyperlinear property (T) 2026 arXiv"). No f.p. infinite simple sofic or hyperlinear group found |
| Is every sofic infinite simple Kazhdan group LEF? (new) | none located; the note's own | new `sofic-non-lef-infinite-simple-kazhdan-group-exists` OPEN (the negative answer), with routes from finite presentation and from universal hosts | sk-questions-ggt sweep of 25 sources, including grep of the Kourovka Notebook for "sofic" and "LEF". Alekseev–Thom 2608.05362 §5 lists only Thom's group among sofic non-RF Kazhdan groups, and it is LEF (sk-novelty-prior-art part 1). This lane: 1 search ("sofic group with property (T) that is not LEF"). No sofic non-LEF Kazhdan group located, simple or not |
| f.g. sofic ⊆ infinite f.g. simple Kazhdan sofic | none located; the note's own. The LEF form is Corollary cor:lef; the RF form without (T) is Kionke–Schesler Thm 1.2 | `sofic-groups-embed-in-simple-kazhdan-sofic-groups` OPEN. Linear-sofic hosts: `sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups` (unreviewed) | This lane: 2 searches. No theorem embedding f.g. sofic groups into f.g. simple sofic groups was located, even without (T). Fournier-Facio–Sun arXiv:2503.01987 (abstract read) controls dimension, not approximation |
| G_X ≅ G_Y ⇒ flip conjugate, or SOE | Analogue: Cornulier, Séminaire Bourbaki 1064, (2f), "Classifier les morphismes entre les différents groupes [[ϕ]] ou [[ϕ]]′" (sk-questions-ggt part 2). Converse for topological full groups: GPS99, Bezuglyi–Medynets | `subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence` OPEN; `subshift-el3-isomorphisms-are-standard-over-f2` OPEN. Ring level: `cantor-crossed-product-matrix-ring-iso-forces-soe` PASS (sk-verify-3); `subshift-ring-isomorphism-preserves-soe-class-and-growth` PASS (sk-verify-5) | sk-rigidity-ring: every located isomorphism theorem for GL/EL over rings assumes 1/2, or n ≥ 4 with GL_n, and Petechuk shows n = 3 is exceptional in characteristic 2 |

**For main:**
- Reviewed ring-level results make "or at least strongly orbit equivalent" a question only about standardness of group isomorphisms. The note cannot say so without the ~40-line ring proof, so the wording stays.
- If sk-iso-rigidity (wave 10) proves standardness over F_2, delete "or at least strongly orbit equivalent" and state the result.

## 5. Tested and not posed
- **MF of C*_r(G_X).** Decision 18 (famous-level). It is now tied to matricial stability of SL_4(F_q[t^{±1}]) (sk-matricial-stability, unreviewed), which does not change the decision.
- **C*-simplicity.** O2 above. Not recommended while two lanes work on it.
- **Characters.** Settled by `subshift-elementary-groups-are-character-rigid` (sk-characters-rigidity-b; independent review PASS by sk-characters-rigidity-a, 591d1248dc). If the result goes into the note it is a sentence, not a question.
- **Z² subshifts of finite type** (sk-open-5 Q2). Decision 18.
- **LEF growth of G_X** (Bradford arXiv:2104.07111 Questions 7.2 and 7.5 analogues). Narrower; `elementary-group-lef-growth-separates-subshifts` OPEN.
- **Minimal number of generators** (Cornulier Bourbaki (8) analogue). Owned by sk-two-generators; if proved, it is a clause in Theorem 1.
- **Hosts with solvable word problem** (a Boone–Higman form). Owned by sk-decidable-host; if proved, it is a theorem.
- **A finitely presented host for recursively presented LEF groups.** Falls: a finitely presented LEF group is residually finite.

## 6. Cairn wiring landed with this proposal
- **New open claim** `sofic-non-lef-infinite-simple-kazhdan-group-exists`, with Attempts: the linear-target barrier, rank to Hamming, finite presentation, bounded literature check.
- **Routes into it:**
  - `sofic-non-lef-simple-kazhdan-from-fp-sofic-ring-route`, requiring `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` and `finitely-presented-lef-groups-are-residually-finite`;
  - `sofic-non-lef-simple-kazhdan-from-universal-sofic-host`, requiring `sofic-groups-embed-in-simple-kazhdan-sofic-groups` and `sofic-universal-envelope-forces-non-lef-simple-kazhdan`.
- **Merged onto main's blobs:**
  - the note's questions root `simple-kazhdan-lef-groups-note-open-questions` (blob 5160167f3c) now lists all four questions;
  - its conjunction route `simple-kazhdan-lef-note-open-questions-conjunction` (blob a1f225e27a) now requires the host claim and the new claim as well.
