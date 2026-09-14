# sk-lit-background, part 2: what the background sources say, verbatim, and a draft background paragraph (2026-09-13)

Lane sk-lit-background. Subject: main's `simple_kazhdan_sofic_group.tex` at e80dcf20ad (revision 2, md5 4ad49212…). Line numbers "r2 l.N" refer to it.

**Sources read.** arXiv e-print sources fetched and grepped on MSI, about 20:30 CDT:
- Thom, arXiv:0810.2180 (`main.tex`);
- Pestov, arXiv:0804.3968v8 (`hypsof.tex`);
- Caprace–Rémy, arXiv:math/0607664 (`SimplSuperrigid.tex`);
- Kionke–Schesler, arXiv:2304.09307 (`tree-permutations.tex`);
- Rădulescu, arXiv:math/0004172 (`convexsets.tex`);
- Lubotzky, arXiv:1105.2389, for the Margulis entry (proposal §B).

The arXiv abstract-page metadata (title, authors, date) confirm 2608.05362 (Alekseev–Thom, "Centralizers of sofic approximations of Kazhdan groups", 5 Aug 2026), 2304.09307, math/0004172 and 0810.2180. The quotes below are copied from the TeX sources. Macros are left as printed, except `\ ` spacing.

## 1. Verbatim record

**V1. Simple Kazhdan groups: the two sources** (Thom, main.tex l.96).
> "There are two sources of simple groups with Kazhdan's property (T). Such groups appear for example as lattices in certain Kac-Moody groups, see \cite{caprem}. Much earlier, it was also shown by Gromov (\cite{MR919829}) that every hyperbolic group surjects onto a Tarski monster, i.e. every proper subgroup of this quotient is finite cyclic; in particular: this quotient group is simple and is a Kazhdan group if the hyperbolic group was a Kazhdan group."

- MR919829 is Gromov, *Hyperbolic groups* (1987).
- Caveat: "every hyperbolic group" needs "non-elementary". The theorem is often credited to Ol'shanskii (IJAC 3, 1993), whose paper I did NOT read. So the note should say only "quotients of hyperbolic Kazhdan groups [Gromov87]", and add Ol'shanskii only after a check.

**V2. The first finitely presented simple Kazhdan groups** (Caprace–Rémy, SimplSuperrigid.tex l.153–154, l.158–161, l.1827–1828).
> "As pointed out to us by Y.~Shalom, we obtain the first infinite {\it finitely presented} discrete groups to be both simple and Kazhdan."

> "If the generalized Cartan matrix $A$ is $2$--spherical (i.e. every $2 \times 2$--submatrix is of spherical type) and if $q > 1764^n$, then the group $\Lambda/Z(\Lambda)$ is finitely presented, simple and Kazhdan. Moreover there exist infinitely many isomorphism classes of infinite groups with these three properties."

> "The above simple groups seem to be the first examples of infinite finitely generated simple groups enjoying property (T)."

- The last sentence conflicts with V1's Gromov attribution. The safe credit is the one in the first quote: the first finitely PRESENTED examples.

**V3. Sofic groups** (Pestov, hypsof.tex l.378; Thom, main.tex l.341).
> "This question originated in 1999 Gromov's article \cite{gromov99} where the concept of a sofic group was first introduced (without a name of its own) in order to attack Gottschalk's Surjunctivity Conjecture ... The current expression ``sofic group'' was coined by Benjy Weiss \cite{weiss}."

> "Sofic groups (with an equivalent definition in terms of Cayley graphs) were first studied by Gromov in \cite{gromov} and later by B. Weiss in \cite{MR1803462} who also coined the name. Later, G. Elek and E. Szab{\'o} continued a more systematic study in \cite{MR2178069, MR2220572} and proved that sofic groups are hyperlinear."

**V4. Hyperlinear groups and Connes' problem** (Pestov, hypsof.tex l.385; Rădulescu, convexsets.tex l.290).
> "The statement that every group (equivalently: every countable group) is hyperlinear is known as {\em Connes' Embedding Conjecture for Groups,} and we will discuss it below. The origin of this conjecture is Connes' 1979 paper \cite{connes-injective}. The expression ``hyperlinear group'' belongs to Radulescu \cite{radulescu00}."

> "\label{definition2.5}We call an i.c.c.\ group $\Gamma$ hyperlinear if $\Gamma$ ..."

- Pestov's bibitem `connes-injective` (l.1044–1046) is *Classification of injective factors*, Ann. of Math. 104 (1976), 73–115. The year "1979" in his text is a slip, so the note should use 1976.
- In arXiv v3 of Rădulescu, 2.5 is a **Definition**. Pestov cites "Prop. 2.5".

**V5. Credit for "hyperlinear ⟺ L(G) embeds in R^ω"** (Pestov, hypsof.tex l.799–802).
> "\begin{theorem}[Kirchberg \cite{kirchberg94}; Radulescu \cite{radulescu00}, Prop. 2.5; Ozawa \cite{ozawa}, Prop. 7.1] Let $G$ be a countable group. Then $VN(G)$ embeds into $R^\omega$ if and only if $G$ is hyperlinear."

- `kirchberg94` (l.1173) is the Math. Ann. 299 (1994) paper already in the note.
- r2 l.168 credits only [Ozawa, Proposition 7.1] (proposal item P7).

**V6. LEF** (Pestov, hypsof.tex l.481).
> "So is every {\em LEF group} $G$ in the sense of Vershik and Gordon \cite{VG}, defined by the property that one can embed every finite $F\subseteq G$ into a suitable finite group so as to preserve the partial multiplication."

- Pestov's bibitem VG (l.1240): "St. Petersburg Math. J. **9** (1998), 49--67". It agrees with the note's printed data.

**V7. The space of marked groups** (Thom, main.tex l.200).
> "Following ideas of M. Gromov, R. Grigorchuk (see \cite{MR764305}) has introduced the space of marked groups with $n$ generators."

- MR764305 is Grigorchuk, *Degrees of growth …* (Izv. 1984); the Crossref data are in part 1, B3.

**V8. Earlier non-simple examples behind the LLP sentence** (Thom, main.tex l.56).
> "In \cite{MR2072092}, N. Ozawa observed that there are no hyperlinear groups known which do not have E. Kirchberg's factorization property (see below for definitions). In this note, we give examples of groups with this behaviour. As a consequence, the maximal group $C^*$-algebra of such a group cannot have the local lifting property."

- r2 l.173–177 derives the same consequence for G_X, citing Kirchberg and Ozawa. Thom's examples came first but are not simple. r2 l.77–79 credits Thom for LEF Kazhdan non-RF, and that sentence should also carry this credit (proposal P8).

**V9. Embedding residually finite groups into simple LEF groups** (Kionke–Schesler, tree-permutations.tex l.173, l.183–196).
> "It is an easy consequence of the Baer-Schreier-Ulam theorem~\cite{Baer34} that every group $G$ embeds into a simple group $Q$."

> "Here we prove a significantly more general result by showing that every finitely generated, residually finite amenable group $G$ embeds in a finitely generated, simple amenable group $Q$. ... it will be an immediate consequence of our construction that $Q$ is still locally embeddable into finite groups ($\LEF$, for short) in the sense of Vershik-Gordon~\cite{VershikGordon}."

> "Let $H$ be a finitely generated, residually finite (amenable) group. There is a finitely generated, residually finite (amenable) group $G$ and an infinite, simple, (amenable) $\LEF$ group $Q$ such that (1) there is an embedding $\iota \colon H \rightarrow G$, (2) there is a projection $\pi \colon G \rightarrow Q$, (3) the composition $\pi \circ \iota$ is injective."

- This is the credit rev3's §2 needs. Without (T), every f.g. RF group already lies in an infinite f.g. simple LEF group.
- The theorem numbers differ by version: arXiv 1.2 = 9.14 per sk-questions-ggt; the journal numbering is sk-lit-locators' check.

**V10. Secondary confirmation of bibliographic data** (Pestov's bibliography, hypsof.tex).
- Connes, Ann. of Math. 104 (1976), 73–115.
- Weiss, *Sofic groups and dynamical systems*, Sankhyā Ser. A 62 (2000), no. 3, 350–359.
- Gromov, JEMS 1 (1999), no. 2, 109–197.
- Kirchberg, Math. Ann. 299 (1994), 551–563.
- Ozawa, IJM 15 (2004), 501–530.
- Vershik–Gordon, St. Petersburg Math. J. 9 (1998), 49–67.

These agree with part 1. Weiss and Vershik–Gordon have no Crossref records; this is their second independent confirmation.

## 2. Draft background paragraph for the introduction

It would go right after r2 l.46 ("The groups below answer all three forms positively."). The draft uses only V1–V9 and Crossref-verified items. It costs about 10 source lines.

```latex
Property~\textup{(T)} goes back to Kazhdan~\cite{Kazhdan}. Infinite simple
Kazhdan groups arise as quotients of hyperbolic Kazhdan
groups~\cite{Gromov87} and as Kac--Moody lattices, which gave the first
finitely presented examples~\cite{CapraceRemy}. Sofic groups were introduced
by Gromov~\cite{Gromov99} and named by Weiss~\cite{Weiss}. A countable group
is hyperlinear, a term due to R\u{a}dulescu~\cite{Radulescu}, if and only if
its von Neumann algebra embeds in $\mathcal R^\omega$~\cite{Kirchberg,Radulescu,Ozawa},
in the sense of Connes' embedding problem~\cite{Connes}, and sofic groups are
hyperlinear~\cite{ElekSzabo}. Thom constructed a finitely generated Kazhdan LEF
group that is not residually finite~\cite{Thom}, but no infinite simple Kazhdan
group was known to be sofic or hyperlinear~\cite{Ozawa,Pestov}.
```

- **Doctrine check (RULES §6):**
  - no metacommentary, no "hence" or "therefore", no cleft constructions;
  - the one semicolon-free long sentence has clause boundaries a reader can follow;
  - no Lean or agent mention.
- **Overlap:** the last sentence makes r2 l.77–79 ("Thom constructed …") redundant, so the proposal moves that sentence here instead of duplicating it.
- **What the reader gets:** the history in one screen, and the credit a top-journal referee expects (sk-panel-referee-3, B5). There is no mathematical content to trust, and the cost is about 10 source lines plus 6 bibitems.

## 3. Claims I recommend NOT printing
- "Every hyperbolic group surjects onto a Tarski monster" as stated (V1): it needs "non-elementary", and the primary source was not read.
- "Caprace–Rémy gave the first finitely generated simple Kazhdan groups" (V2, l.1827): it contradicts V1. Print "first finitely presented".
- Any date "Connes 1979" (V4): the paper is 1976.
- "No non-hyperlinear group is known": true but outside the note's needs, and it invites a famous-problem discussion. Nonsofic groups are known to exist (OpenAI, 2026), and that also belongs outside this note.
