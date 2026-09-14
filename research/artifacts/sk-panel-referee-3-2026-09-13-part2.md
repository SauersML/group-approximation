# sk-panel-referee-3, part 2: ranking the four candidate papers (exposition, structure, impact)

Lane `sk-panel-referee-3`, 2026-09-13 ~19:45 CDT. I read all four drafts line by line:

| draft | file | lines | pages | md5 (self-reported) |
|---|---|---|---|---|
| minimal | `sk/drafts/sk-draft-minimal/minimal.tex` | 288 | 3 | d6b27d4a… |
| rich | `sk/drafts/sk-draft-rich/sk-draft-rich.tex` | 448 | 5 | 6253fcca… |
| general | `sk/drafts/sk-draft-general/sk-draft-general.tex` | 504 | 6 | not reported |
| ring | `sk/drafts/sk-draft-ring/sk-draft-ring.tex` | 352 | 4 | 87372e3a… |

Line numbers below refer to those files. Part 1 (blocking issues on main's revision 1) stands.

## 0. Headline finding: every draft is behind main on impact
- **The characterization is established.** `lef-groups-embed-in-simple-kazhdan-lef-groups` is ESTABLISHED with two independent PASSes: sk-verify-3 (`sk-review-3-2026-09-13-part6.md` §A0) and sk-lef-embedding-c's adversarial review (0db6bc6383). It is also queued with sk-verify-4. The GAP in the density step of the note-text proposal has a reviewed repair (`sk-review-3-2026-09-13-part7.md` §2–4).
- **Statement.** A finitely generated group is LEF if and only if it is a subgroup of an infinite finitely generated simple Kazhdan LEF group.
- **Why it matters here.** It supersedes the RF corollary (rich §2, general Corollary 3) and answers Question 2 of rich (l.335–336) and general (l.381–384). Both drafts would publish as open a question main now answers. That must not ship.
- **Impact.** For a reader outside the field this is the most memorable sentence available: it characterizes a class of groups, where the RF corollary gives only examples. It belongs in the abstract.
- **Construction** (sk-universal-embedding-b):
  - Ore's theorem gives Γ ≤ [Δ,Δ];
  - L = Z/2≀Δ acts on {0,1}^Δ minimally and topologically freely, but NOT freely;
  - G = EL_3(LC({0,1}^Δ,F_2)⋊L);
  - γ ↦ diag(u_γ,1,1) on commutators.
- **Consequence for architecture.** The general draft organizes everything around free minimal subshifts with finite models, and its own Proposition 2(b) shows these force the acting group to be residually finite. So that architecture cannot carry the characterization. The right hypothesis is a minimal topologically free action with exact matricial models.
- **What that needs.** The tower proof survives with one sentence changed, "every nonempty clopen set contains a small one" (sk-lef-embedding-e §1, length neutral; node `tower-simplicity-holds-for-topologically-free-actions`). That node is UNREVIEWED; it is queued with sk-verify-4, `queue/sk-verify-4.txt` line 15.

## 1. Ranking (what a top-journal reader gains per page)

| rank | draft | verdict |
|---|---|---|
| 1 | **rich**, as the architecture | Concrete Theorem 1 over Z, the strongest corollaries, a questions section. This is the shape that should ship, but three pieces must be replaced (§3.1 R1–R4). |
| 2 | **minimal**, as the text of §1 | The cleanest proof section of the four. Its covering-step ending (l.171–177) is the best ending: no level ideal, no odd Stepanov citation. It is also the right fallback if "short" must win outright (3 pages, full). |
| 3 | **general** | Complete proofs over Γ, now reviewed: Theorem G, Proposition N and Proposition E PASS (`sk-review-4-2026-09-13-part1.md`). But its Γ-theorem is built on finite models, which force residual finiteness, so it misses the LEF characterization. Its abstract buries the answer to the question in the fourth sentence. 6 pages. |
| 4 | **ring** | The most elegant engine: Lemma 2 works for every finite field and n ≥ 3 with no GL_d(F_2). But it is the least memorable paper: the abstract opens with a technical definition, and there is no characterization. By its own account, +60 lines buy only F_q. Keep Lemma 2 in reserve in case an F_q statement is ever wanted. |

## 2. The paper I would accept (merge recipe; about 5 pages, about 380–400 source lines)
1. **Title.** Plural, e.g. general's "Infinite simple Kazhdan groups that are sofic". sk-title-abstract owns the final wording.
2. **Abstract** (verbatim candidate; the lineage wording is rev1's):
```latex
\begin{abstract}
For every infinite minimal subshift $X$, the group
$\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)} that is locally embeddable into
finite groups, so it is sofic and hyperlinear. This answers the question
of Brown and Ozawa whether an infinite simple Kazhdan group can be
hyperlinear, and Pestov's sofic version of it. A finitely generated group
is locally embeddable into finite groups if and only if it is a subgroup
of an infinite finitely generated simple Kazhdan group with this
property. The word problems of the groups above realize every Turing
degree.
\end{abstract}
```
3. **Intro.**
   - The rev1 lineage paragraph, with part 1 F1 (Ozawa's LLP remark).
   - Theorem 1 over Z, plus the EL_n sentence.
   - The LEF characterization stated as Corollary 2 in the intro.
   - A credit paragraph without "The new step is simplicity" (part 1 B2/F2). It should credit:
     - Matui for the tower pattern;
     - Kionke–Schesler for the residually finite case without (T);
     - Stepanov: "Over $\Z$, simplicity also follows from Stepanov's normal-structure theorem~\cite[Theorem~4.4]{Stepanov}". The route passed conditionally in `sk-review-1-2026-09-13-part9.md` §3; the bibitem comes back in.
4. **§1 Proof of Theorem 1.**
   - Minimal draft l.70–177.
   - Apply sk-lef-embedding-e's §1 patch once sk-verify-4 passes the node. The patch is length neutral and makes the proof literally valid for topologically free actions, which is what makes §2 short.
   - Then the operator-algebra paragraph (Brown bridge, Kirchberg Theorem 1.1, LLP), placed AFTER simplicity is proved.
5. **§2 Every LEF group.** The corollary and its proof.
   - Preferred: sk-lef-embedding-e §2, which says "the proof of Theorem 1 applies word for word", if and only if §1 already carries the topologically free patch. Otherwise that sentence is a substitution list, the same weakness as rich l.266–278.
   - Fallback: sk-universal-embedding-b's self-contained text (about +55 lines, density sentence as repaired in review part 7).
6. **§3 Word problems.** rev1, with §4 C1–C2 below.
7. **Questions.**
   - Q1: finite presentation, citing Alekseev–Thom Open problem 6.1.
   - Q3: rigidity, with the easy direction stated.
   - DELETE Q2 (answered).
8. **Bibliography.**
   - Add Ore, Kionke–Schesler, Kirchberg, AlekseevThom, GPS, and Stepanov if item 3's sentence goes in.
   - Drop CortezPetite and KerrNowak: the Toeplitz machinery is not needed once the lamplighter host is used.

## 3. Line-level fixes per draft (verbatim)

### 3.1 sk-draft-rich (the architecture to use)
**R1. ERROR, notation (l.144–147).** `R` is the ring (l.89) and is also used for the hyperfinite factor, which is never defined.
Before:
```latex
So $L(G)$ embeds in $R^\omega$~\cite[Proposition~7.1]{Ozawa}. Since $G$
is infinite and simple, its nontrivial conjugacy classes are infinite,
so $L(G)\mathbin{\bar\otimes}R$ is a McDuff factor. It embeds in
$R^\omega$, and its unitary group contains $G$, as Brown asked. Kirchberg
```
After:
```latex
So $L(G)$ embeds in $\mathcal R^\omega$~\cite[Proposition~7.1]{Ozawa},
where $\mathcal R$ is the hyperfinite $\mathrm{II}_1$ factor. Since $G$
is infinite and simple, its nontrivial conjugacy classes are infinite,
so $L(G)\mathbin{\bar\otimes}\mathcal R$ is a McDuff factor. It embeds in
$\mathcal R^\omega$, and its unitary group contains $G$, as Brown asked. Kirchberg
```

**R2. Order (l.144–151).** The paragraph uses "infinite and simple" before §Simplicity (l.153–203) proves it. Move the paragraph to directly after l.203.

**R3. Obsolete question (l.335–336).** Delete "Does every finitely generated LEF group embed in an infinite simple Kazhdan LEF group?". It is answered on main, reviewed. Replace §2 (RF) by the LEF characterization (§2 item 5 above).

**R4. Sketch (l.266–278).** "The proof of Theorem~\ref{thm:main} now applies … Exponents become group elements …" asks the reader to redo a whole theorem. Use a §1 written for topologically free actions (§2 item 4), or the self-contained fallback.

**R5. Abstract (l.33–36).** "one of these groups" has no clear referent after the RF clause. Use §2 item 2.

**R6. Credit (l.62–63).** Delete "The new step is simplicity." (part 1 B2).

### 3.2 sk-draft-minimal (the text of §1)
**M1. Credit and vagueness (l.54–57).**
Before:
```latex
Jaikin-Zapirain~\cite{EJZ}. The finite models use periodic sequences
with the same short words as $X$, as in Grigorchuk and
Medynets~\cite{GM}. The new step is simplicity. A nontrivial normal
```
After:
```latex
Jaikin-Zapirain~\cite{EJZ}. The finite models use periodic sequences
with the same words of a given length as $X$, as in Grigorchuk and
Medynets~\cite{GM}. In the proof of simplicity, a nontrivial normal
```

**M2. Referent (l.106).** "This word begins and ends with" → "The word $x_{[0,m_\ell+2\ell)}$ begins and ends with".

**M3. Quantifier (l.118).** "for all $r,s\in R$ the identities" → "for fixed $r,s\in R$ the identities". The threshold on ℓ depends on r and s.

**M4. Order (l.28 vs l.49).** The abstract says "infinite, simple, finitely generated" and the theorem "infinite, finitely generated, simple". Use the theorem's order in both.

**M5. Keep (l.171–177).** Adopt the covering ending in every merged text. Every term of 1−∏_a(1−e_{T^aV}) is a product of the e_{T^aV} = u^a e_V u^{−a}, so it has the form r e_V s. I checked this.

### 3.3 sk-draft-general (only if its Γ material is reused)
**G1. Abstract (l.30–43).** The answer to Brown, Ozawa and Pestov is sentence 4. Lead with G_X (§2 item 2).

**G2. Precision (l.36).** "Such subshifts exist exactly over residually finite groups" → "exactly over infinite residually finite groups". A finite group carries no infinite subshift.

**G3. Order (l.174–185).** Same as R2: move after l.237.

**G4. Citation with no content (l.95–96).** "Kerr and Nowak studied residually finite actions and their crossed products~\cite{KerrNowak}." tells the reader nothing specific, and the draft's own self-assessment says the definitions were not compared. Delete it, or state the relation.

**G5. Level ideal (l.231–237).** Replace with minimal's covering ending, written over Γ:
```latex
For distinct $p,q,l$ and $r,s\in R$, \eqref{eq:elementary} gives
$e_{pl}(re_V)=[e_{pq}(r),e_{ql}(e_V)]\in N$ and
$e_{pq}(re_Vs)=[e_{pl}(re_V),e_{lq}(s)]\in N$. By minimality and
compactness finitely many translates $aV$ cover $X$. Since
$e_{aV}=u_ae_Vu_a^{-1}$, the identity $1=1-\prod_a(1-e_{aV})$ writes $1$,
and so every element of $R$, as a sum of products $re_Vs$. So $N$
contains every $e_{pq}(r)$, and $N=G$.\hfill$\square$
```

**G6. Uncited standard fact (l.283–284).** "$x$ is almost periodic, and $X$ is minimal" needs a citation or its one-line reason. sk-citations owns the source.

**G7. Obsolete question (l.381–384).** Delete Question 2.

### 3.4 sk-draft-ring (reserve only)
**N1. Abstract (l.27–38).** A definition comes before any group is named, and the answer appears in sentence 5. Lead with G_X.

**N2. Missing reason (l.121–123).**
Before: "So there are $s$ and $t\ne0$ with $tFs=0$, and $i\ne j$, such that $\rho=[g,e_{ij}(s)]\ne1$."
After: "Since the $s$ with $tFs=0$ for some $t\ne0$ span $R$, one of them lies outside this subgroup, so some $i\ne j$ has $\rho=[g,e_{ij}(s)]\ne1$."

**N3. Anthropomorphism (l.79–80).** "local annihilation supplies the noncentral commutators it starts from" → "and under local annihilation some commutator $\rho\ne1$ with $g\in N$ satisfies $t\rho=tI_n$ for some $t\ne0$."

## 4. Common to all four
- **C1.** "each $f_j$ a table on words" (word-problem proof) → "each $f_j$ given by a table on the words of some length".
- **C2.** The Grigorchuk–Medynets credit sentence sits inside the word-problem proof. Move it directly after `\end{corollary}`: credit inside a proof reads as a proof step.
- **C3.** The Pestov locators "Example 4.5 and Theorem 3.3" come from arXiv v8, and the journal numbering is unchecked. The primary alternative is Elek–Szabó, Math. Ann. 332 (2005).
- **C4.** The Brown bridge uses McDuff's theorem and the fact that M ⊂ 𝓡^ω implies M⊗̄𝓡 ⊂ 𝓡^ω, both without citation (minimal, rich, general, ring). One citation, owned by sk-citations.

## 5. What I verified in this part
- **Mathematics re-derived. No ERROR in any draft.**
  - ring Lemma 2:
    - the entries of ρ−I have the form fsr;
    - e_{ml}(ct)ρ = ρ+ctE_{ml};
    - v = I+Y·ctE_{ml};
    - [e_{bq}(1),v] = e_{bl}(z(v^{−1})_{ll});
  - ring Lemma 3's finite-central quotient: fZ ↦ ψ(f)ψ(Z) is well defined, injective, and preserves products;
  - general Proposition 2(c):
    - finite models with index ≥ 3, using only the values x(K_n);
    - the index-3 defect that sk-draft-rich found in sk-general-actions-a does not affect the general draft's text;
  - the Whitehead identities in characteristic 2 in rich and general;
  - minimal's covering ending.
- **Crossref:**
  - Kerr–Nowak, ETDS 32, 1585–1614 (online 2011, volume 32 is 2012);
  - Cortez–Petite, J. Lond. Math. Soc. 78 (2008), 1–20;
  - Ore, Proc. AMS 2 (1951), 307–314;
  - Kionke–Schesler, J. Comb. Algebra (2024), doi 10.4171/JCA/103, no volume listed.
- **Review status used:**
  - RF embedding: PASS ×2 (review-3 part 3, review-4 part 1);
  - Theorem G, Proposition N, Proposition E: PASS, first review (review-4 part 1);
  - LEF characterization: PASS ×2 (review-3 part 6; sk-lef-embedding-c 0db6bc6383);
  - tower simplicity for topologically free actions: UNREVIEWED;
  - Stepanov Theorem 4.4 route: PASS, conditional (review-1 part 9).
