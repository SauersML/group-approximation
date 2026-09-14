# sk-rev4-referee-c: length and elegance referee of revision 4 (2026-09-13)

Lane sk-rev4-referee-c (ROSTER-I). The target is `simple_kazhdan_sofic_group.tex` as landed on main at c8b6021ca9, md5 9144d8536cdca9073d50ffb64b826c00, 771 lines, 8 pp (checked at tip 2260a3a655).
- Line numbers refer to that file.
- The page breaks come from the MSI compile of the same md5 (`/scratch.global/sauer354/sk/main-rev4/rev4.pdf`, ghostscript txtwrite).
- Scope: cuts, what a reader remembers, section order, title and abstract, and three rev4.1 candidates. No new mathematics.
- I did not read referees (a) or (b).

## 0. Verdict
Rev4 is a coherent short paper: one engine (Theorem 2), one example (Theorem 1), one characterization (Corollaries 3–4), and sharp boundaries. Nothing needs to be cut for correctness.
- Five cuts, K2–K6, save 11 source lines and keep every proof step.
- One move, K1, puts the whole idea on page 1 at no cost.
- One optional move, K8, improves the order.
- Candidates:
  - IN after PASS: the solvable-word-problem clause (strongest of the three), and the non-embeddable continuum.
  - OUT: the Thue–Morse growth remark.

## 1. Ranked cut list (every proof step kept)

### K1 (HIGH, 0 lines): put the whole idea on page 1
Page 1 now ends inside l.87 ("as in the proof by Grigorchuk and"). The simplicity mechanism, l.97–100 ("a nontrivial normal subgroup contains a nontrivial commutator lying in a copy of the finite simple group GL_d(F_2) over a clopen tower"), is on page 2. The background paragraph l.71–81 sits between Theorem 1 and the idea.
- **Change:** move l.71–81 unchanged ("Hyperlinear groups were named by R\u{a}dulescu … hyperlinear~\cite{PestovKwiatkowska}.") to just after l.103 ("Theorem~4.9]{Matui}."), before "The proof works for other actions."
- **Effect:** page 1 gains about 11 source lines of the idea paragraph, which should reach l.100. Confirm at compile.
- **Reader merit:** the question, the theorem and the three-step mechanism ((T) from finite generation, matrix models from periodic approximations, a commutator in a finite simple tower group) all fit on one page.

### K2 (HIGH, −3 lines): drop the marking-without-constants sentence
Theorem 1 claims expanders "with respect to the images of a fixed generating set", and Theorem 2 marks by e_ij(s) with s ∈ S ∋ 1. So nothing in the paper claims a marking without e_ij(1), and l.292–294 prove a refinement that is never stated.

Before (l.290–294):
```latex
and with $P$ every matrix unit. So $\varphi_\ell(S)$ generates
$M_{N_\ell}(\F_2)$, and Theorem~\ref{thm:general} applies. In both
quotients of $\EL_3(F)$, $e_{ij}(1)$ is the image of
$\prod_ae_{ij}(\tau_a)$, as $\sum_ae_a=1$ and $\sum_aD_\ell(e_a)=I$, so the
$e_{ij}(s)$ with $s\ne1$ also give expanders.\qed
```
After:
```latex
and with $P$ every matrix unit. So $\varphi_\ell(S)$ generates
$M_{N_\ell}(\F_2)$, and Theorem~\ref{thm:general} applies.\qed
```

### K3 (MEDIUM, −2 lines): state each credit once, before both corollaries
Coulon–Fournier-Facio and Kionke–Schesler are each cited twice, at l.303/306 and again at l.420/423. The G2 paragraph (l.419–423) repeats the opening credit paragraph after the proof.

Before (l.301–307):
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and even in a simple quotient of a
torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio}.
Kionke and Schesler proved that every finitely generated residually finite
group embeds in a finitely generated simple LEF
group~\cite[Theorem~1.2]{KionkeSchesler}, and raised the question which
groups embed in finitely generated simple amenable groups. For LEF groups
```
After:
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and even in a simple quotient of a
torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
so one simple Kazhdan group contains Higman's universal finitely presented
group~\cite{Higman}. Kionke and Schesler proved that every finitely
generated residually finite group embeds in a finitely generated simple
LEF group~\cite[Theorem~1.2]{KionkeSchesler}, so with Wilson's
theorem~\cite{Wilson} one simple LEF group contains every finitely
presented residually finite group. They raised the question which
groups embed in finitely generated simple amenable groups. For LEF groups
```
Before (l.419–424):
```latex
Without property~\textup{(T)}, Wilson's theorem~\cite{Wilson} and
\cite[Theorem~1.2]{KionkeSchesler} give a simple LEF group containing
every finitely presented residually finite group; without LEF, Higman's
universal finitely presented group~\cite{Higman} lies in a simple Kazhdan
group~\cite[Theorem~1.5]{CoulonFournierFacio}. Every group as in the last
statement of Corollary~\ref{cor:host} has unsolvable word problem: a
```
After:
```latex
Every group as in the last statement of Corollary~\ref{cor:host} has
unsolvable word problem: a
```
- **Reader merit:** before the corollaries the reader sees what each property gives alone, so "both at once" is visibly the new part. Every citation stays. The G2 content is unchanged.

### K4 (MEDIUM, −2 lines): drop the duplicate Thom sentence in Questions
l.75–78 already say that Thom's Kazhdan LEF group is not residually finite and not simple. l.505–507 repeat it.

Before (l.505–508):
```latex
with property~\textup{(T)} that are not residually finite. The groups
$G_X$ are sofic Kazhdan groups that are not residually finite, as is
Thom's group~\cite[\S5]{AlekseevThom}, but they are also simple. Is every
sofic infinite simple Kazhdan group LEF?
```
After:
```latex
with property~\textup{(T)} that are not residually finite. Is every
sofic infinite simple Kazhdan group LEF?
```

### K5 (MEDIUM, −3 lines): the roadmap paragraph
l.124–130 point to results the reader meets two pages later. The Turing-degree and factor pointers add nothing that page 1 needs; the abstract no longer mentions them either.

Before (l.124–130):
```latex
The periodic approximations make $\LC(X,\F_2)\rtimes_T\Z$ matricial, which
gives Theorem~\ref{thm:main}. The lamplighter group $\F_2\wr\Delta$ acting
on $\F_2^{\Delta}$ shows that the countable subgroups of the groups in
Theorem~\ref{thm:general} are exactly the countable LEF groups
(Corollaries~\ref{cor:lef} and~\ref{cor:host}). The word problems of the
groups $G_X$ realize every Turing degree, and the factors $L(G_X)$ fall
into continuum many isomorphism classes (Section~\ref{sec:wp}).
```
After:
```latex
Periodic approximations make $\LC(X,\F_2)\rtimes_T\Z$ matricial, which
gives Theorem~\ref{thm:main}, and lamplighter actions show that the
countable subgroups of the groups in Theorem~\ref{thm:general} are exactly
the countable LEF groups (Corollary~\ref{cor:host}).
```

### K6 (LOW, −1 line; also UNCLEAR): "The equality holds"
At l.223 "The equality" has no near antecedent: the equality was two clauses earlier. Its reason is the tower-step fact at l.187–189.

Before (l.220–225):
```latex
$\rho_k(\tau_s)=\varphi_k(s)$. Both are onto, so $G$ and
$\EL_3(M_{N_k}(\F_2))=\SL_{3N_k}(\F_2)$ are quotients of $\EL_3(F)$, which
is generated by the $e_{ij}(1)$ and $e_{ij}(\tau_s)$; in both quotients
$e_{ij}(1)$ and $e_{ij}(\tau_1)$ have the same image. The equality holds
as transvections generate $\SL_{3N_k}(\F_2)$ and those inside one block are
commutators of those between blocks. A word of length $\lambda$ or less in
```
After:
```latex
$\rho_k(\tau_s)=\varphi_k(s)$. Both are onto, so $G$ and
$\EL_3(M_{N_k}(\F_2))$, which equals $\SL_{3N_k}(\F_2)$ as in the tower
step, are quotients of $\EL_3(F)$, which is generated by the $e_{ij}(1)$
and $e_{ij}(\tau_s)$; in both quotients $e_{ij}(1)$ and $e_{ij}(\tau_1)$
have the same image. A word of length $\lambda$ or less in
```

### K8 (OPTIONAL, 0 lines): move "Brown's formulation"
The subsection l.240–256 sits inside §1, the proof of the general theorem, between the finite models and §2. A reader following Brown → Ozawa → Pestov looks for it once G_X is built. Move it unchanged to just after §2's `\qed` (l.294, or l.291 after K2). Its "G" covers the groups of both theorems, so no wording changes.

### Considered and kept (reader merit outweighs length)
- **Pestov–Kwiatkowska sentence (l.78–81):** the printed record that the question was open in 2012.
- **Stepanov alternative and Matui "in the same way" (l.93–103):** credit.
- **Grigorchuk–Medynets decidability sentence (l.479–481):** credit for the parallel result.
- **No-decidable-host sentence (l.423–430):** sharpness of Corollary 4, with the KMS and Rauzy credit.
- **SL_3(Z) paragraph (l.432–442):** it is why the lamplighter hosts are needed, and it is complete in 11 lines.
- **NPS sentence (l.491–494):** it prevents the separable-factor paragraph from reading as priority.

Total K2–K6: −11 source lines, about 0.2 pp. That room pays for candidate C3.

## 2. What a reader remembers
1. For every infinite minimal subshift X, G_X = EL_3(LC(X,F_2)⋊Z) is an infinite, finitely generated, simple Kazhdan group that is a limit of finite simple groups SL_{3N}(F_2) forming expanders. So it is LEF, sofic and hyperlinear, which answers Brown, Ozawa and Pestov.
2. A finitely generated group is LEF if and only if it is a subgroup of such a group, and one such group contains every recursively presented finitely generated LEF group.
3. The mechanism: a finitely generated ring gives (T); periodic approximations give matrix models; a commutator lands in a finite simple GL_d(F_2) over a clopen tower.

**Page 1:** it states 1 (Theorem 1) and 2 (in the abstract, l.37–41), but only half of 3. The (T) step is there, but the models sentence is cut mid-way at l.87 and the simplicity mechanism is on page 2. K1 fixes this.

## 3. Section order
- **Serves the reader:** engine first (§1), then the example (§2), then the characterization (§3), then consequences (§4), then Questions.
- **One misplacement:** Brown's formulation inside the proof of Theorem 2 (K8).
- **§4 pairs word problems with factors, and that is justified:** the factor paragraph uses §4's cylinder word and the Sturmian continuum proved there.
- **§2 is short (37 lines):** a reader who wants only G_X must read §1 in Λ-notation. Acceptable, since §1 is general and complete.

## 4. Title and abstract against what is proved
- **Title:** "Infinite simple Kazhdan groups that are limits of finite simple groups" is exact for Theorems 1–2 and Corollary 3. "Infinite" is needed, since finite simple groups have (T) trivially. Keep it.
- **Abstract:** every sentence is proved in the text.
  - "Their Cayley graphs form a family of expanders" omits "with respect to the images of a fixed generating set", which is normal for an abstract.
  - The last sentence matches Corollary 4 exactly ("every recursively presented finitely generated group with this property").
  - It claims no priority and names no "first". Keep it.

## 5. Candidates for rev4.1 (reader merit only)

### C1: sk-free-7, continuum many G_X with none a subgroup of another. IN, after a PASS
- **Where:** Corollary `cor:wp` l.450, "Every Turing degree occurs." becomes "Every Turing degree occurs, so there are continuum many groups $G_X$, none of which is isomorphic to a subgroup of another." Add three proof lines after l.476, following the proposal's text: a word problem only goes up along an embedding, plus an antichain of continuum many Turing degrees. One bibitem.
- **Cost:** +4 text lines, +3 bibliography lines.
- **Why in:** rev4's separable-factor paragraph already gives continuum many nonisomorphic G_X; this upgrades nonisomorphism to non-embeddability. The proof adds no machinery beyond one textbook fact.
- **Gates:** a PASS on `continuum-many-subshift-el-groups-pairwise-non-embeddable` (queued with sk-verify-13), and the Odifreddi p. 462 locator (VERIFY-PENDING). Otherwise use the proposal's fallback "by a construction of Sacks" with the primary Sacks source checked.

### C2: sk-free-8, non-uniform exponential growth for Thue–Morse. OUT
- **Why out:** the remark's key step, carrying Sauer–Schesler's counting from Aut(F_{4·2^n}) to EL_{3·2^n}(R_X), is neither printed (the proposal says it needs 20 lines) nor citable. The note's standard is that every claim is proved or cited, so a remark resting on an unprinted transfer fails it.
- **Other costs:** it is off the paper's line (approximation and simplicity, not growth); it adds +10 text and +10 bibliography lines; and it carries a novelty caution (Hull, Theorem 8.6).
- **Keep:** Cairn, or a separate short note if the user wants one.

### C3: sk-decidable-host, the solvable-word-problem clause. IN, after a PASS (strongest of the three)
- **Where:** Corollary `cor:lef` gains "It is LEF with solvable word problem if and only if this group can be chosen with solvable word problem." The Boone–Higman sentence (l.309–311) then changes from "parallels" to an exact analogue that keeps a solvable word problem, and credits Thompson 1980 for simple hosts with solvable word problem.
- **Architecture:** rev4's combined proof builds the overgroup by isolation inside ∏_ω Sym, and that overgroup is not effective. So the clause needs the half-line overgroup C(Γ), for finitely generated Γ only.
  - Add one paragraph of at most 10 lines after the proof: C(Γ) is LEF with WP(C(Γ)) ≡ WP(Γ) (proposal P1, compressed), and the host's entries reduce to WP(C(Γ)) (proposal P3).
  - Corollary 4 keeps the isolation overgroup.
- **Cost:** about +15 text lines and +3 bibliography lines, offset by K2–K6.
- **Why in:** it is a genuinely new characterization. It upgrades the introduction's Boone–Higman parallel to a theorem, adds no new machinery, and answers the natural question of which LEF groups have decidable simple Kazhdan LEF hosts.
- **Gates:**
  - a PASS on `half-line-overgroup-keeps-lef-and-solvable-word-problem` and `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts` (queued with sk-verify-13, served by sk-verify-14);
  - the Thompson 1980 bibitem checked at source;
  - the compressed P1/P3 LaTeX reviewed as note text.

## 6. Status
No Cairn nodes; referee prose only. Not checked: the mathematics (referee (a)), credit locators (referee (b)), and whether K1's page break lands exactly at l.100, which needs a recompile.
