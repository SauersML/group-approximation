# sk-reader-grad: cold read of the simple Kazhdan note, rev4.5

Base: `simple_kazhdan_sofic_group.tex` rev4.5 (8b36733d78, md5 29d63f7944bccccbf9a91b0b2714c0b4). All line numbers below refer to this revision.

**Reader:** a strong PhD student in geometric group theory. They know property (T), expanders and sofic groups from surveys. They do not know crossed product rings, subshifts or marked groups.

**Method:** one pass top to bottom, as a reader; math re-checked only where I stalled.

**Verdict:** no mathematical error found. The stalls are about exposition and are concentrated on page 1 (the LEF mechanism, marked-group limits, the ring) and in the proof of Corollaries 3–4.

## 1. Stall log

| # | Lines | Kind | Why I stalled |
|---|---|---|---|
| S1 | 30–31, 58 | undefined term | "minimal subshift" is never defined; it is the first hypothesis of the main theorem. |
| S2 | 62, 111 | notation before definition | `LC(X,F_2)⋊_T Z` is not defined until l.133–136; in Theorem 1 the reader cannot picture the ring. |
| S3 | 65–68, 118–120 | undefined term | "limit in the space of marked groups" is undefined until the proof (l.223–233), so "So G_X is LEF" (l.67–69) is taken on trust. |
| S4 | 77–80 | over-compressed | "Periodic sequences … give the ring finite models in M_N(F_2)" does not say what the models are (functions → diagonal matrices, shift → cyclic permutation). This is the key LEF idea. |
| S5 | 80–82 | logical jump | "which form expanders as in Kassabov's construction" does not give the reason: they are quotients of one Kazhdan group, EL_3 of a free algebra (only visible at l.214–235). |
| S6 | 82–85 | undefined term; missing step | "clopen tower" is undefined. The sketch stops at "an elementary matrix" and never says how one matrix gives all of G_X (minimality, l.202–208). |
| S7 | 89–92 | over-compressed | The Stepanov sentence ("pr+qs=0 with (r,s)≠0 by a dimension count on a tower over one small cylinder") uses towers and small sets before they are defined. It could not be parsed on first reading. |
| S8 | 94–102 | flow | The naming credits and the Thom / Pestov–Kwiatkowska background interrupt between the proof sketch and "The proof works for other actions". |
| S9 | 110–111, 133–207 | notation clash | The Cantor set is called `Z` (italic) right next to `⋊\Z` (blackboard) in Theorem 1. "LC(Z,F_2)" reads as functions on the integers at a glance. |
| S10 | 115–116 | reread (quantifiers) | "for all r,s … we have … for large k": I had to reread to see that k depends on r,s. |
| S11 | 144 | small jump | "So the e_ij(s) with s∈S generate G": this needs S∋1 and (1). It is fine once seen. |
| S12 | 153–155 | reread | The definition of "small" packs two conditions into one sentence. "coefficient" is only defined implicitly at l.162. |
| S13 | 156–158 | small jump | "every nonempty clopen set contains a nonempty small one": the reader supplies "take a small clopen neighborhood of a point moved by all ξ". |
| S14 | 171–173 | ambiguous term | "constant coefficients" (the coefficient at u_e) collides with "constant on V", used four times nearby. I first read it as "coefficients that are constant functions". |
| S15 | 218–220 | notation | `τ_1` reads as "the first letter", not "the letter of 1∈S". |
| S16 | 225–226 | undefined term (mild) | "algebraic ultraproduct" is standard, but the proof relies on it heavily. |
| S17 | 245 | undefined term | "cylinder indicators": cylinders are never defined. |
| S18 | 281–282 | motivation | "and G is not residually finite" is not used in the paragraph, and the reader looks for why it is there. |
| S19 | 313 | forward reference | `L(Y)` is used in Corollary 4; the language is only named in Corollary 5 (l.465–466). |
| S20 | 327–354 | no roadmap | The longest proof has three stages (Γ ≤ [Δ,Δ]; lamplighter host; [Λ,Λ] ↪ G_Δ) and never announces them. |
| S21 | 338–346 | over-compressed | The powers-of-2 level trick: the key fact, that the two conjugates are never both nontrivial on a level other than 0, is left for the reader to derive. |
| S22 | 377–379 | over-compressed | "move the attached points near e as Λ moves the points of Ω": "near e" means "on a ball of coordinates around e"; this took a reread. |
| S23 | 412–438 | hardest paragraph | θ, κ, ζ, 3r, 5r arrive with no statement of purpose. "Transversals give a bijection κ" hides the coset count. |
| S24 | 37–41 | reread | The abstract has two "if and only if" in one sentence and repeats the host description from l.32–33. (U1 named the host deliberately; I offer no NEW text.) |

## 2. The three questions

**Q1. After page 1, could I explain to a friend why G_X is simple, Kazhdan and LEF?**
- **Kazhdan: yes.** EL_3 over a finitely generated ring has (T) by Ershov–Jaikin-Zapirain, and the ring is finitely generated.
- **Simple: mostly.** "A nontrivial normal subgroup contains a commutator in a copy of GL_d(F_2)" is clear, but "tower" is undefined and the last step (minimality spreads one elementary matrix to everything) is missing.
- **LEF: no.** Page 1 does not say what the finite models are, and "limit in the space of marked groups" is undefined, so the passage from models to LEF is on trust. The expander claim cites Kassabov without the one-line reason (quotients of one Kazhdan group).
- **The ring itself is undefined on page 1** (S2).

**Q2. Which proof was hardest to follow, and why?**
- **Corollaries 3–4.**
  - The hardest paragraph is l.412–438: the half-line Neumann–Neumann model with θ, κ, ζ and the constants 3r, 5r.
  - Next is l.338–346, the powers-of-2 levels.
  - The reasons: several objects arrive before their purpose is stated, there is no roadmap for the three stages, and the decisive combinatorial facts (only level 0 carries both conjugates; the domain and image of θ have equal index) are implicit.
- **Theorem 2.** Within Theorem 2 the densest step is "x ∈ H_V" (l.187–198), but it checks line by line and needs no change.

**Q3. What would I remember a week later?**
- EL_3 over the crossed product ring of a minimal subshift is simple, Kazhdan and LEF, so simple Kazhdan groups can be sofic and hyperlinear (Brown, Ozawa, Pestov).
- The beautiful trick: the approximate matrix models become faithful in the ultraproduct because the kernel is a normal subgroup and G is simple (l.224–231).
- LEF ⇔ subgroup of such a host; one host for all recursively presented LEF groups.
- The word problem of G_X has the degree of L(X).
- **I would not remember** Theorem 2's hypotheses precisely, or the lamplighter models.

## 3. Top 10 fixes (OLD → NEW), ranked by reader benefit

No mathematics changes. Costs are estimated in typeset lines (11pt amsart), about **+10 in total**. Fixes 9–10 are the first to drop if the budget is tight.

**F1 (S4, S5), l.77–82, +1.5.** The LEF mechanism and the reason for expanders on page 1.
OLD: `Periodic sequences approximating $X$ give the ring finite models in the matrix algebras $M_N(\F_2)$, as in the proof by Grigorchuk and Medynets that topological full groups of minimal Cantor systems are LEF~\cite[Theorem~2.6]{GM}. So $G_X$ is a limit of the groups $\SL_{3N}(\F_2)$, which form expanders as in Kassabov's construction~\cite{Kassabov}.`
NEW: `A periodic sequence of period $N$ approximating $X$ turns the shift into a cyclic permutation matrix and each locally constant function into a diagonal matrix, which gives the ring approximate finite models in the matrix algebras $M_N(\F_2)$, as in the proof by Grigorchuk and Medynets that topological full groups of minimal Cantor systems are LEF~\cite[Theorem~2.6]{GM}. So $G_X$ is a limit of the groups $\SL_{3N}(\F_2)$. These are quotients of one Kazhdan group, $\EL_3$ of a finitely generated free algebra over $\F_2$, so they form expanders, as in Kassabov's construction~\cite{Kassabov}.`
Check: matches l.257–263 (P cyclic, D_ℓ(f) diagonal) and l.211–215, 233–235 (EL_3(F), EJZ Thm 1.1).

**F2 (S3), after l.75 ("…preserving the products that stay in that subset."), +2.**
NEW, appended: `A finitely generated group $G$ is a limit of finite groups $G_k$ in the space of marked groups~\cite{Grigorchuk,Champetier} if the generators of $G$ correspond to generators of $G_k$ so that, for every word $w$ in them and all large $k$, $w$ is trivial in $G$ if and only if it is trivial in $G_k$; then $G$ is LEF.`
Check: this is exactly what l.220–233 proves. "All large k" is quantified after w, so k depends on w.

**F3 (S1), l.58–59, +0.7.**
OLD: `Let $X\subseteq A^{\Z}$ be an infinite minimal subshift over a finite alphabet, with shift $T$,`
NEW: `Let $X\subseteq A^{\Z}$ be an infinite minimal subshift over a finite alphabet, that is, a closed shift-invariant set in which every orbit is dense, with shift $T$,`

**F4 (S2), l.75–76, +1.**
OLD: `The ring $\LC(X,\F_2)\rtimes_T\Z$ is finitely generated, so by`
NEW: `The ring $\LC(X,\F_2)\rtimes_T\Z$ consists of the finite sums $\sum_jf_ju^j$ with $f_j\in\LC(X,\F_2)$, multiplied using $ufu^{-1}=f\circ T^{-1}$. It is finitely generated, so by`
Check: l.240.

**F5 (S6), l.82–85, +1.**
OLD: `In the proof of simplicity, a nontrivial normal subgroup contains a nontrivial commutator lying in a copy of the finite simple group $\GL_d(\F_2)$ over a clopen tower, so it contains this group and with it an elementary matrix.`
NEW: `In the proof of simplicity, a nontrivial normal subgroup contains a nontrivial commutator lying in a copy of the finite simple group $\GL_d(\F_2)$ over a clopen tower, a small clopen set with its disjoint translates. So it contains this group and with it an elementary matrix, from which minimality gives every elementary matrix.`
Check: l.175–185 (the aV, a∈B_w, are disjoint) and l.202–208 (J = R).

**F6 (S14), l.171 and l.172–173, +0.**
OLD: `The constant coefficients agree on every small $V$, so they agree everywhere.` → NEW: `The coefficients at $u_e$ agree on every small $V$, so they agree everywhere.`
OLD: `comparing constant coefficients in $cc^{-1}=1$` → NEW: `comparing coefficients at $u_e$ in $cc^{-1}=1$`
Check: consistent with "coefficients at $u_\xi$" at l.168.

**F7 (S20), after l.330 ("…so that it is infinite."), +2.**
NEW, inserted: `We embed $\Gamma$ in the derived subgroup of a $2$-generated LEF group $\Delta$, and then $[\Delta,\Delta]$ in a group of Theorem~\ref{thm:general} built from a lamplighter action of $\Delta$.`
Check: Δ = ⟨a,b⟩ (l.352); [Δ,Δ] ≤ [Λ,Λ] ↪ G_Δ (l.397–403). The sentence deliberately does not claim that Δ itself embeds.

**F8 (S21), l.343–346, +1.**
OLD: `As distinct pairs of powers of $2$ have distinct differences, all below a quarter of the modulus, the word $w_j=[b^{-2^{2j-1}}ab^{2^{2j-1}},\,b^{-4^j}ab^{4^j}]$ evaluated at $(a_k,b_k)$ acts by $[f_{jk},t_k]$ on the level $0$ and trivially on the other levels, for $j\le k$.`
NEW: `As distinct pairs of powers of $2$ have distinct differences, all below a quarter of the modulus, the two conjugates in $w_j=[b^{-2^{2j-1}}ab^{2^{2j-1}},\,b^{-4^j}ab^{4^j}]$, evaluated at $(a_k,b_k)$, cannot both act nontrivially on a level other than $0$. So $w_j(a_k,b_k)$ acts by $[f_{jk},t_k]$ on the level $0$ and trivially on the other levels, for $j\le k$.`
Check, re-derived:
- On level i, the first conjugate acts as a_k on level i+2^{2j−1}, and the second as a_k on level i+4^j.
- If both levels are special (powers 2^p, 2^q ≤ 4^k), then 2^q−2^p ≡ 2^{2j−1} mod 4^{k+1}. Both are below 4^k, so 2^q−2^p = 2^{2j−1}, which forces (q,p) = (2j, 2j−1) and i = 0.
- "cannot both act nontrivially" stays true even when f_jk or t_k is trivial.

**F9 (S23), l.428–429, +0.5.**
OLD: `Transversals give a bijection $\kappa$ of $Q^{[-3r,3r]}$ with $\kappa(vx)=\theta(v)\kappa(x)$ for $v$ in the domain of $\theta$.`
NEW: `The domain and the image of $\theta$ have equally many right cosets, so matching them through transversals gives a bijection $\kappa$ of $Q^{[-3r,3r]}$ with $\kappa(vx)=\theta(v)\kappa(x)$ for $v$ in the domain of $\theta$.`
Check: θ is an isomorphism between two subgroups of the same finite group, each of index |Q|. κ(vx_i) = θ(v)x'_i for transversals (x_i), (x'_i).

**F10 (S12), l.153–155, +0.3.**
OLD: `Call a clopen set $V$ small if $V\cap\xi V=\varnothing$ for $\xi\in B_{2w}\setminus\{e\}$ and every $f\circ\xi$, with $\xi\in B_w$ and $f$ a coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$.`
NEW: `Call a clopen set $V$ small if (i) $V\cap\xi V=\varnothing$ for every $\xi\in B_{2w}\setminus\{e\}$, and (ii) $f\circ\xi$ is constant on $V$ for every $\xi\in B_w$ and every coefficient $f\in\LC(Z,\F_2)$ of an entry of $g$ or $g^{-1}$.`

## 4. Zero-cost extras, not ranked

- **E1 (S10), l.115–116.** OLD `and for all $r,s\in R$ we have $\varphi_k(r+s)=\varphi_k(r)+\varphi_k(s)$ and $\varphi_k(rs)=\varphi_k(r)\varphi_k(s)$ for large $k$.` → NEW `and for all $r,s\in R$ and all large $k$, depending on $r$ and $s$, we have $\varphi_k(r+s)=\varphi_k(r)+\varphi_k(s)$ and $\varphi_k(rs)=\varphi_k(r)\varphi_k(s)$.`
- **E2 (S15), l.219–220.** OLD `in both quotients $e_{ij}(1)$ and $e_{ij}(\tau_1)$ have the same image` → NEW `in both quotients $e_{ij}(1)$ and $e_{ij}(\tau_s)$ with $s=1$ have the same image`.
- **E3 (S9).** Rename the Cantor set `Z` → `C` in Theorem 2 and §1 (l.110, 111, 133, 148, 156, 206, 207, and F10 if adopted). Capital C is unused elsewhere. Grep every italic `Z` that is not `\Z`.
- **E4 (S17), l.245.** OLD `which are the cylinder indicators,` → NEW `which are the indicators of the cylinders $\{x:x_{[i,j]}=v\}$,`.
- **E5 (S19), l.465–466.** OLD `the language $L(X)$ of $X$` → NEW `the language $L(X)$ of $X$, the set of words occurring in points of $X$`. Corollary 4 already points forward to Corollary 5.
- **E6 (S7).** Move the Stepanov sentence (l.89–92) to the end of the Simplicity subsection (after l.208), where towers and small sets are defined. It costs 0 lines.
- **E7 (S8), structural, uncertain.** Move l.94–102 (credits and background) before Theorem 1, so that the page-1 sketch leads straight into "The proof works for other actions". The cost is that Theorem 1 arrives later.
- **E8 (S18), l.281–282.** Either say why non-residual finiteness matters there, or drop "and $G$ is not residually finite".

## 5. What already reads beautifully (keep)

- The opening question (l.47): one line, and it is the right question.
- The ultraproduct faithfulness argument (l.224–231): short, conceptual and memorable.
- The commutation criterion (l.160–162) and the matrix units ε_ab (l.176–181): crisp.
- The word-problem converse (l.479–481): one line, and exactly the right test word.
