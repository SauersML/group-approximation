# Andrews–Curtis conjecture: status pins and the stable-AK(3) correction (2026-09-13)

Lane `hl-andrews-curtis`. Sources were fetched as arXiv e-prints on MSI
(`/scratch.global/sauer354/hl-andrews-curtis/lit/`) and read there. Line numbers
refer to those files. Primary sources that were not read are marked.

## 1. The rank-2 frontier

J. Carreras, *Machine-checkable equivalence certificates at the length-14
Andrews–Curtis frontier*, arXiv:2607.23611 (submitted 26 July 2026),
`manuscript.tex` l.100–105:

> Miasnikov--Myasnikov \cite{MM03} proved that every balanced two-generator
> presentation of the trivial group with total relator length $\le 12$ is
> AC-trivializable. Havas--Ramsay \cite{HR03} showed that at length 13 every
> such presentation is AC-trivializable or AC-equivalent to $\AK(3)$; since
> $\AK(3)$ itself has total length 13 and remains open, $\AK(3)$ is the unique
> minimal potential counterexample, and unconditional verification stops at 12.

The primary sources MM03 and HR03 were not read here.

A. Shehper et al., *What makes math problems hard for reinforcement learning: a
case study*, arXiv:2408.15332v2 (11 Feb 2025), `sec/conjecture.tex`:
- l.38: "is the shortest presentation, up to AC-equivalence, that eludes all
  attempts at length reduction."
- l.43: "$\AK(2)$ has length 11 and has been established to be AC-trivial
  \cite{genetic}, whereas $\AK(3)$ is the aforementioned presentation with length 13."
- l.46: "Notably, \cite{Panteleev-Ushakov} found that no sequence of AC-moves that
  allows relator lengths to increase up to 20 trivializes $\AK(3)$."

Panteleev–Ushakov, arXiv:1609.00325 (`ac15.tex`, abstract): "Unfortunately,
despite a lot of effort we were unable to trivialize any of AK(n)-presentations,
for $n>2$." Their per-relator length-20 bound is taken from Shehper et al.; it
was not located verbatim in their TeX.

### Length 14: Carreras, Theorem on GS bottlenecks (proof, l.437–447)

> Lower bounds: the exclusive-cap-26 search from the three sources
> $\{\AK(3),\ \PP{1},\ \PP{2}\}$ exhausted 6{,}212{,}968 canonical states without
> any cross-source intersection, excluding every GS path of bottleneck $\le 25$;
> the exclusive-cap-27 search exhausted 13{,}504{,}944 states, excluding
> bottleneck $\le 26$.

Carreras stresses (l.450–455) that these are statements about the GS-substitution
graph, "not AC-distance lower bounds". The certificates and the verifier
`ac_verify.py` are in the arXiv ancillary files.

### Competition context

The SAIR Andrews–Curtis challenge (T. Tao, blog post of 2026-09-11) uses
"10,115 balanced two-generator presentations of the trivial group", with an AC
track and a stable AC track ("we allow up to eight generators"). It closes on
November 30, 2026.

## 2. Correction: stable AC-triviality of AK(3) is not established

Several secondary summaries repeat that Shehper et al. (2024) proved AK(3)
*stably* AC-trivial. The current version of their paper withdraws that basis.

Shehper et al., arXiv:2408.15332v2, `sec/introduction.tex` l.84–91 (compiled
text):

> Motivated by this connection and by the claim in \cite{MMS} that the presentation
> [(eq:MMS3)] is stably AC-trivial, we apply reinforcement learning to demonstrate
> its AC equivalence to $\AK(3)$.
> However, after closer inspection, we discovered a subtle misprint in
> \cite[p.10]{MMS} that had gone unnoticed for more than 20 years. This misprint
> undermines the claim that \eqref{eq:MMS3} is stably AC-trivial.

`sec/stable.tex` l.195 (remark): "Their manuscript contained an unfortunate
misprint in the 13th relator, where it is written as $x_{13}=x_5 x_{12} x_5^{-1}$.
The resultant presentation is not a Wirtinger presentation of any knot diagram,
affecting the validity of one of their main theorems (\cite[Theorem 1.4]{MMS})."

`app/mms.tex` l.19: "which is AC-equivalent to $\AK(3)$. Note, however, that
unlike any presentation AC-equivalent to a correct Wirtinger presentation, these
presentations are not necessarily stably AC-trivial."

`ac_paper.tex` l.50 keeps the former appendix commented out:
`%\input{app/stable_ak3}`.

A. Lisitsa, *Stable Andrews-Curtis trivialization of AK(3) revisited*,
arXiv:2501.18601, `main_arxiv.tex` l.475–479:

> In their proof of stable AC-trivializability of AK(3) the authors of
> \cite{shehper2024makesmathproblemshard} have found a sequence of
> AC-transformations which transforms balanced presentation P [...] into AK(3).
> The presentation $P$ is a particular instance of a family of presentations for
> which it was shown in \cite{ACE} that they are all stably AC-trivializable.

Here `\bibitem{ACE}` is "Alexei G. Myasnikov, Alexei D. Myasnikov and Vladimir
Shpilrain. On the Andrews–Curtis equivalence. Contemporary Mathematics, 296,
2002", the same source whose misprint Shehper et al. identify. Lisitsa's
automated proofs therefore establish AC-equivalence of P and AK(3); stable
AC-triviality still rests on the undermined family claim.

**Conclusion.** Stable AC-triviality of AK(3) is OPEN. Claim node
`ak3-is-stably-ac-trivial`.

## 3. What Shehper et al. prove for correct Wirtinger presentations

`sec/stable.tex` l.205–206, Lemma `lem:all_ac_equiv`:

> Let $\langle x_1,\ldots, x_n \mid r_1,\ldots,r_{n-1}\rangle$ be a presentation
> of $\mathbb{Z}$. Then there exists one word $x$ in the $x_i$, such that for any
> word $w$ that makes the group trivial, the balanced presentation of the trivial
> group $\langle x_1,\ldots, x_n \mid r_1,\ldots,r_{n-1}, w\rangle$ is
> AC-equivalent to $\langle x_1,\ldots, x_n \mid r_1,\ldots,r_{n-1}, x\rangle$.

Theorem `thm:unknot` (l.217): every Wirtinger presentation of an unknot diagram,
with one relator removed and any $w$ of exponent sum $\pm 1$ added, is AC-trivial.

Conjecture `conj:general_Z`, l.255–256:

> Let $\langle x_1,\ldots x_n | r_1,\ldots, r_{n-1}\rangle$ be any presentation of
> $\mathbb{Z}$ where each $x_i$ generates $\mathbb{Z}$, i.e., $x_i=x_j^{\pm 1}$ for
> any $i,j$. Then for any word $w$ in the $x_i$ with exponent sum $\pm 1$, the
> presentation $\langle x_1,\ldots x_n | r_1,\ldots, r_{n-1}, w\rangle$ is AC-trivial.

## 4. New in this lane

`shehper-z-conjecture-iff-one-stabilization-ac` shows that, for each n ≥ 2,
Conjecture `conj:general_Z` on n generators is equivalent to the statement that
every balanced presentation of the trivial group on n−1 generators becomes
AC-trivial after one stabilization.
- **Consequence:** the rank-3 case of the conjecture already implies that AK(3)
  is stably AC-trivial.
- **Credit:** no novelty is claimed. The argument is elementary once
  `lem:all_ac_equiv` is available.

## 5. Not done

- No bounded exhaustive AC search was run. An exhaustive search with total-length
  cap L adds nothing beyond the per-relator length-20 negative reported for
  Panteleev–Ushakov unless L is around 30 or more, which is out of reach.
- No invariant separating AC-classes was found. Every standard homotopy or K-theory
  invariant is constant on balanced presentations of the trivial group.
