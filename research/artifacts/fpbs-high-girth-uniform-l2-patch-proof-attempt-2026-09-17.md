# Nachmias-Peres path counting with the Benjamini-Nachmias-Peres girth bound gives uniform l2 constants

*Attempt artifact (2026-09-17), formerly route `fpbs-high-girth-uniform-l2-patch-proof` into `fpbs-high-girth-uniform-l2-patch`, requires [fpbs-l2-gap-baire-dichotomy]. Demoted from the graph together with `fpbs-l2-gap-baire-dichotomy`, which it requires and which referee lenses 1 and 3 refuted as written over its "never isolated" sentence. Lenses 2 and 3 checked Proposition 3.0, Theorem 3.1 and Corollary 3.2 line by line and found no unfilled step. Restore it as a route once the dichotomy claim is repaired and a full referee pass survives.*

Source: `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`, Section 3. The two published
inputs are imported verbatim from the arXiv e-print sources, fetched
2026-09-17. The only other inputs are the elementary facts (F1) and (0.1) of
`research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`, and the
self-contained Lemma 1.3 (`||P|| = rho` on transitive graphs).

**Import 1.** Benjamini, Nachmias, Peres, *Is the critical percolation
probability local?*, arXiv:0901.4616, `localpc.tex`:

> \begin{theorem} \label{localpc} There exists an absolute constant $C>0$ such
> that if $G$ is a non-amenable regular graph with degree $d$ and girth $g$ such
> that the bottom of spectrum of $I-P$ is $\lambda_1>0$, then
> $$ p_c(G) \leq {1 \over d-1} + {C \log\big( 1 + {1 \over \lambda_1^2} \big) \over dg} \, .$$

**Import 2.** Nachmias, Peres, *Non-amenable Cayley graphs of high girth have
$p_c<p_u$ and mean-field exponents*, arXiv:1207.1480:

> \begin{lemma} \label{nbwvssrw} For any graph $G$, vertices $x,y$ and
> $n \geq 0$ we have
> $$ \pnbw^n(x,y) \leq \sum_{j \geq n} \psrw^j(x,y) \, .$$

> since $d(d-1)^{n-1} \pnbw^n(x,y)$ is an upper bound on the number of simple
> paths of length precisely $n$ between $x$ and $y$.

**Steps.**

1. Union bound over simple paths and Import 2 give, entrywise,
   `tau_q <= I + sum_{n>=1} q^n d(d-1)^{n-1} sum_{j>=n} P^j`.
2. Nonnegative domination and `||P^j|| <= rho^j` give
   `||T_q|| <= 1 + (d/(d-1)) r/((1-r)(1-rho))`, with `r = q(d-1)rho`.
3. Take `q = (1 + 1/rho)/(2(d-1))`. Then `r = (1+rho)/2`, `||T_q|| <= 1 + 3/eta^2`,
   and `q - 1/(d-1) >= eta/(2(d-1))`.
4. Import 1, with `lambda_1 = 1 - rho >= eta` and `g >= L(eta)`, gives
   `p_c <= 1/(d-1) + eta/(4(d-1))`.
5. So `p_c + eta/(4(d-1)) <= q`, and (F1) gives the bound at that parameter.
   The girth condition involves finitely many words, so it is clopen. With
   `L >= 3` it forces `d = 2k`.
