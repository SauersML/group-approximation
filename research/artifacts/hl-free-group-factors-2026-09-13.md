# Free group factor isomorphism problem: source pins and route map (2026-09-13)

Lane hl-free-group-factors. All TeX sources were fetched on MSI into
`/scratch.global/sauer354/hl-free-group-factors/src/` via `https://arxiv.org/e-print/<id>`.
The arXiv API query endpoint returned nothing from MSI, so ids were found by web
search and then the sources were fetched directly.

## Sources read at source

| arXiv id | paper | status used |
|---|---|---|
| funct-an/9211012 | Dykema, *Interpolated free group factors* (PJM 163, 1994) | Theorem 2.4 (l.440–441), definition of `M_gamma` (l.145–150), Kadison attribution (l.130–136) |
| 2305.08168 | Goldbring–Pi, *On the first-order free group factor alternative* | alternative as quoted from Rădulescu Cor. 4.7 (l.170–175); Main trichotomy (l.188–195); `F_fo` definition and closedness (l.388); amplification lemma (l.339) |
| 2308.14109 | Hayes–Jekel–Kunnawalkam Elayavalli, *Consequences of the random matrix solution to the Peterson–Thom conjecture* | intro theorems l.280 (coarseness), l.325 (solidity generalization), l.363 (Pinsker dichotomy): all stated for arbitrary `t > 1` |
| 2609.11074 | Shlyakhtenko, *On the II_1 factors of Fuchsian groups* (preprint, Sept 2026) | Corollary `cor:torsionFreeAreFree` (l.155–161): `L(pi_1(Sigma_g)) = L(F_{2g-1})` |
| 2412.20346 | Arulseelan, *On the elementary equivalence of group factors* | **WITHDRAWN**: v2 2024-12-31, arXiv comment "Error in main theorem" (abs page, 2026-09-13); e-print endpoint returns "This version of 2412.20346 has been withdrawn and is unavailable" |

Already on main, reused: Jung arXiv:math/0510576 and Hayes arXiv:1505.06682
(`cartan-algebras-are-strongly-one-bounded`).

Not read, second-hand only: Rădulescu Invent. Math. 115 (1994) Cor. 4.7;
Goldbring–Hart on `F_fo`.

## Verbatim excerpts

Dykema l.440–441:

    \proclaim{Theorem 2.4}
      $$ L(\freeF_r)_\gamma=L(\freeF(1+\frac{r-1}{\gamma^2})) \tag9 $$
      for $1<r\le\infty$ and $0<\gamma<\infty$.
    \endproclaim

Goldbring–Pi l.188–195 (Main theorem):

    Exactly one of the following holds:
    \item $L(\F_r) \equiv L(\F_s)$ for all $1 < r \leq s < \infty$, and the first-order fundamental group of $L(\F_r)$ is $\bR_+$ for all $1 < r \leq \infty$.
    \item $L(\F_r) \not \equiv L(\F_s)$ for all $1 < r < s < \infty$, and the first-order fundamental group of $L(\F_r)$ is $\{1\}$ for all $1 < r < \infty$.
    \item There is $\alpha\in (1,\infty)$ such that the first-order fundamental group of $L(\F_r)$ is $\alpha^\bb Z$ for all $1<r < \infty$.

Goldbring–Pi l.339: "Let $\cM, \cal{N}$ be $II_1$ factors satisfying $\cM \equiv \cal{N}$. Then for any $t\in \bR_+$, we have $\cM_t \equiv \cal{N}_t$."

HJKE l.363 (Pinsker dichotomy): "Fix $t>1$, and let $Q,P$ be maximal amenable subalgebras of $L(\bF_{t})$. Then exactly one of the following occurs: [...] there are nonzero projections $e\in Q,f\in P$ and a unitary $u\in L(\bF_{t})$ so that $u^{*}(ePe)u=fQf$, or for any diffuse $Q_{0}\leq Q$ we have that $Q_{0}\nprec P$."

Shlyakhtenko l.155–161: "If $\Lambda$ is a torsion-free finitely degenerated non-elementary discrete subgroup of $PSL_{2}(\mathbb{R})$, then $L(\Gamma)\cong L(\mathbb{F}_{r})$ (where $r$ is as above). In particular, if $\Lambda=\pi_{1}(\Sigma_{g})$ is the fundamental group of a surface of genus $g\geq2$, then $L(\Lambda)\cong L(\mathbb{F}_{2g-1}).$"

## Route map

- **Isomorphism.** By the alternative, one pair decides everything.
  - Candidate invariants:
    - 1-bounded entropy `h` is invariant but `+infinity` on all `L(F_r)`, so it cannot separate;
    - the HJKE structure theorems are uniform in `t > 1`, so they cannot separate;
    - `delta_0` separates only if generator-independent, which is the classical open step, known only in the strongly 1-bounded regime (Jung).
  - Surface group factors are free group factors, so invariants must agree across them.
- **Elementary equivalence.**
  - The Goldbring–Pi trichotomy.
  - The transfer from Sela is unavailable, because Arulseelan was withdrawn.
  - New elementary theorem: two log-independent equivalences force case 1; `L(F_2) ≡ L(F_3)` plus `L(F_2) ≡ L(F_4)` suffices.

## Exact gap

Either:

- a `t`-dependent generator-independent invariant;
- one explicit isomorphism;
- one non-equivalence or equivalence of first-order theories, e.g. decide `L(F_2) ≡ L(F_3)`.

Sources (web):

- https://arxiv.org/abs/funct-an/9211012
- https://arxiv.org/abs/2305.08168
- https://arxiv.org/abs/2308.14109
- https://arxiv.org/abs/2609.11074
- https://arxiv.org/abs/2412.20346
