# hl-nh-local-colimit: curvature certificates for phase-surviving local colimits (2026-09-13)

Lane target: `tracial-nonru-bcs-has-phase-surviving-local-colimit`.
Sources fetched as arXiv TeX on MSI under
`/scratch.global/sauer354/hl-nh-local-colimit/src/`. Line numbers are source lines.

## 1. Pins

### Petrosyan--Prytula, arXiv:1712.07606 (`a1712.07606/`)

- **l.307:** "Given a simple complex of groups $G(\mathcal{Q}$) one defines its
  \emph{fundamental group} $\widehat{G(\mathcal{Q})}$ as the direct limit
  [...] A simple complex of groups $G(\mathcal{Q})$ is called
  \emph{strictly developable} if every $i_J$ is injective."
- **l.218:** "[...] such that whenever $J<T$, then there is an injective,
  non-surjective homomorphism $P_J \to P_T$. The \emph{fundamental group} of
  $G(\mathcal Q)$ is defined as the direct limit of the system
  $\{P_J\}_{J \in \mathcal Q}$."
- **l.1057:** "The crucial theorem \cite[Theorem~II.12.28]{BH} states that a
  non-positively curved simple complex of finite groups $G(\mathcal Q)$ is
  strictly developable and that the standard development
  $D(\D, G(\mathcal{Q}))$ admits a $\mathrm{CAT}(0)$ metric such that $G$ acts
  by isometries."

### Prytula, *Graphical complexes of groups*, arXiv:2004.08187 (`a2004.08187/graph_groups3.0.tex`)

- **Definition 4.? (l.243--255):** local groups non-trivial finite, every
  $\psi_{vw}$ a proper inclusion, "if $v_1 \leq w$ and $v_2 \leq w$ then
  $\psi_{v_1w}(G_{v_1}) \cap \psi_{v_2w}(G_{v_2})= \{e\}$", and the cone vertex
  carries the trivial group.
- **Theorem (l.328--330):** "Let $G(\mQ)$ be a $k$--huge graphical complex of
  groups, where $k \geq 6$. Then $C(\abs{\mQ})$ admits a piecewise linear metric
  such that $G(\mQ)$ is non-positively curved. Consequently, $G(\mQ)$ is
  strictly developable [...]"
- **k-huge (l.315):** girth of $|\mQ|$ at least $2k$.
- **Metric (l.346--352):** angle $\pi/2$ at small vertices, $\pi/3$ at big
  vertices, $\pi/6$ at the cone vertex.
- **Link condition (l.364--366):** "locally $\mathrm{CAT}(0)$ if for every
  vertex $v \in X$ the link $X_v$ has girth at least $2\pi$ with respect to the
  angular metric."
- **Proof (l.371--383):**
  - cone link $\cong |\mQ|$, so girth $\ge 12 \cdot \pi/6$;
  - small-vertex link $|Q_{>v}| \ast \{g\cdot c\}$, whose 4-cycles have length $2\pi$;
  - big-vertex link $D(G_w, |Q_{<w}|)$ has even cycles, and a putative 4-cycle
    forces $g_1^{-1}g_2 \in G_{v_1} \cap G_{v_2}$, contradicting the definition;
  - "This shows that $G(\mQ)$ is non-positively curved and thus it is strictly
    developable."
  - The remark at l.257--259 records the reversed order convention relative to
    Bridson--Haefliger.

### Slofstra--Zhang, arXiv:2412.10305v2 (`sz/small.tex`, l.119--128)

"Let $H(A)$ be the hypergraph with vertex set $[m]$, edge set $[n]$, and vertex
$i$ incident to edge $j$ if $A_{ij} \neq 0$. If $H(A)$ has minimum vertex degree
$\geq d$ and girth $\geq g$, where $(d,g) \in \{(4,4),(3,6)\}$, then $|J| = p$
in $\Gamma_p(A,b)$ for all $b$." Berge cycles alternate distinct vertices and
distinct edges.

### Bridson--Haefliger

Not read. Springer chapter `10.1007/978-3-662-12494-9_20` (*Simple Complexes of
Groups*) returned an HTML access page from MSI.

## 2. Results landed

1. `commuting-nonscalar-readouts-force-coset-four-cycles` (elementary):
   - (CN1): commuting nonscalar readouts with `H cap K = J` give `m(H,K) = 2`;
   - (CN2): functionally dependent readouts give `H cap K > J`.
2. `barycentric-curvature-certificates-need-incidence-girth-eight` (elementary):
   - (CB1): `2 + sum 1/m_i <= k` along incidence cycles;
   - (CB2): `k >= 4 + r` for nonscalar cycles;
   - (CB3): functional subdivision can't help.
3. `nonpositively-curved-simple-complexes-are-developable`:
   citation import of BH II.12.28 via the two sources above.
4. `central-local-data-of-incidence-girth-twelve-keeps-the-phase`: (G12), (CI)
   and (PR) together make the phase survive for arbitrary finite local groups.
   The proof is Prytula's cone metric with the phase at the cone vertex.
   - Calibration: the SZ `(3,6)` case for `p = 2` is recovered.
   - Degree-2 cyclic systems violate (CI), matching the collapse of `J` there.
5. `some-nonru-bcs-has-central-local-data-of-girth-twelve` (OPEN) with route
   `nonhyperlinear-group-via-central-girth-twelve-local-data` into
   `non-hyperlinear-group`.

## 3. Exact gap

Phase survival is automatic once local data has incidence girth at least 12 and
central pairwise intersections. The target therefore comes down to a design and
girth question for non-`R^U` sources.
- **Girth.** The source's incidence girth can't be raised by functional copying (CB3).
- **Short cycles.** Any barycentric certificate needs at least four contexts
  per nonscalar cycle (CB2).
- **Test.** No such local data can exist for sources that are not tracially
  satisfiable.
- **Unknown.** Whether a non-`R^U` source with an incidence graph of girth at
  least 12 admits centrally intersecting finite readouts, including at its
  affine-unsafe contexts, which need nonabelian groups.
