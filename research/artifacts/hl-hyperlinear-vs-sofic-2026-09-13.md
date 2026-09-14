# hl-hyperlinear-vs-sofic, 2026-09-13

Lane question: is every hyperlinear group sofic (Pestov Question 3.4,
`hyperlinear-nonsofic-group` / `hyperlinear-implies-sofic`)?

## 1. Where the question stands on main

- **No established nonsofic witness is known to be hyperlinear.** Every one
  comes from the (T)-compression mechanism (Leavitt unit group, Kun--Thom
  wreaths and doubles, Fournier-Facio, the Clifford covers, the product-action
  full group). Their hyperlinearity is OPEN in every case:
  `hyperlinear-wreath-model`, `kun-thom-clifford-crossed-product-ce`,
  `kt-canonical-hs-normalization-fails`, the routes into
  `hyperlinear-nonsofic-group`.
- **Where the Kun--Thom argument is permutation-specific** is already pinned
  in `kt-centralizer-normalization-hs`. Theorem 4.1's two median arguments run
  on vertex masses and isotropy orders of the cluster groupoid. Those are
  counting invariants of an atomic partition algebra, and the relative
  commutant of a Hilbert--Schmidt model need not be atomic.
- **Both answers reduce to stability of the vertex.** Put
  `Γ = EL_r(F_q[x_1..x_d])` with `r, d >= 3`.
  - Flexible HS rounding of `Γ` at every actor-extendable model is equivalent
    to non-hyperlinearity of the Kun--Thom wreath
    (`kt-wreath-models-never-round-on-the-vertex`, corollary 1).
  - Any separation through a coset wreath or double needs a non-roundable
    actor-extendable model of `Γ`
    (`kt-hyperlinear-coset-wreath-forces-nonroundable-vertex`).
  - The weakest form, instability of `Γ` alone, is OPEN as
    `el-r-polynomial-vertex-not-flexibly-hs-stable`. It has two routes, rank-3
    covers and a congruence central extension.

## 2. What this lane settled

The rank-3 cover route needs finite quotients of the finitely presented covers
of `SL_3(F_q[t])` in which the truncation kernels survive
(`sl3-polynomial-covers-have-extra-finite-quotients`). Its recorded sufficient
condition was that the profinite completion of `SL_3(F_q[t])` is not finitely
presented.

- **`sl3-fq-t-profinite-completion-is-finitely-presented`.** For `q >= 4` and
  `r >= 3`, `SL_r(F_q[t])^ ≅ SL_r(F_q[[t]]) × SL_r(F_q[t,t^-1])^`, and both
  factors are finitely presented profinite groups. The sufficient condition is
  false.
- **`fp-cover-truncations-see-kernel-iff-profinite-closures-differ`.** A
  truncation kernel survives in a finite quotient iff `cl(N_L) ≠ cl(N)`. This
  is monotone in `L`, and fails iff the truncation already has the profinite
  completion of the limit group.
- **`clr-profinite-presentations-and-csp-over-fq-t`.** Citation import of the
  three inputs.

## 3. Verbatim pins (arXiv:1508.00526, e-print TeX `ProfinitePresentations_August28.tex`)

Capdeboscq--Lubotzky--Rémy, *Presentations: from Kac--Moody groups to
profinite and back*.

**Theorem C (TeX l.288--294, attributed to Capdeboscq):**
"There exists a constant $C>0$ such that for any simple, simply connected,
Chevalley group scheme ${\bf G}$ of rank $\geqslant 2$ and for any prime power
$q \geqslant 4$, the group $G={\bf G}(\mathbf{F}_q[t,t^{-1}])$ admits a
presentation $\Sigma(G)$ with $D_{\Sigma(G)}$ generators and $R_{\Sigma(G)}$
relations satisfying $D_{\Sigma(G)}+R_{\Sigma(G)} \leqslant C$."

**Proposition 1.2 (`prop::AL`, TeX l.307--311):**
"Assume that the rank of the simple, simply connected, Chevalley group
${\bf G}$ is $\geqslant 2$ and that the arithmetic group
${\bf G}(\mathbf{F}_q[t, t^{-1}])$ has a presentation with $d$ generators and
$r$ relations. Then for any $e \geqslant 1$, the group
${\bf G}(\mathbf{F}_{q^e}[[t]])$ has a profinite presentation with $d$
generators and $r+1$ relations."

**Theorem `th:CSP` (TeX l.348--354):**
"Let ${\bf G}$ be a simply connected Chevalley group, let $k$ be a global field
and let $S$ be a finite set of places of $k$. Let $A$ denote the ring of
$S$-integers in $k$ and for each $v \in S$, let $k_v$ be the corresponding
completion of $k$. We set
${\rm rk}_S({\bf G}) = \sum_{v \in S} {\rm rk}_{k_v}({\bf G})$ and assume that
${\rm rk}_S({\bf G}) \geqslant 2$. Then the kernel of the map
$\pi : \widehat{{\bf G}(A)} \to \overline{{\bf G}(A)}$ is cyclic; it is even
trivial whenever $S$ contains a non-Archimedean place."

**Strong approximation (proof of Prop. 1.2, TeX l.341--343):**
"Since there is no place of ${\bf F}_q(t)$ at which ${\bf G}$ is anisotropic
and since ${\bf G}$ is simply connected, strong approximation \cite{Prasad}
implies that the $S$-congruence completion $\overline{{\bf G}(A)}$ is described
by means of the $S$-ad\`eles $\mathbf{A}_S$ of ${\bf F}_q(t)$."

## 4. Sources consulted but not pinned

- Lubotzky, *Finite presentations of adelic groups, the congruence kernel and
  cohomology of finite simple groups*, Pure Appl. Math. Q. 1 (2005) 241--256.
  CLR describe Proposition 1.2 as "a quantitative version of a method already
  used in" it. I did not read it.
- Krstić--McCool, *Presenting GL_n(k<T>)*, J. Pure Appl. Algebra 141 (1999),
  DOI 10.1016/S0022-4049(98)00022-X. The MSI download returned an HTML page,
  not the PDF. Bux--Wortman (arXiv:math/0412101, p. 841) record: "In [6],
  Krstić–McCool showed that SL3(J[t]) is not finitely presented for any integral
  domain J." Their witnesses were not read.

## 5. Exact gap

- **For the separation:** a non-roundable actor-extendable asymptotic
  representation of `EL_r(F_q[x_1..x_d])`. None is known for any infinite
  higher-rank Kazhdan group.
- **For the vertex alone, rank-3 route:** a finitely presented Kazhdan cover
  of `SL_3(F_q[t])` none of whose truncations has the profinite completion
  `SL_3(F_q[[t]]) × SL_3(F_q[t,t^-1])^`. It must be certified from the
  specific truncation kernels, e.g. sector colimits or the Krstić--McCool
  witnesses, since the completion itself is finitely presented.

## 6. Decision: does the Kun--Thom argument survive unitary approximations?

**Verdict: only on the sector where the vertex restriction is tame. Outside
it the question is equivalent to open problems, and this lane decides neither
direction.** The step-by-step status below uses established nodes on main. The
Kun--Thom proof steps are as main transcribes them in
`kt-centralizer-normalization-hs` and `kun-thom-nonsofic-wreath-citation`; the
preprint was not re-read by this lane.

| step | permutation proof | unitary (normalized HS) version |
|---|---|---|
| KT1, endgame: normalization of `C(sigma(Gamma))` by `sigma(G)` kills the wreath | Theorem A from Theorem 4.1 | **transfers.** `rigid-compression-defect-normalization-dichotomy` (ESTABLISHED) gives `DD(C) <=> NORM(C)` in every metric class, hyperlinear included. So the unitary question is exactly `NORM(hyperlinear)`, i.e. `kt-centralizer-normalization-hs`. |
| KT2, expansion from property (T) | expander components | **transfers:** spectral gap on `L^2(M) (-) L^2(M^Gamma)` for Kazhdan actions on tracial algebras. |
| KT3, exact finite-stage invariant structure | the group generated by the images of `F_Gamma` in `Sym(n)` has an exact orbit partition at every stage, multiplicative or not. Kun's decomposition refines it after deleting `o(n)` edges, and the invariant diagonal is `prod_U D(Q_n)`, a partition algebra with cell sizes. | **first failing step.** The algebra generated by the images is generically all of `M_n`, and almost-central projections need not round to the literal commutant (`hs-literal-commutant-profile-rounding-is-false`, ESTABLISHED). The HS decomposition is the recorded open input `hs-one-level-expander-block-decomposition` / `hs-expander-block-decomposition`. Its compressor-transport clause cannot hold for arbitrary Kazhdan pairs: `nonmonomial-multiplicity-obstructs-hs-compressor-transport`, witnessed by `SL_3(Z) x A_5` in dimension 3 (status not graded here). |
| KT4, medians of vertex mass and isotropy order on the cluster groupoid | integer counting invariants of finite components | **no transcription:** a diffuse commutant has no isotropy orders. The trace-median analogue is the recorded open `tracial-median-concentration`. |

On the directive's question: as main transcribes it, the permutation proof does
not rest on nonnegative matrix entries or on rank-one projections. The
permutation-specific inputs are KT3 and KT4, namely an exact orbit partition
at every finite stage and integrality of cell sizes and isotropy orders.

**Sectors where the unitary conclusion `NORM` is established per model:**
- `sigma(Gamma)''` Haagerup: `haagerup-targets-carry-no-relative-wall`;
- the discrete type I summand and the finite-dimensional isotypic part of the
  commutant: `trace-preserving-endomorphism-fixes-discrete-type-i-summand` and
  `fd-isotypic-part-of-a-kazhdan-image-carries-no-wall`. A compressor acts
  there as an automorphism, so no wall can live there;
- trace-preserving matrix-ultraproduct models whose vertex restriction flexibly
  rounds, through the four per-model claims ending in
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`, as recorded
  in the Attempts of `kt-canonical-hs-normalization-fails`.

**Where it provably fails:** every trace-preserving model extracted from a
hyperlinear coset wreath `W_K`, `N not in K`, has a non-normalized commutant
and a non-roundable vertex (`kt-hyperlinear-coset-wreath-forces-nonroundable-vertex`).

**What deciding the complement means:**
- `NORM(hyperlinear)` makes the Kun--Thom wreath non-hyperlinear (KT1), which
  answers `non-hyperlinear-group`.
- A Connes-embeddable counterexample to `NORM` is equivalent to a hyperlinear
  intermediate coset wreath, which answers Question 3.4
  (`kt-canonical-hs-normalization-fails`).
- Any witness must have a diffuse commutant summand on which a compressor acts
  as a proper trace-preserving endomorphism, and a vertex restriction that is
  not flexibly roundable. No such model is known for any infinite higher-rank
  Kazhdan group.

So no established nonsofic witness on main is known to be hyperlinear, and
none is known to be non-hyperlinear.

## 7. Checks

- Landing 4808327397 on a0d51ab02, an ancestor of origin/main; all eight
  blobs match.
- `cairn why` on a fresh MSI clone at 4808327397 (Python 3.12) shows
  `clr-profinite-presentations-and-csp-over-fq-t`,
  `sl3-fq-t-profinite-completion-is-finitely-presented` and
  `fp-cover-truncations-see-kernel-iff-profinite-closures-differ` ESTABLISHED,
  with every leaf ✓.
- The full `check` exits 4 on 7 foreign errors: the missing claim
  `a2-kernel-removal-iff-image-satisfies-pbh` and missing
  `GroupApproximation/BowenChapman/*.lean` artifacts. None names these ids.
