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
