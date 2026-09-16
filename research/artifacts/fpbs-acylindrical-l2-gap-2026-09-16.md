# Critical l2 gap and pivotal kernels on acylindrically hyperbolic Cayley graphs

Swarm note for `fpbs-pivotal-budget-universal`, 2026-09-16.

## 0. Summary

Let `G` be an acylindrically hyperbolic group, let `S` be a finite generating
set of `G`, and let `Gamma = Cay(G,S)`.

* **Theorem A.** `p_c(Gamma) < p_(2->2)(Gamma)`.
* **Corollary B.** `Gamma` satisfies all four pivotal kernels of
  `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`, and PB
  holds with a count bounded independently of `n`.

Theorem A is not stated as a theorem in either source. It is a short deduction
from two imported theorems:

* Choi–Seo, arXiv:2508.08932v2, prove Hutchcroft's two sufficient estimates
  `(Gamma1)` and `(Gamma2)` on every such `Gamma`.
* Hutchcroft, arXiv:1804.10191, Proposition `prop:criterion`, turns them into
  `p_c < p_(2->2)`.

Choi–Seo's formal statements give only the weaker conclusions `p_c<p_u` and
`nabla_(p_c)<infinity`. Their introduction (line 242, quoted as CS8 below) says
in prose that the triangle condition "is derived from yet another fact, namely,
the `L^2`-boudedness". So the authors evidently regard the gap as the
underlying fact, and Theorem A should not be read as new mathematics. What
this note adds is an explicit, checked deduction of the gap. It also records
the gap in the archive, which before this note recorded only `p_c<p_u` for this
class (`fpbs-sc-choi-seo`).

This gives no new case of the Benjamini–Schramm conjecture, because Choi–Seo
already prove `p_c<p_u` here. The universal target
`fpbs-pivotal-budget-universal` stays OPEN. What changes is the largest
recorded class on which PB is proved. Before, it was the hyperbolic,
nonunimodular and free-product (union generating set) graphs. It now
includes every Cayley graph of every acylindrically hyperbolic group.

## 1. Sources and how they were read

* **[H]** Tom Hutchcroft, *Percolation on hyperbolic graphs*, arXiv:1804.10191.
  - Read from the e-print TeX source `HyperbolicPercolation6.tex`, downloaded
    on 2026-09-16.
  - Line numbers below refer to that file. They agree with the lines quoted
    in `research/fpbs-hyperbolic-nonunimodular-critical-l2-gap-citation.md`
    (`thm:pell2` label line 304).
  - The number Proposition 2.7 comes from the theorem counter
    (`\newtheorem{thm}{Theorem}[section]`, shared by prop, lemma and
    corollary). Choi–Seo cite `[Proposition 2.7]` for the same statement.
    The TeX label `prop:criterion` is the authoritative identifier.
* **[CS]** Inhyeok Choi and Donggyun Seo, *Percolation in acylindrically
  hyperbolic groups*, arXiv:2508.08932v2.
  - Submitted 2025-08-12, v2 2025-08-13. The arXiv API metadata, fetched
    2026-09-16, give 61 pages and no journal reference.
  - Read from the e-print TeX source `perc.tex`, downloaded 2026-09-16. Line
    numbers below refer to that file.
  - Refereeing status was not verified.

Markup is transcribed with light simplification. `\iota`, `\chi` and `\tau`
are written `iota`, `chi` and `tau`.

## 2. Quoted statements

### 2.1 From [H]

* **H1, the parameter** (line 288). For a connected, locally finite graph `G`,
  `T_p(u,v) = tau_p(u,v)`, and
  "`p_{q\to q} = p_{q\to q}(G) = \sup\{p\in [0,1]: \|T_p\|_{q\to q} <\infty\}`".
  The `1->1` norm is `\overline{\chi}_p := \sup_v \chi_p(v)`.
* **H2, the upper bound** (line 301). "it follows that
  `p_{q\to q}(G)\leq p_u(G)` whenever `q\in [1,\infty]` and `G` is infinite
  and quasi-transitive."
* **H3, the isoperimetric constant** (lines 504–508). "For each
  `0\leq p<p_c`, we define
  `\iota(T_p) = 1 - \sup\{ \frac{\sum_{u,v\in K} \tau_{p}(u,v)}{\overline{\chi}_{p} |K|} : K \subseteq V \text{ finite} \}`."
* **H4, `prop:criterion`** (label line 514, statement lines 515–520).
  > Let `G` be a connected, locally finite, quasi-transitive graph. Then
  > `p_c(G)<p_{2\to2}(G)` if and only if
  > `\liminf_{p\uparrow p_c} \frac{p_c-p}{1-p} \overline{\chi}_{p} \sqrt{1-\iota(T_p)^2} < \frac{1}{\|A\|_{2\to2}}`.
  > In particular, if (this) holds then `p_c(G)<p_u(G)` and
  > `\nabla_{p_c}<\infty`.

  Here `A` is the adjacency matrix. The "if" direction is proved in [H]
  (lines 542–543) from two lemmas:
  - `lem:Cheeger`, label line 529:
    `||T_p||_{2->2} <= chi-bar_p sqrt(1-iota(T_p)^2)`;
  - `cor:l2AizBar`, label line 449:
    `||T_p||_{2->2} >= (1-p)/(||A||_{2->2}(p_(2->2)-p))` for `p<p_(2->2)`.

  Together they rule out `p_(2->2)=p_c`. This short step was re-checked for
  this note.
* **H5, `prop:2to2givesqtoq`** (label line 397). If `p_c<p_(2->2)` then
  `p_c<p_(q->q)` for every `q in (1,infinity)`.
* **H6, `prop:nonuniquenessatpell2`** (label line 1721). Let `G` be connected,
  locally finite, transitive and nonamenable, and let `X` be simple random
  walk. Then "`\E[ \tau_p(X_0,X_n) ] \leq \rho(G)^{n}` for every
  `0\leq p \leq p_{2\to2}`."

### 2.2 From [CS]

* **CS0, standing setting** (lines 485–499). "Throughout, `\Gamma` will be a
  Cayley graph of a finitely generated group `G`."
  - `tau_p(g,h) = P_p(g <-> h)` and `chi_p = sum_g tau_p(id,g)`.
  - Line 496: "`\chi_{p} <+\infty` for `0 \le p < p_{c}` and
    `\lim_{p \nearrow p_{c}}\chi_{p} = +\infty`."
  - Line 499: `iota_p` is defined exactly as H3, with `chi_p` in place of
    `chi-bar_p`. The index set is printed as `K` in the numerator and `A` in
    the denominator, a typo.

  On a Cayley graph `chi_p(v)` does not depend on `v`, so `chi_p = chi-bar_p`
  and `iota_p = iota(T_p)`.
* **CS1, `thm:main`** (label line 216, statement line 217). "Let `G` be an
  acylindrically hyperbolic group and let `\Gamma` be its Cayley grpah. Then we
  have `p_{c}(\Gamma) < p_{u}(\Gamma)`; in particular, there exist uncountably
  many `p \in (0, 1)` such that `\Gamma[p]` has infinitely many infinite
  clusters."
* **CS2, `thm:mainDelta`** (label line 236). `nabla_(p_c)(Gamma) < infinity`.
* **CS3, the two estimates** (labels `eqn:hutchcroftGamma1` and
  `eqn:hutchcroftGamma2`, lines 540–542).
  - `(Gamma1)`: `\limsup_{p \nearrow p_{c}} (p_{c} - p) \chi_{p} <+\infty`.
  - `(Gamma2)`:
    `\lim_{p \nearrow p_{c}} \sup\{ \frac{\sum_{g, h \in A} \tau_{p} (g, h)}{\chi_{p} \cdot \#A} : A \subseteq G \textrm{ finite}\} =0`.
* **CS4, `thm:hutchcroft1plus2`** (label line 561, statement lines 562–566).
  > Let `\Gamma = Cay(G, S)` be the Cayley graph of a finitely generated group
  > `G`. Let `\mathscr{H} = \{H(g) : g \in G\}` be a collection of subsets of
  > `G`. Suppose that there exists `R>0` such that the following holds: For
  > each finite set `A \subseteq G` there exists `A' \subseteq A` with
  > `\#A' \ge \#A / 2` such that for each `a \in A'`, there exists
  > `g, h \in G` such that `\|g\|_{S}, \|h\|_{S} \le R`, `A \subseteq a H(g)`
  > and `H(g) \cap h H(g) = \emptyset`. Then Equation (Gamma1) holds for
  > `\Gamma`.

  [CS] prove it in Appendix A (line 2222 onward), following [H, Section 5.1].
* **CS5, the hypothesis of CS4 for acylindrically hyperbolic groups.**
  - Line 1224, `prop:supportingWPD`, is stated for "a non-virtually cyclic
    group acting on `X` with a WPD loxodromic element `f`" and for an
    arbitrary finite generating set `S`.
  - Line 1537: "Proposition `prop:supportingWPD` now follows from Proposition
    `prop:supportingWPDWeak` and Lemma `lem:pigeon`. Therefore acylindrically
    hyperbolic groups satisfy the assumption of Theorem
    `thm:hutchcroft1plus2`."
* **CS6, `thm:hutchcroftIotaGen`** (label line 655). This is an abstract
  criterion for `(Gamma2)` on `Cay(G,S)`, using roughly branching sets,
  barriers and a magic-lemma hypothesis. [CS] prove it at lines 676–692.
* **CS7, `cor:hutchcroftIotaAcyl`** (label line 2195, statement line 2196).
  "Let `\Gamma` be the Cayley graph of an acylindrically hyperbolic group `G`.
  Then Equation (Gamma2) holds." The proof begins at line 2200: "Let `S` be a
  finite generating set for `G` that gives rise to `\Gamma = Cay(G, S)`."
  It ends at line 2217 by applying CS6.
* **CS8, the l2 remark** (lines 242–243).
  - Line 242 opens: "In fact, the triangle condition `\nabla_{p_{c}}<+\infty`
    is derived from yet another fact, namely, the `L^{2}`-boudedness of an
    operator associated with the transition probability."
  - It continues: "Hence, once `p_{c} < p_{2 \rightarrow 2}` holds, then both
    the triangle condition `\nabla_{p_{c}} < +\infty` and the inequality
    `p_{c} < p_{u}` follow".
  - The display there is headed "`L^{2}`-boundedness", with a typo `p_{2}`
    for `p_c`.

  Line 245 says: "We will not explain the `L^{2}`-boundedness in detail."
  Line 522 repeats that Hutchcroft derives the triangle condition from
  `eqn:nablaPre` "by means of the so-called `L^{2}` boundedness".
  [CS] never state `p_c<p_(2->2)` as a theorem. Their `thm:hutchcroft`
  (label line 505) cites [H, Proposition 2.7] only in a weakened form: if the
  liminf `= 0` then `p_c<p_u` and `nabla_(p_c)<infinity`.
* **CS9, their definition** (`dfn:proper`, lines 915–926, sentence at line
  925). "If `G` has WPD action on a Gromov hyperbolic space and is not
  virtually cyclic, then we call it an acylindrically hyperbolic group."
  - Line 870 lets them replace the metric by a `G`-equivariantly
    quasi-isometric one in which a chosen loxodromic element is unital and
    axial.
  - Section 7 opens at line 1716 with "Let `G` be an acylindrical hyperbolic
    group with a finite generating set `S`" and fixes such an action.
* **CS10, the product question** (`ques:f2z`, label line 288). "Does every
  Cayley graph of `F_{2} \times \Z` have a nonuniqueness phase?" Line 286
  says: "Theorem `thm:main` deals with no products."

## 3. Theorem A: the deduction

**Theorem A.** Let `G` be an acylindrically hyperbolic group and `S` a finite
symmetric generating set of `G` with `e` not in `S`. Put `Gamma = Cay(G,S)`.
Then `p_c(Gamma) < p_(2->2)(Gamma)`. Consequently:

* `p_c(Gamma) < p_(q->q)(Gamma)` for every `q in (1,infinity)`, by H5;
* there is `p > p_c(Gamma)` with `E[tau_p(X_0,X_n)] <= rho(Gamma)^n` for all
  `n`, by H6.

*Proof.*

**Step 0 (setting).** `Gamma` is connected because `S` generates. It is
`|S|`-regular, and left multiplication makes it transitive, so H4 applies.
The adjacency operator satisfies `||A||_(2->2) <= ||A||_(1->1) = |S|`, so the
right-hand side `1/||A||_(2->2)` of H4 is positive. On a Cayley graph
`chi_p(v)` does not depend on `v`, so `chi-bar_p = chi_p`. Hence the
quantity `iota_p` of [CS] equals `iota(T_p)` of H3. Also
`p_c >= 1/(|S|-1) > 0`, the standard branching bound for bounded degree.

**Step 1 (`p_c<1`).** By CS1, `p_c(Gamma) < p_u(Gamma) <= 1`.

**Step 2 (Gamma1).** By CS5 the pair `(G,S)` satisfies the hypothesis of CS4,
so CS4 gives

    M := limsup_(p -> p_c-) (p_c - p) chi_p < infinity.

Fix `p_1 in (0,p_c)` with `(p_c-p) chi_p <= M+1` for every `p in (p_1,p_c)`.

**Step 3 (Gamma2).** For `0 <= p < p_c` put

    s(p) := sup{ sum_(g,h in K) tau_p(g,h) / (chi_p |K|) : K subset G finite },

so `s(p) = 1 - iota(T_p)`. Two bounds:

* `K = {e}` gives `s(p) >= 1/chi_p > 0`.
* `sum_(h in K) tau_p(g,h) <= chi_p` for each `g` gives `s(p) <= 1`.

So `iota(T_p) in [0,1)`, and

    1 - iota(T_p)^2 = s(p)(2 - s(p)) <= 2 s(p).

By CS7, `s(p) -> 0` as `p -> p_c-`.

**Step 4 (criterion).** Let `p in (p_1,p_c)`. Then `1-p >= 1-p_c > 0` by Step 1,
so

    (p_c-p)/(1-p) * chi-bar_p * sqrt(1 - iota(T_p)^2)
        <= (M+1)/(1-p_c) * sqrt(2 s(p))  ->  0      as p -> p_c-.

The limit inferior in H4 is therefore `0 < 1/||A||_(2->2)`, and H4 gives
`p_c(Gamma) < p_(2->2)(Gamma)`. QED.

**Check of the direction of H4 that is used.** Take `p<p_c` at which
`((p_c-p)/(1-p)) chi-bar_p sqrt(1-iota(T_p)^2) < 1/||A||_(2->2)`.

* `lem:Cheeger` gives `||T_p||_(2->2) <= chi-bar_p sqrt(1-iota(T_p)^2)`.
  This is Cheeger's inequality for the symmetric substochastic matrix
  `T_p/chi-bar_p`, whose Cheeger constant is `iota(T_p)`.
  - [H] state the lemma for `0<p<p_(1->1)(G)`, where `p_(1->1)` is H1 with
    `q=1`.
  - The liminf hypothesis gives such `p` arbitrarily close to `p_c`, so we
    may take `p>0`.
  - `chi-bar_(p') < infinity` for every `p' in (p,p_c)` (CS0, line 496), so
    `p<p_(1->1)`.

  So the lemma applies.
* Suppose `p_(2->2) = p_c`. Then `cor:l2AizBar` at this `p` gives
  `||T_p||_(2->2) >= (1-p)/(||A||_(2->2)(p_c-p))`.

The two displays contradict each other. Since `p_c <= p_(2->2)` always
([H], line 299), `p_c < p_(2->2)`.

**Remark A.1 (Gamma1 and Gamma2 are exactly the gap).** The "only if"
direction of H4 is also proved in [H], at line 543. On a Cayley graph it shows
that `p_c<p_(2->2)` gives back both (Gamma1) and (Gamma2). So on Cayley graphs

    (Gamma1) and (Gamma2)   <=>   p_c < p_(2->2).

The Choi–Seo estimates are thus exactly the strict l2 gap. Recording the gap
loses no information, and it is the form that the pivotal kernel bound of
`fpbs-l2-gap-gives-bounded-pivotal-counts` consumes.

**Remark A.2 (no explicit gap).** `cor:l2AizBar` gives
`p_(2->2) - p >= (1-p)/(||A||_(2->2) ||T_p||_(2->2))` for `p<p_(2->2)`. [CS]
give no rate in (Gamma2) and no explicit `M`, so Theorem A gives no explicit
lower bound on `p_(2->2)-p_c`. By contrast,
`fpbs-free-product-cayley-graphs-have-critical-l2-gap` gives an explicit
bound for free products on union generating sets.

## 4. Corollary B: the pivotal kernels

**Corollary B.** Let `G`, `S` and `Gamma` be as in Theorem A, and use the
setup of Section 1 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`. Fix
`p0 in (p_c(Gamma), p_(2->2)(Gamma))` and put
`C_0 = 2|S| ||T_(p0)||_(2->2)^2 < infinity`. Then, for both walks, every
`n>=1`, every `R>=n` and every `p <= p0`,

    E_p[N_(n,R) | E_(n,R)] <= C_0.

So on `Gamma`:

* `fpbs-pivotal-budget-universal` holds with `C = C_0` and a count bounded
  independently of `n`;
* `fpbs-integrated-sensitivity-universal` holds;
* `fpbs-pivotal-nonconcentration-universal` holds with `B(epsilon) = 0` for
  `epsilon <= p0 - p_c`;
* `fpbs-universal-subcritical-pivotal-growth-rate` holds.

*Proof.*

1. By `fpbs-osin-ah-groups-not-products-not-torsion` (Osin, arXiv:1304.1246),
   `G` contains a non-abelian free subgroup. So `G` is nonamenable, and so is
   every Cayley graph of `G` on a finite generating set.
2. By Theorem A, `p_c(Gamma) < p_(2->2)(Gamma)`.
3. `Gamma` is therefore a nonamenable Cayley graph with a critical l2 gap.
   `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels` (Corollary 4.2 of the
   kernel note) gives every conclusion as stated, with its constant
   `C_0 = 2d||T_(p0)||^2` and `d = |S|`. QED.

## 5. Scope and limits

### 5.1 Conventions

`Cay(G,S)` means the simple graph on `G` with an edge `{g,gs}` for each
`s in S union S^(-1)` with `s != e`. This is the convention of [CS] (line 204,
edges indexed by `S union S^(-1)`; line 357, simplicial graphs). Replacing `S`
by `(S union S^(-1)) \ {e}` does not change the graph. So Theorem A and
Corollary B hold for every finite generating set, with `d = |S|` read as the
degree `|(S union S^(-1)) \ {e}|`.

### 5.2 What is covered

Every Cayley graph, on every finite generating set, of every acylindrically
hyperbolic group. [CS] list examples at lines 220–228. They are quoted here and
were not re-verified. Each item carries the usual non-elementarity conditions,
which [CS] leave implicit.

* non-elementary relatively hyperbolic groups;
* non-elementary Kleinian groups;
* free products of nontrivial groups, excluding `Z/2 * Z/2`, which is
  virtually cyclic;
* mapping class groups of finite-type hyperbolic surfaces;
* `Out(F_n)`;
* `Aut` of a hyperbolic group;
* rank-one CAT(0) groups;
* many Artin groups and 3-manifold groups.

Before this note the archive recorded PB, via `p_c<p_(2->2)`, only in these
cases:

* quasi-transitive nonamenable Gromov hyperbolic graphs;
* graphs with a quasi-transitive nonunimodular automorphism subgroup;
* free products on union generating sets.

Some Cayley graphs covered now are in none of these classes. For example,
take a finite-type surface mapping class group containing `Z^2`, with any
generating set. Such a graph is not Gromov hyperbolic, and it is not a free
product on a union generating set. No archive node gives it the nonunimodular
hypothesis.

A second example is a free product `A * B` on a generating set that is not a
union of generating sets of the factors. Here
`fpbs-free-product-cayley-graphs-have-critical-l2-gap` does not apply, while
Theorem A does, whenever the product is not `Z/2 * Z/2`. (Referee note: this
is new only when some factor is not hyperbolic, for example `Z^2 * Z`. If both
factors are hyperbolic, `A * B` is hyperbolic and `fpbs-hyperbolic-nonunimodular-critical-l2-gap`
already covers every generating set.)

### 5.3 What is not covered

* **Products.** By `fpbs-osin-ah-groups-not-products-not-torsion`, a product
  of two infinite groups is not acylindrically hyperbolic. So Theorem A says
  nothing about `F_2 x Z` or `F_2 x F_2`.
  - For `F_2 x Z`, [CS] ask (`ques:f2z`) whether every Cayley graph even has
    `p_c<p_u`.
  - The product generating set of `F_2 x Z` gives `T_4 x Z`, which the
    nonunimodular theorem already covers. Arbitrary generating sets stay open.
* **Infinite amenable wq-normal subgroups.**
  `fpbs-amenable-splittings-are-ah-or-amenable-wq-normal` shows the following.
  A nonamenable group that splits over an amenable subgroup is either
  acylindrically hyperbolic, in which case Theorem A covers it, or has that
  subgroup as an infinite amenable wq-normal subgroup. Theorem A says nothing
  in the second case.
* **The universal target.** `fpbs-pivotal-budget-universal` asks for PB on
  every nonamenable Cayley graph. It stays OPEN.
  - Theorem A and Corollary B add a class, not an argument that reaches
    non-AH groups.
  - PB on every nonamenable Cayley graph would in particular need an answer
    for all Cayley graphs of `F_2 x Z`. For that group even `p_c<p_u` on
    every generating set is open (`ques:f2z`).
* **No new BS case.** Every graph covered here already has `p_c<p_u` by [CS].

## 6. Weakest steps

The steps are ordered by how much a referee should worry.

1. **(Gamma2) for acylindrically hyperbolic groups, CS7.**
   - This is the new part of [CS]: Sections 4–7, the magic lemma, supporting
     hyperplanes, branching sets and barriers.
   - It is a 61-page preprint with no journal reference in the arXiv metadata.
     Its refereeing status was not verified. None of Sections 4–7 was re-checked
     here.
   - If CS7 fails, the proof of Theorem A fails. So does [CS]'s own proof of
     `p_c<p_u`, which goes through the same criterion. The trust base is
     therefore the same as that of `fpbs-sc-choi-seo`.
2. **(Gamma1), CS4 and CS5.**
   - Appendix A of [CS] adapts [H, Section 5.1].
   - Line 1537 closes the verification of its hypothesis for acylindrically
     hyperbolic groups.
   - Neither was re-checked here.
3. **Definitions at the interface.**
   - [CS] define acylindrically hyperbolic groups as non-virtually-cyclic groups
     with a WPD action on a hyperbolic space (CS9). They then pass to a
     `G`-equivariantly quasi-isometric metric in which a loxodromic is unital
     and axial, citing Bestvina–Fujiwara [Proposition 6.(2)] at line 870.
   - That this agrees with Osin's definition is Osin's Theorem 1.2 in
     arXiv:1304.1246. This is from memory; that theorem was not re-fetched in
     this session. (Referee, 2026-09-16: the arXiv abstract of 1304.1246,
     fetched that day, says that the class of acylindrically hyperbolic groups
     "coincides with ... the class of groups admitting a non-elementary weakly
     properly discontinuous action on a hyperbolic space". The theorem number
     was still not checked.)
   - Some statements write `G <= Isom(X)`, for example line 1546, which
     presumes a faithful action. The action of `G` on a Cayley graph
     `Cay(G,X)` with respect to a possibly infinite generating set is by left
     multiplication, so it is faithful. Osin's Theorem 1.2 supplies such a
     hyperbolic, acylindrical action. This is also from memory and unverified
     here.
4. **Matching of the two sources' quantities**, Step 0.
   - `iota_p` of [CS] is `iota(T_p)` of [H], because `chi_p = chi-bar_p` on a
     Cayley graph. [CS] line 499 has a typo in the index set (`K` versus
     `A`).
   - `||A||_(2->2)` is finite and positive.
   - `p_c<1` comes from CS1. Only `1-p_c>0` is used, to bound
     `(p_c-p)/(1-p)`.
5. **The deduction itself**, Steps 2–4 and the check of H4.
   - It uses only the elementary inequality `1-iota^2 <= 2(1-iota)` for
     `iota in [0,1]`, together with the two quoted lemmas of [H]. Both lemmas
     were read in the TeX source (label lines 449 and 529; proof of
     `prop:criterion` at lines 542–543).
   - I regard this step as secure.
6. **Corollary B.**
   - It uses Theorem 4.1 and Corollary 4.2 of the kernel note, recorded as
     `fpbs-l2-gap-gives-bounded-pivotal-counts` and
     `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`. These were read but
     not re-proved in this session.
   - Nonamenability comes from Osin's free-subgroup corollary via
     `fpbs-osin-ah-groups-not-products-not-torsion`.
7. **Numbering.** "Proposition 2.7" of [H] was derived from the theorem counter,
   and [CS] cite the same number. Labels are used as identifiers throughout.

## 7. Cairn nodes

* `fpbs-acylindrically-hyperbolic-critical-l2-gap` (claim): Theorem A.
* `fpbs-acylindrically-hyperbolic-critical-l2-gap-citation` (route,
  `requires: []`). It gives precise imports of CS1, CS4 with CS5, CS7 and H4,
  and the complete deduction of Section 3.
* `fpbs-acylindrically-hyperbolic-pivotal-kernels` (claim): Corollary B.
* `fpbs-acylindrically-hyperbolic-pivotal-kernels-proof` (route). It requires:
  - `fpbs-acylindrically-hyperbolic-critical-l2-gap`;
  - `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`;
  - `fpbs-osin-ah-groups-not-products-not-torsion`.

Nodes deliberately not created:

* **The converse `(Gamma1) and (Gamma2) <=> p_c<p_(2->2)` on Cayley graphs**
  (Remark A.1). It is a restatement of H4, and nothing in the archive needs
  it.
* **The consequence `E[tau_p(X_0,X_n)] <= rho^n` for some `p>p_c`.** It is
  H6 applied to Theorem A. The kernel note already records the same
  consequence for its class `C_2`, in the remark after Corollary 4.2 and in
  Lemma 2.3.
* **Any claim that PB implies `p_c<p_(2->2)`.** No argument was found; see the
  swarm note `notes/fpbs-pivotal-budget-universal-swarm-2026-09-16.md`.
