# Co-amenability collapse for subrelations of Kazhdan relations

Lane: a-gs-pull-5 (transplanter, operator-algebras), wave swarm-0917, 2026-09-17.

Target context: `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`, attempt "Percolation treeings", and
`research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md` line 82: "The relation-level (T)
statement is not proved here. For Kazhdan groups the Bernoulli orbit relation has property (T), and relative (T)
for equivalence relations should force co-amenable subrelations to have finite index, just as Proposition 1.1 does
for subgroups." This artifact proves the correct form of that statement. The naive form (global finite index) is
false (Section 6.1). The true form is local: finite index on a positive invariant piece, and property (T) there.
As a consequence no subrelation with the Haagerup property (treeable, Gaboriau--Lyons factor-of-iid treeings,
restrictions of Haagerup-group orbit relations) is co-amenable in a Kazhdan relation.

## 0. Setting and conventions

`R` is a countable Borel p.m.p. equivalence relation on a standard probability space `(X, mu)`. Here `nu` is the
measure `int_X (counting on [x]_R) d mu(x)` on `R`, as in AD11 Section 1.1. A relation is a groupoid with
`r(x,y) = x`, `s(x,y) = y`, `(x,y)(y,z) = (x,z)`. It is r-discrete, so AD05 Theorem 5.22 applies to it.

Feldman--Moore: `R` is the orbit relation of a countable group `Gamma = {g_1 = id, g_2, ...}` of Borel automorphisms
of `X`. Since `R` is p.m.p., every `g_k` preserves `mu`. Fix such an enumeration for every relation used below.

For a Borel subrelation `S <= R` and `x in X`, write `[x]_R / S` for the countable set of `S`-classes contained in
`[x]_R`. Label them by first appearance: `c_1(x) = [x]_S`, and `c_i(x)` is the `i`-th distinct class in the sequence
`[g_1 x]_S, [g_2 x]_S, ...`. If `a_i(x)` is the index of first appearance, then `c_i(x) = c_j(y)` iff
`(g_(a_i(x)) x, g_(a_j(y)) y) in S`. This condition is Borel in `(x, y, i, j)`.

## 1. Imported statements (verbatim)

C. Anantharaman-Delaroche, "Cohomology of property T groupoids and applications", Ergodic Theory Dynam. Systems
25(4) (2005) 977--1013, arXiv:math/0308158v1 (AD05). Read on 2026-09-17 from arxiv.org/html, extracted to text.

- Definition 3.2: "A representation of a measured groupoid $(G,C)$ is a pair $(G^{(0)}*\mathcal{H},L)$ where
  $G^{(0)}*\mathcal{H}$ is a Hilbert bundle over $G^{(0)}$, and $L:G\rightarrow\hbox{Iso}(G^{(0)}*\mathcal{H})$ is a
  Borel map such that there exists an inessential reduction $G|_{U}$ for which the restriction of $L$ to $G|_{U}$ is
  a representation of the Borel groupoid $G|_{U}$."
- "Given a section $\xi$ of $\mathcal{H}$, the coboundary $\gamma\mapsto\xi\circ r(\gamma)-L(\gamma)\xi\circ
  s(\gamma)$ will often be denoted by $c_{L}(\xi)$."
- $S_1$: "the space of all its Borel sections $\xi$ such that $\|\xi(x)\|=1$ almost everywhere ... called unit
  sections".
- "Lemma 4.1. Let $(G^{(0)}*\mathcal{H},L)$ be a representation of $(G,C)$ and let $\nu$ be a probability measure in
  the class $C$. The following conditions are equivalent: (i) for every $\varepsilon>0$, there exists $\xi\in S_{1}$
  such that $\nu(\|c_{L}(\xi)\|\geq\varepsilon)\leq\varepsilon;$ (ii) there exists a sequence of elements
  $\xi_{n}\in S_{1}$ such that $\lim c_{L}(\xi_{n})=0$ $C$-a.e.; ..."
- "Definition 4.2. (1) A section $\xi$ ... is said to be invariant with respect to $L$ if $\xi\circ
  r(\gamma)=L(\gamma)\xi\circ s(\gamma)$ a.e. (2) If there is an invariant section $\xi\in S_{1}$ ... we say that the
  representation $L$ contains a unit invariant section ... (3) We say that $L$ almost contains unit invariant
  sections if the equivalent conditions of Lemma 4.1 are fulfilled."
- "Definition 4.3. We say that the measured groupoid $(G,C)$ has property $T$, or is a Kazhdan groupoid, if every
  representation of $(G,C)$ which almost has unit invariant sections actually has unit invariant sections."
- "For discrete measured equivalence relations, Definition 4.3 is the definition introduced by Zimmer in [38]".
- "Definition 5.19. A real conditionally negative definite function on a Borel groupoid $G$ is a Borel function
  $\psi:G\rightarrow\mathbb{R}$ such that we have (i) $\psi(x)=0$ for every $x\in G^{(0)}$; (ii)
  $\psi(\gamma)=\psi(\gamma^{-1})$ for every $\gamma\in G$; (iii) for every $x\in G^{(0)}$, every integer $n\geq 2$,
  every $\gamma_{1},\dots,\gamma_{n}\in G^{x}$ and every real numbers $\lambda_{1},\dots,\lambda_{n}$ with
  $\sum_{i=1}^{n}\lambda_{i}=0$, then $\sum_{i=1}^{n}\sum_{j=1}^{n}\lambda_{i}\lambda_{j}\psi(\gamma_{i}^{-1}\gamma_{j})
  \leq 0.$ A real conditionally negative definite function on a measured groupoid $(G,C)$ is a Borel function
  $\psi:G\rightarrow\mathbb{R}$ such that the restriction of $\psi$ to some inessential reduction satisfies the above
  three conditions. Note that $\psi$ must be a non-negative function."
- "Theorem 5.18. Let $(G,\mu)$ be a $r$-discrete ergodic Kazhdan groupoid. Then the associated discrete measured
  equivalence relation $(R,\mu)$ also has property $T$."
- "Theorem 5.22. Let $(G,C)$ be an ergodic $r$-discrete measured groupoid. The following conditions are equivalent:
  (i) $(G,C)$ has property $T$. (ii) For every real conditionally negative definite function $\psi$, there exists a
  Borel subset $E\subset G^{(0)}$ of positive measure, such that the restriction of $\psi$ to $G|_{E}$ is bounded.
  (iii) ..."

C. Anantharaman-Delaroche, "Old and new about treeability and the Haagerup property for measured groupoids",
arXiv:1105.5961 (AD11). Read on 2026-09-17 from ar5iv, extracted to text.

- "A reduction $(G_{|_{U}},\mu_{|_{U}})$ such that $U$ is conull in $X$ is called inessential."
- "Theorem 6.5. The groupoid $(G,\mu)$ has the Haagerup property if and only if there exists a conditionally negative
  definite function $\psi$ on $(G,\mu)$ such that $\forall c>0,\ \nu(\{\psi\leq c\})<\infty$."
- "Theorem 8.4 (Ueda). Let $(G,\mu)$ be a countable measured groupoid which is treeable. Then $(G,\mu)$ has the
  Haagerup property."
- "Theorem 9.2. Let $(G,\mu)$ be an ergodic countable measured groupoid. We assume that $(G^{(0)},\mu)$ is a diffuse
  standard probability space. Then $(G,\mu)$ cannot have simultaneously properties (T) and (H)."
- "Corollary 9.4. Let $\Gamma\curvearrowright(X,\mu)$ be an ergodic probability measure preserving action of a
  countable group $\Gamma$ having property (T). Then $({\mathcal{R}}_{\Gamma},\mu)$ has not property (H) and in
  particular is not treeable." Proof, verbatim: "Indeed under the assumptions of the corollary, the semi-direct
  product groupoid $(X\rtimes\Gamma,\mu)$ has property (T) by [39, prop. 2.4], and we apply the previous theorem."
- Section 10.4: "If $(G,\mu)$ is an ergodic countable groupoid having property (T), then $({\mathcal{R}}_{G},\mu)$
  too has property (T) (see [7, thm. 5.18])."

Nothing else is imported. In particular Jackson--Kechris--Louveau finite-index permanence and the
Feldman--Sutherland--Zimmer choice lemma are not used. The choice lemma needed is proved in Section 4.

## 2. Co-amenable subrelations: definition

**The quotient representation.** Let `S <= R`. The field `H(x) = l^2([x]_R / S)` has fundamental sequence
`x -> delta_(c_i(x))`, defined for `i <= n(x) = |[x]_R / S|`, where `n` is Borel. For `(x,y) in R` the sets
`[x]_R / S` and `[y]_R / S` coincide, so let `lambda_(R/S)(x,y) = identity`. The matrix coefficients
`<lambda(x,y) delta_(c_j(y)), delta_(c_i(x))> = 1[c_i(x) = c_j(y)]` are Borel. So `lambda_(R/S)` is a strict
representation of the Borel groupoid `R` (AD05 Def 3.1--3.2), real or complex.

**Definition (co-amenable subrelation).** `S` is *co-amenable in* `R` if `lambda_(R/S)` almost contains unit
invariant sections (AD05 Def 4.2(3)). By AD05 Lemma 4.1(ii), this means there are Borel unit sections
`xi_n(x) in l^2([x]_R/S)` with `||xi_n(x) - xi_n(y)|| -> 0` for `nu`-a.e. `(x,y) in R`.

**Følner form implies it.** Suppose there are Borel choices of finite nonempty `F_n(x) <= [x]_R / S` with
`|F_n(x) Δ F_n(y)| / |F_n(x)| -> 0` for `nu`-a.e. `(x,y)`. Put `xi_n = 1_(F_n) / sqrt|F_n|`. Then
`||xi_n(x) - xi_n(y)||^2 = 2 - 2|F_n(x) ∩ F_n(y)| / sqrt(|F_n(x)||F_n(y)|) -> 0`. The same holds for a Reiter form
(approximately invariant unit vectors in `l^1`), via `xi = sqrt(f)` and `||sqrt f - sqrt g||_2^2 <= ||f - g||_1`.

This is the relation analogue of the Hilbert characterization of co-amenability for subgroups. For `S = R_H`
coming from a free action of `G` restricted to `H`, `l^2([x]_R/S) = l^2(G/H)` for every `x`. Then `lambda_(R/S)` is
the constant representation `l^2(G/H)`, and co-amenability of `S` is exactly almost invariance of vectors in
`l^2(G/H)`. **Not proved here:** whether an `R`-invariant Borel field of means on `l^infty([x]_R/S)` implies this
Hilbert form (the measurable Day--Namioka step). Statements below are for the Hilbert form, which is what Følner or
Reiter-type transfer data produce.

## 3. Theorem A: local finite index

**Theorem A.** Let `R` be ergodic, p.m.p., with property (T), and let `S <= R` be co-amenable. Then there is an
`S`-invariant Borel `A <= X` with `mu(A) > 0` and an integer `1 <= k < infty` such that:
1. `S|_A` is ergodic;
2. for a.e. `x in A`, the class `[x]_R ∩ A` of `R|_A` is the union of exactly `k` classes of `S`, all contained in
   `A`.

*Proof.*

**Step 1 (invariant section).** By Def 4.3, `lambda_(R/S)` has an invariant unit section `xi`. The set of
`(x,y) in R` with `xi(x) != xi(y)` is `nu`-null. So its `r`-projection is `mu`-null, and so is the saturation of that
projection, because `R` is countable and p.m.p. Hence there is a conull `R`-invariant Borel `X_0` on which `xi` is
constant along `R`-classes and `||xi(x)|| = 1`.

**Step 2 (the maximizing set).** On `X_0` let `M(x) = sup_i |xi(x)(c_i(x))|`. This is Borel and positive, and the
supremum is attained because `xi(x) in l^2`. Let `P(x)` be the set of classes where it is attained. Then `P(x)` is
finite with `|P(x)| <= 1/M(x)^2`. `P` is constant along classes in `X_0`. So `m(x) = |P(x)|` is a Borel `R`-invariant
integer, hence equal to a constant `m` on a conull invariant `X_1 <= X_0`, by ergodicity.

Put `Y = {x in X_1 : [x]_S in P(x)} = {x in X_1 : |xi(x)(c_1(x))| = M(x)}`. It is Borel, and `S`-invariant because
`(x,y) in S` gives `[x]_S = [y]_S` and `P(x) = P(y)`. Every class in `X_1` meets `Y`, since any point of a maximizing
class lies in `Y`. So the saturation of `Y` is `X_1`, and `mu(Y) > 0`. For `x in Y`, `[x]_R ∩ Y` is the union of the
`m` classes in `P(x)`.

**Step 3 (ergodic piece).** Let `T = R|_Y`. Then `T` is ergodic: a `T`-invariant set `B` has `R`-saturation `B'`
with `B' ∩ Y = B`, and `B'` is null or conull. `S|_Y` has classes equal to `S`-classes, `m` per `T`-class.

For an `S`-invariant Borel `B <= Y` let `k_B(x)` be the number of `S`-classes inside `B` among the `m` classes of
`[x]_T`. This is Borel (test the first-appearance representative) and `T`-invariant, hence a constant `k_B`. If
`mu(B) > 0` then `k_B >= 1`. Choose `A` with `mu(A) > 0` and `k_A` minimal, and put `k = k_A`.

If `B <= A` is `S`-invariant with `0 < mu(B) < mu(A)`, then `k_B + k_(A \ B) = k_A` with both terms at least `1`,
contradicting minimality. So `S|_A` is ergodic. For `x in A`, the class `[x]_R ∩ A` is the union of the `k` classes
of `S` counted by `k_A`. QED

## 4. Lemmas on reductions, choice functions and induced functions

**Lemma R (reductions keep (T)).** If `R` is ergodic p.m.p. with (T) and `mu(Y) > 0`, then `R|_Y` has (T).

*Proof.* `R|_Y` is ergodic (Step 3 above). We verify AD05 Theorem 5.22(ii) for it.

**Extending the function.** Let `psi_Y` be a real cnd function on `R|_Y`. After an inessential reduction it
satisfies Def 5.19 everywhere on `R|_(Y')` with `Y' <= Y` conull. Rename `Y'` as `Y`; the conclusion is unchanged.

`X_0 = [Y]_R` is conull and invariant. Let `k(x) = min{k : g_k x in Y}` and `p(x) = g_(k(x)) x`, both Borel on
`X_0`. Define `psi(x,y) = psi_Y(p x, p y)` on `R|_(X_0)`, and `psi = 0` on `R|_(X \ X_0)`. Since `X_0` is invariant,
`R` is the disjoint union of these two pieces.

**psi is cnd.** `psi(x,x) = 0` and `psi` is symmetric. Take points `y_1..y_n` in a class inside `X_0` (with arrows
`gamma_i = (x, y_i)`, `gamma_i^-1 gamma_j = (y_i, y_j)`) and `sum lambda_i = 0`. Group indices by the value
`z = p(y_i)` and put `mu_z = sum_(p y_i = z) lambda_i`. Then `sum mu_z = 0`. Since `psi_Y(z,z) = 0`,
`sum_(i,j) lambda_i lambda_j psi(y_i,y_j) = sum_(z,z') mu_z mu_(z') psi_Y(z,z') <= 0`. The zero function is cnd on
`R|_(X \ X_0)`.

**A bounded piece.** By Theorem 5.22 (i)=>(ii) for `R`, there are `E` with `mu(E) > 0` and `c` with `psi <= c` on
`R|_E`. We may take `E <= X_0`. Some `E_k = E ∩ {k(x) = k}` has positive measure. Put `F = g_k E_k <= Y`, so
`mu(F) = mu(E_k) > 0`. For `(z,w) in R|_F` write `z = g_k x`, `w = g_k y` with `x, y in E_k`. Then `(x,y) in R`,
`p x = z` and `p y = w`, so `psi_Y(z,w) = psi(x,y) <= c`. Theorem 5.22 (ii)=>(i) gives (T) for `R|_Y`. QED

**Lemma E (equal measures).** Let `E` be an ergodic p.m.p. countable relation on a finite measure space `(Z, rho)`
generated by a countable group `{h_1, h_2, ...}` of measure-preserving Borel automorphisms. If `B, C <= Z` are Borel
with `rho(B) = rho(C)`, then there are conull `B_* <= B`, `C_* <= C` and a Borel measure-preserving bijection
`theta: B_* -> C_*` with graph in `E`.

*Proof.* Exhaust.
- Start with `B_0 = B` and `C_0 = C`.
- At step `n`, let `D_n = B_(n-1) ∩ h_n^-1 C_(n-1)`, set `theta = h_n` on `D_n`, and put `B_n = B_(n-1) \ D_n`,
  `C_n = C_(n-1) \ h_n D_n`.
- The pieces `D_n` are disjoint, and so are the images `h_n D_n`. Let `B_inf = ∩ B_n` and `C_inf = ∩ C_n`. Equal
  measure is removed at each step, so `rho(B_inf) = rho(C_inf)`.

Suppose this common value is positive. The saturation of `B_inf` is invariant with positive measure, hence conull.
So some `h = h_n` has `rho(B_inf ∩ h^-1 C_inf) > 0`. But `B_inf <= B_(n-1)` and `C_inf <= C_(n-1)`, so
`B_inf ∩ h_n^-1 C_inf <= D_n`, which is disjoint from `B_n >= B_inf`. That is a contradiction. So `B_inf` and
`C_inf` are null, and `theta` is defined on `B_* = B \ B_inf` onto `C_* = C \ C_inf`. QED

**Lemma C (choice functions).** Let `T` be ergodic p.m.p. on `(Y, mu)`, and let `S <= T` be an ergodic subrelation
such that a.e. `T`-class is the union of exactly `k` `S`-classes. Then there are `phi_1 = id, phi_2, ..., phi_k` in
the full group `[T]` with `[x]_T = ⊔_(i <= k) [phi_i x]_S` for a.e. `x`.

*Proof.*

**The lifted relation.** Let `Y_0` be the conull `T`-invariant set where the index is `k`, and label classes
`c_1(x) = [x]_S, ..., c_k(x)` as in Section 0 with `Gamma = {g_1 = id, ...}` generating `T`. Put `Z = Y_0 x {1..k}`
with `rho = mu x counting`. Define `(x,i) E~ (y,j)` iff `(x,y) in T` and `c_i(x) = c_j(y)`. This is a Borel
equivalence relation.

For `g in Gamma` let `sigma_g(x) in Sym(k)` be defined by `c_(sigma_g(x) i)(g x) = c_i(x)`, and put
`g~(x,i) = (g x, sigma_g(x) i)`. The following hold.
- `g~` is a Borel bijection preserving `rho`: on the Borel pieces `{sigma_g = sigma} x {i}` it is `g x sigma`.
- `(g h)~ = g~ h~`, since both send `(x,i)` to the unique `(g h x, j)` with `c_j(g h x) = c_i(x)`.
- `E~` is the union of the graphs of the `g~`: if `(x,i) E~ (y,j)` and `y = g x`, then `sigma_g(x) i = j`.

So `E~` is the orbit relation of a measure-preserving action of `Gamma`, and it is p.m.p.

**Ergodicity.** `W = Y_0 x {1}` meets every class: given `(y,j)`, pick `x in c_j(y)`; then `c_1(x) = c_j(y)`. Let `B`
be `E~`-invariant and `A = {x : (x,1) in B}`. If `(x,y) in S` then `c_1(x) = c_1(y)`, so `A` is `S`-invariant, hence
null or conull.
- If `A` is null, then `B`, the saturation of `A x {1}`, is null.
- If `A` is conull, the complement of `B` is invariant and meets `W` in a null set, so it is null.

So `E~` is ergodic.

**The choice maps.** Apply Lemma E to `Z_i = Y_0 x {i}` and `W`, both of measure `mu(Y)`. This gives `theta_i`. Let
`phi_i(x) = pi(theta_i(x,i))`, with `theta_1 = id`. Since `theta_i(x,i) = (y,1)` with `(x,y) in T` and
`[y]_S = c_i(x)`, `phi_i` is a Borel measure-preserving bijection between conull sets with graph in `T`, so
`phi_i in [T]`. Moreover `[phi_i x]_S = c_i(x)`, and the `c_i(x)` exhaust `[x]_T / S` without repetition. QED

**Lemma I (induced cnd function).** In the situation of Lemma C, let `psi_S` be a real cnd function on `S`. For `(x,y) in T` let `tau = tau_(x,y) in Sym(k)` be given by
`[phi_(tau(i)) y]_S = [phi_i x]_S`, and put `psi_T(x,y) = sum_(i=1)^k psi_S(phi_i x, phi_(tau(i)) y)`. Then:
- (a) `psi_T` is a real cnd function on `T`;
- (b) `psi_T(x,y) >= psi_S(x,y)` for `(x,y) in S`;
- (c) `nu_T({psi_T <= c}) <= k nu_S({psi_S <= c})`.

*Proof.* `psi_T` is Borel, since `tau` is Borel through the class labels. Every pair `(phi_i x, phi_(tau(i)) y)` lies
in `S`.

**(a)** `psi_T(x,x) = 0` since `tau = id`. Symmetry follows from `tau_(y,x) = tau_(x,y)^-1`. For points
`y_1..y_n` in one `T`-class `C`, let `d_1..d_k` be the `S`-classes of `C`, and let `z_a^j` be the unique point among
`phi_1 y_a, ..., phi_k y_a` lying in `d_j`. Reindexing the sum by classes gives
`psi_T(y_a, y_b) = sum_j psi_S(z_a^j, z_b^j)`. For each `j`, the kernel `(a,b) -> psi_S(z_a^j, z_b^j)` is
conditionally negative definite: merge coefficients over equal points, as in Lemma R, using condition (iii) of
Def 5.19 inside the `S`-class `d_j`. A sum of such kernels is conditionally negative definite.

**(b)** If `(x,y) in S` then `tau(1) = 1`, and the `i = 1` term is `psi_S(x,y)`. The other terms are non-negative
("Note that $\psi$ must be a non-negative function").

**(c)** `psi_T(x,y) <= c` forces `psi_S(phi_i x, phi_(tau(i)) y) <= c` for every `i`, in particular for `i = 1`. So
`w = phi_(tau_(x,y)(1)) y` lies in `[x]_S` with `psi_S(x,w) <= c`. Each `w` arises from at most `k` points `y`,
namely among `phi_j^-1 w` for `j <= k`. So `|{y : psi_T(x,y) <= c}| <= k N_c(x)`, where
`N_c(x) = |{w in [x]_S : psi_S(x,w) <= c}|`. Integrate over `x`. (Part (c) is not used below.)

**Domains.** If `psi_S` satisfies Def 5.19 only on `S|_U` with `U` conull, let `U'` be the complement of the
`T`-saturation of `{x : phi_i x not in U for some i}`, together with the null sets where the `phi_i` are undefined.
This `U'` is conull and `T`-invariant, and (a)--(c) hold on `T|_(U')`, an inessential reduction. QED

## 5. Theorems A' and B, and the Kazhdan-group corollary

**Theorem A' (co-amenable subrelations are locally Kazhdan).** In Theorem A, `S|_A` has property (T).

*Proof.* `T = R|_A` is ergodic with (T) by Lemma R. `S|_A` is ergodic with exact index `k` in `T` by Theorem A. Let
`psi` be a real cnd function on `S|_A` and `psi_T` the induced function of Lemma I. By Theorem 5.22 (i)=>(ii) for
`T`, there are `E <= A` with `mu(E) > 0` and a constant `c` with `psi_T <= c` on `T|_E`. By Lemma I(b),
`psi <= psi_T <= c` on `(S|_A)|_E <= T|_E`. Theorem 5.22 (ii)=>(i) for the ergodic `S|_A` gives (T). QED

**Theorem B (no co-amenable Haagerup subrelations).** Let `R` be ergodic p.m.p. with property (T) on a diffuse
standard probability space. Then no subrelation `S <= R` with the Haagerup property is co-amenable in `R`. In
particular (Ueda, AD11 Thm 8.4) no treeable subrelation is co-amenable in `R`.

*Proof.* Suppose `S` is co-amenable with (H). Take `A` from Theorem A, so `S|_A` has (T) by Theorem A'.
- **(H) passes to `S|_A`.** AD11 Thm 6.5 gives a cnd `psi` on `S` (on an inessential reduction `S|_U`) with
  `nu_S({psi <= c}) < infty`. Its restriction to `S|_(A ∩ U)`, an inessential reduction of `S|_A`, is cnd. Because
  `A` is `S`-invariant, `nu_(S|_A)({psi <= c}) <= nu_S({psi <= c}) < infty`, and normalizing `mu|_A` only rescales.
  So `S|_A` has (H) by Thm 6.5.
- **The contradiction.** `S|_A` is ergodic, and `A` is a positive-measure subset of a diffuse space, hence diffuse.
  AD11 Thm 9.2 forbids (T) and (H) together. QED

**Corollary K.** Let `G` be an infinite countable group with property (T), and `G -> (X, mu)` an essentially free
ergodic p.m.p. action, for example a Bernoulli shift. Then:
1. the orbit relation `R_G` has property (T);
2. every co-amenable subrelation of `R_G` restricts, on a positive `S`-invariant set, to an ergodic, finite-index,
   Kazhdan subrelation;
3. no Haagerup subrelation of `R_G` (treeable, factor-of-iid percolation treeing, orbit relation of a free action of
   a Haagerup group inside `R_G`) is co-amenable.

*Proof.*
- **Part 1.** The quoted proof of AD11 Cor 9.4 says `X ⋊ G` has (T) under exactly these hypotheses, and AD05
  Thm 5.18 transfers (T) to the associated relation `R_G`.
- **Diffuseness.** An atom would have a finite orbit of equal-mass atoms, contradicting freeness with `G` infinite.
- **Parts 2 and 3.** Theorems A, A' and B. QED

## 6. Sharpness

### 6.1 Global finite index fails

Let `R` be ergodic with (T), and let `0 < mu(A) < 1`. Put `S = (R ∩ (A x A)) ∪ Delta_X`. Its classes are
`[x]_R ∩ A` for `x in A`, and singletons off `A`.
- **`S` is co-amenable.** The section `xi(x) = delta_([x]_R ∩ A)` is an invariant unit section of `lambda_(R/S)`.
- **Its index is infinite.** A.e. `R`-class meets `X \ A` in infinitely many points. (`R|_(X \ A)` is ergodic on a
  diffuse space, so its classes are infinite a.e.) Each such point is its own `S`-class.

So a co-amenable subrelation need not have finite index anywhere globally. Only the local form of Theorem A holds,
and "finite index" in the 2026-09-12 artifact must be read locally. Here `S|_A = R|_A`, consistent with Theorem A'.

### 6.2 Lemma C needs ergodicity of `S`

Let `Y = Y_1 ⊔ Y_2` with `mu(Y_1) = 0.9`, `T` ergodic, and `S = T ∩ (Y_1^2 ∪ Y_2^2)`. Each `T`-class is two
`S`-classes. A `phi_2 in [T]` with `phi_2 x` in the other class maps `Y_1` into `Y_2`, which is impossible by measure.

### 6.3 The group case is the constant-field case

For a free action and `S = R_H`, Theorem A with `k` the index recovers "co-amenable implies finite index" for
subgroups of Kazhdan groups. The invariant section is constant, so `A = X` and `k = [G:H]`, and the
simplicity step of `simple-kazhdan-groups-have-no-proper-co-amenable-subgroups` then gives `H = G`. The relation
statement has no simplicity analogue: 6.1 gives proper co-amenable subrelations of every Kazhdan relation. What
survives is the (T)/(H) exclusion.

## 7. What this kills and what it does not

**Killed class.** Every relation-level co-amenable ascent of a Rokhlin or f-invariant lower bound onto a Kazhdan
orbit relation that starts from a subrelation with the Haagerup property. This includes:
- a factor-of-iid treeing (Gaboriau--Lyons);
- a hyperfinite subrelation;
- the orbit relation of a free action of a free, amenable or Haagerup group sitting inside `R_G`;
- any treeable piece.

**Invariant.** Relation property (T), in the cnd-boundedness form of AD05 Thm 5.22.

**Step where every member dies.** The input to the ascent. The Følner or Reiter data on `[x]_R / S` give an
invariant unit section (Step 1). This forces a positive invariant piece on which the source subrelation is
Kazhdan (Theorem A'), and that contradicts the source's (H) (AD11 Thm 9.2).

This proves condition 4 of Section 4 of the 2026-09-12 artifact ("co-amenability collapses") for subrelations, which
that artifact marked "not proved here".

**What survives.**
- A source subrelation that is itself locally Kazhdan and of finite index on a piece. Then no entropy theory is
  available on it that is not already needed on `R_G|_A`.
- A transfer that uses no co-amenability at all.

Theorem B is a statement about mechanisms that use co-amenability. It does not claim that every lower-bound
mechanism needs co-amenability.

**Interaction with live lanes (swarm-0917).** a-gs-pull-11 records anti-monotonicity `eps_R <= eps_S` for `S <= R`
of Bernoulli extension entropy. So subrelation lower bounds do not lift for free, and a repair must add a transfer
hypothesis. Corollary K says a co-amenability transfer hypothesis confines the source to a locally Kazhdan,
finite-index piece.

## 8. Not proved here

- The measurable Day--Namioka step: an invariant field of means implies the Hilbert form of Section 2.
- A `h^Rok` transfer theorem along finite-index subrelations. Theorem A leaves `[R|_A : S|_A] = k`, and Seward-type
  compression formulas would be needed to use it.
- Hyperfinite subrelations are covered through "hyperfinite implies treeable" (Ornstein--Weiss / Connes--Feldman--Weiss
  and Dye's single generator). That standard fact is not imported verbatim here. Theorem B itself is stated for the
  Haagerup property and for treeable subrelations, which are imported.
