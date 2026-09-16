# Bengi--Wise doubles are left-orderable (counterexample lane, 2026-09-16)

Lane `hi-coun-kaplansky-zero-divisor-conject`. Target: `kaplansky-zero-divisor-conjecture`.
Angle (c): settle the status of a candidate host that the literature supplies. The root's Attempts
section lists "Bengi--Wise group: not classified here". This artifact classifies it. For every
admissible sequence `n`, the group `D(n)` of Bengi--Wise is left-orderable. So `D(n)` has unique
products, `k[D(n)]` is a domain over every field, and `D(n)` contains no subgroup isomorphic to
Promislow's group. The step of the source that fails is identified in §5.

Nothing here has been independently reviewed.

## 1. The source, read at source

N. Bengi and D. T. Wise, *Residually finite groups that do not virtually have the unique product
property*, arXiv:2602.11819v1. On 2026-09-16 the e-print TeX source was fetched from
`arxiv.org/e-print/2602.11819` (`main.tex`, md5 `59cd378f4c0c341697af4015834a326c`, dated
2026-02-12 in the tarball). No v2 was found (`arxiv.org/abs/2602.11819v2` returned 404 on
2026-09-16), and no erratum or journal version turned up in a web search. The TeX acknowledges a
referee.

Verbatim statements used (TeX line numbers):

- l. 139: `P = \langle x,y \ \mid \ x^{-1}y^2xy^2 \ , \ y^{-1}x^2yx^2 \rangle` (Promislow's group).
- l. 141--143: "In fact, $P$ arises as an amalgamated product, actually a `double': $$P\ \cong \
  K\underset{T}{*} K$$ where $K$ is $\pi_1$ of the Klein-bottle, and $T\subset K$ is the index~2
  subgroup isomorphic to $\integers^2$."
- l. 186 (definition): "The \emph{double} of $G$ along $H$ is the amalgamated free product
  $G\underset{H=\underline H }{*} \underline G$, which amalgamates $G$ and $\underline G$ by
  identifying $H$ with $\underline H$ using this isomorphism." "This isomorphism" is the copy map of
  l. 184: "there is an isomorphism $G\rightarrow \underline G$ denoted by $g\mapsto \underline g$".
- l. 191: "Promislow's group $P$ arises as the double $P = K\underset{T}{*} \underline K$."
- l. 353: "Let $F$ be the free group on $a,b$."
- l. 452: "Consider the double $G = F * _{\widehat{H}} \underline{F}$."
- l. 457: `K_i = \langle a^{-i} b^{n_i} a^i, \ \underline{a}^{-i}\underline{b}^{n_i}\underline{a}^{i} \rangle`.
- l. 481--482: "The groups we are interested in are the following doubles: $$D \ = \ D(\vec{n}) \
  = \ G \underset{\widehat Y}{*} \underline{G}.$$" Here `\widehat Y = C_G(z)` with
  `z = b^{-n_0}\underline b^{n_0}` (l. 461).
- l. 496--499: "Let $P_i=\langle K_i , \underline K_i \rangle$ be the $i$-th copy of the Promislow
  group in $D$. Indeed, each $K_i \underset{T_i}{*} \underline{K}_i \rightarrow G \underset{\widehat
  Y}{*} G$ is injective by Lemma~\ref{lem:NFT_and_doubles}. Hence $P_i \cong K_i\underset{T_i}{*}
  \underline K_i \cong P$."
- l. 503--508 (main theorem): "Suppose $\vec n$ has the property that for each $r\geq 1$, we have
  $r!$ divides some $n_i$. Then $D=D(\vec n)$ persistently contains $P$. In particular, this holds
  for $n_i=2\cdot(i!)$."
- l. 156--157 (introduction): "There is a finitely generated residually finite torsion-free group
  that persistently contains Promislow's group."

"Persistently contains `P`" means that every finite-index subgroup contains a subgroup isomorphic to
`P` (definition, l. 125--130).

Two facts about the source matter below.
- Both `G` and `D(n)` are doubles in the sense of l. 186, that is, amalgams of a group with its copy
  along the copy map.
- `F` is free.
Nothing else in the construction (the subgroups `\widehat H`, `\widehat Y`, the sequence `n`)
enters the argument of §3.

## 2. Four elementary lemmas

A group `G` is *left-orderable* (LO) if it carries a total order `<` with `g < h => fg < fh` for
all `f, g, h`. Equivalently, it has a *positive cone*: a subset `Pi` with `Pi Pi ⊆ Pi` and
`G = Pi ⊔ Pi^-1 ⊔ {1}`. Given `Pi`, set `g < h` iff `g^-1 h in Pi`. Subgroups of LO groups are LO,
by restricting the order.

**Lemma 2.1 (extensions).** If `1 -> N -> E -> Q -> 1` is exact, with `N` and `Q` LO, then `E` is
LO.

*Proof.* Let `pi : E -> Q` be the quotient map, and let `Pi_N` and `Pi_Q` be positive cones. Put
`Pi = pi^-1(Pi_Q) ∪ Pi_N`.
- *Trichotomy.* Let `g in E` with `g != 1`. If `pi(g) != 1`, exactly one of `pi(g)` and `pi(g)^-1`
  lies in `Pi_Q`. If `pi(g) = 1`, then `g in N \ {1}`, and exactly one of `g` and `g^-1` lies in
  `Pi_N`.
- *Closure.* Let `g, h in Pi`.
  - If both lie in `pi^-1(Pi_Q)`, then `pi(gh) = pi(g) pi(h) in Pi_Q`.
  - If exactly one lies in `pi^-1(Pi_Q)`, the other lies in `N`, so `pi(gh)` equals `pi(g)` or
    `pi(h)`, which lies in `Pi_Q`.
  - If both lie in `Pi_N`, then `gh in Pi_N`.
No conjugation invariance of `Pi_N` is needed. □

**Lemma 2.2 (LO ⇒ unique products ⇒ domain).** Let `G` be LO, and let `A, B ⊆ G` be finite and
nonempty. Then `m = max(AB)` has exactly one expression `m = ab` with `a in A` and `b in B`.
Consequently, for every field (indeed every domain) `k`, the group ring `k[G]` has no zero divisors.

*Proof.* Let `b_0 = max B`, and suppose `m = ab` with `a in A` and `b in B`. If `b < b_0`, then
`ab < a b_0` by left invariance. But `a b_0 in AB`, so `a b_0 <= m = ab`, a contradiction. Hence
`b = b_0` and `a = m b_0^-1`.

For nonzero `alpha, beta in k[G]`, apply this to `A = supp alpha` and `B = supp beta`. The coefficient
of `m` in `alpha beta` is then `alpha_a beta_{b_0} != 0`. □

**Lemma 2.3 (free groups are LO).** Every free group `F(S)` is left-orderable, and in fact
bi-orderable.

This is classical (Magnus; B. H. Neumann), and the graph already uses it as an import. A complete
proof follows so that the route needs no literature here.

*Proof.* Let `R` be the ring of formal power series in noncommuting variables `X_s` (`s in S`)
whose homogeneous components are finite sums of monomials. It is closed under products, because
the degree-`n` component of a product is `sum_{i+j=n} h_i k_j`. Let `m` be its ideal of series with
zero constant term, and put `U = 1 + m`. `U` is a group, with `(1+h)^-1 = sum_{n>=0} (-h)^n`: only
the terms with `n <= d` contribute in degree `d`, so each component is again a finite sum.

*The Magnus map.* Define `mu : F(S) -> U` by `s -> 1 + X_s`. For `e in Z \ {0}` we have
`mu(s^e) = (1 + X_s)^e = 1 + e X_s + (terms in X_s^2, X_s^3, ...)`. Let
`w = s_1^{e_1} ... s_r^{e_r}` be a nontrivial reduced word, so `r >= 1`, `s_i != s_{i+1}` and
`e_i != 0`.
- In `mu(w)`, the monomial `X_{s_1} X_{s_2} ... X_{s_r}` arises only by choosing `X_{s_i}^{k_i}` from
  the `i`-th factor with `sum k_i = r`.
- If some `k_j >= 2`, the product contains the square `X_{s_j}^2` as a subword. The target monomial
  has no two equal adjacent letters, so this is impossible.
- Hence every `k_i <= 1`, and with `sum k_i = r` every `k_i = 1`.
So that monomial has coefficient `e_1 e_2 ... e_r != 0`, and `mu(w) != 1`. Thus `mu` is injective.

*An order on U.* Totally order `S`. Order the monomials of each fixed degree lexicographically,
which is a total order on them. For `u = 1 + h != 1`:
- let `d` be the least degree in which `h` has a nonzero homogeneous component `h_d`;
- let `c(u)` be the coefficient in `h_d` of the least monomial occurring in `h_d`.

Put `Pi = {u != 1 : c(u) > 0}`.
- *Trichotomy.* `u^-1 - 1 = -h + h^2 - ...`, and its degree-`d` component is `-h_d`, because `h^2`
  starts in degree `2d > d`. So `c(u^-1) = -c(u)`, and exactly one of `u` and `u^-1` lies in `Pi`.
- *Closure.* Let `u = 1 + h` and `v = 1 + k` lie in `Pi`, with least degrees `d` and `e`. Then
  `uv - 1 = h + k + hk`, and `hk` starts in degree `d + e`, which exceeds both `d` and `e`.
  - If `d != e`, the lowest component of `uv - 1` is that of `u` or of `v`, so `c(uv) > 0`.
  - If `d = e`, the degree-`d` component is `h_d + k_d`. Let `m_0` be the lesser of the least
    monomials of `h_d` and `k_d`. Every monomial below `m_0` has coefficient zero in both, and the
    coefficient of `m_0` is a sum of two nonnegative numbers, at least one of them positive. Hence
    `h_d + k_d != 0` and `c(uv) > 0`.

So `U` is LO, and `F(S) ≅ mu(F(S)) <= U` is LO. □

**Lemma 2.4 (doubles).** Let `A` be LO, let `C <= A` be any subgroup, let `\underline A` be a copy
of `A` via `a -> \underline a`, and let `D = A *_{C = \underline C} \underline A` be the double.
Then `D` is LO.

*Proof.* The *fold* `rho : D -> A` is `a -> a` on `A` and `\underline a -> a` on `\underline A`.
The two maps agree on the amalgamated subgroup, since `c = \underline c` in `D` and both go to `c`,
so the universal property of the amalgam defines `rho`. `rho` restricted to the images of `A` and
`\underline A` in `D` is the identity and the inverse copy map, so these images embed, and `rho`
is injective on each of them.

Let `N = ker rho`. For every `g in D`, `N ∩ gAg^-1 = g(N ∩ A)g^-1 = 1`, and likewise for
`\underline A`.

`D` acts without inversion on the Bass--Serre tree of the amalgam, and the vertex stabilizers are
the conjugates of `A` and `\underline A`. So `N` acts without inversion and with trivial vertex
stabilizers, that is, freely. A group acting freely without inversion on a tree is free. Both
facts are Serre, *Trees* (Springer, 1980), Chapter I: the tree of an amalgam, and free actions on
trees. The section numbers were not re-checked against the book on 2026-09-16. The graph uses the
same two facts in `every-noninjective-star-fold-has-kernel-f-infinity-proof`.

So `N` is free, hence LO by Lemma 2.3. `rho` is onto, with LO quotient `A`, so `D` is LO by
Lemma 2.1. □

*Iterating.* A double of a double of a free group is LO, and so on.

## 3. The Bengi--Wise groups are left-orderable

**Theorem 3.1.** For every multiplicative sequence `n` and every choice of the subgroups
`\widehat H <= F` and `\widehat Y <= G`, the groups `G = F *_{\widehat H} \underline F` and
`D(n) = G *_{\widehat Y} \underline G` of §1 are left-orderable. Hence:
- `D(n)` has unique products;
- `k[D(n)]` is a domain for every field `k`;
- `D(n)` is torsion-free;
- `D(n)` contains no subgroup isomorphic to Promislow's group `P`.

*Proof.* `F` is free, hence LO (Lemma 2.3). `G` is a double of `F` (l. 452), so it is LO by
Lemma 2.4. `D(n)` is a double of `G` (l. 481--482), so it is LO by Lemma 2.4 again.
- Unique products and the domain property follow from Lemma 2.2.
- A nontrivial element of finite order `q` in a left-ordered group is impossible: `g > 1` gives
  `1 < g < g^2 < ... < g^q = 1`, and `g < 1` symmetrically.
- A subgroup isomorphic to `P` would be LO, but `P` is not LO (Proposition 4.1). □

**Corollary 3.2.** The main theorem of arXiv:2602.11819v1 (l. 503--508) is false: no `D(n)`
contains `P` at all. The introduction's theorem (l. 156--157) is not established by that paper.

The corollary asserts only that the construction fails. It does not decide whether some other
finitely generated residually finite torsion-free group persistently contains `P`, or more weakly
is not virtually unique-product.

## 4. Promislow's group is not left-orderable

Use the graph's presentation `P = <a, b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>`. It agrees with
the source's (`a = x`, `b = y`).

**Lemma 4.1 (Klein relation).** Let `<` be a left order on a group, and suppose
`c^-1 s c = s^-1` with `c > 1`. Then `s^k < c` for every `k in Z`.

*Proof.* From `c^-1 s^k c = s^-k` we get `s^k c = c s^-k` for all `k`, and so `s^-k c = c s^k`.
- If `s^k <= 1`, then `s^k <= 1 < c`.
- If `s^k > 1`, suppose `c <= s^k`. Left-multiplying by `s^-k` gives `s^-k c <= 1`. But
  `s^-k c = c s^k > c > 1`, where `c s^k > c` holds by left invariance from `s^k > 1`. This is a
  contradiction, so `s^k < c`. □

**Proposition 4.1.** `P` is not left-orderable.

*Proof.* First, the two relations also hold with `a` and `b` inverted.
- From `a^-1 b^2 a = b^-2` we get `a^-2 b^2 a^2 = a^-1 b^-2 a = b^2`, so `a^2` commutes with `b^2`.
- Then `a b^2 a^-1 = a^2 (a^-1 b^2 a) a^-2 = a^2 b^-2 a^-2 = b^-2`.
- Symmetrically `b a^2 b^-1 = a^-2`.

So for both signs `e`, `(a^e)^-1 b^2 a^e = b^-2`, and for both signs `f`, `(b^f)^-1 a^2 b^f = a^-2`.

Suppose `<` is a left order on `P`. Choose signs with `c := a^e > 1` and `d := b^f > 1`. Neither `a`
nor `b` is trivial, since `P` maps onto `(Z/4)^2` with `a -> (1,0)` and `b -> (0,1)`; see §5 and the
experiment.
- Lemma 4.1 with `(c, s) = (a^e, b^2)` gives `b^{2k} < c` for all `k`.
- Lemma 4.1 with `(c, s) = (b^f, a^2)` gives `a^{2k} < d` for all `k`.
- Left invariance from `c > 1` gives `c < c^2`, and `c^2 = a^{2e}` is a power of `a^2`.
- Likewise `d < d^2 = b^{2f}`, a power of `b^2`.

Hence `c < c^2 = a^{2e} < d < d^2 = b^{2f} < c`, a contradiction. □

Every step is a finite computation in `P` from the two defining relations. No literature is used.
The standard statement that `P` is torsion-free without unique products is Promislow, Bull. London
Math. Soc. 20 (1988) 302--304. That reference was taken from the Bengi--Wise bibliography and not
re-fetched. It is not needed here.

## 5. Where the source goes wrong

Let `K = <u, v | u^2 = v^2>` be the Klein bottle group, and put `s = u^-1 v`. Then `u^-1 s u = s^-1`,
`u^2` is central, and `T = <u^2, s> ≅ Z^2` is the unique index-2 subgroup isomorphic to `Z^2`.

In the source, `K_i = <c, \underline c>` with `c = a^-i b^{n_i} a^i`, so `(u, v) = (c, \underline c)`.
Also `T_i = <c^2, c \underline c^-1>` (l. 471--478), and since
`c \underline c^-1 = u v^-1 = u s^-1 u^-1 = s` in `K`, this is `T_i = T`.

**(a) The copies `P_i` are honest doubles of `K`.** Inside `D = G *_{\widehat Y} \underline G`,
each `t in T_i ⊆ \widehat Y` is identified with its copy `\underline t`. So
`P_i = <K_i, \underline K_i> ≅ K *_{T = \underline T} \underline K` with the identity gluing, as the
source itself writes (l. 498--499). This group has the presentation
`<u, v, U, V | u^2 = v^2, U^2 = V^2, u^2 = U^2, u^-1 v = U^-1 V>`.

Substitute `s = u^-1 v` and `t = U^-1 u`, so that `v = us`, `U = u t^-1` and `V = U s`. The
relations become `u^-1 s u = s^-1`, `u^-1 t u = t^-1` and `[s, t] = 1`.
- *Honest double ⇒ these relations.*
  - The first is the Klein relation.
  - For the second, `u^-1 t u = u^-1 U^-1 u^2 = u^-1 U^-1 U^2 = u^-1 U = t^-1`, using `u^2 = U^2`.
  - For the third, `t s t^-1 = U^-1 (u s u^-1) U = U^-1 s^-1 U = s`. Here `u s u^-1 = s^-1`
    because `u^2` commutes with `s`, and `U^-1 s U = s^-1` is the Klein relation in the second
    factor, since `U^-1 V = s`.
- *These relations ⇒ honest double.* The images of the four honest relators evaluate to the
  identity in a faithful affine action of `<u, s, t>` on `R^3`, checked by
  `experiments/bengi-wise-double-abelianization-2026-09-16/snf.py`. The two substitutions are
  mutually inverse on generators.

So `P_i ≅ Z^2 x|_{-I} Z`, the half-turn (dicosm) group. It is poly-`Z`, hence LO, as Lemma 2.4
also shows. Its abelianization is `Z ⊕ (Z/2)^2`.

**(b) `P` is a twisted amalgam of two Klein bottle groups.** In `P = <a, b | ...>`:
- `K_a = <a, b^2>` is a Klein bottle group (`a` inverts `b^2`) with torus `<a^2, b^2>`;
- `K_b = <b, a^2>` is one too, with the same torus.

So `P = K_a *_{T} K_b`. The gluing matches the central generator `a^2` of `K_a` with the
non-central generator `a^2` of `K_b`, and vice versa for `b^2`. In the notation of `K` and
`\underline K`, the relations read `u^2 = U^-1 V` and `u^-1 v = U^2`. Substituting `v = u U^2` and
`V = U u^2` leaves exactly the two relators of `P` (verified on words by the experiment).

An isomorphism `K -> \underline K` carries the center `<u^2>` to the center `<U^2>`. This gluing
sends `u^2` to the non-central `U^-1 V`, so it extends to no such isomorphism, and the amalgam is
not a double in the sense of l. 186. By (c) it is not even isomorphic to one.

**(c) Certificate that `P_i` is not `P`.**

| group | H_1 |
|---|---|
| `P` | `(Z/4)^2` |
| honest double `K *_T \underline K` | `Z ⊕ (Z/2)^2` |
| twisted amalgam | `(Z/4)^2` |

These are Smith normal forms computed by the experiment: `snf.py`, md5
`9b2970c766767c760d3e16c869f6a65f`; output `snf.out`, md5 `3b7f36f95eba14913fd7ceb8ff88ed8a`, which
ends `ALLOK`. The honest double retracts onto `K` and hence onto `Z`, so no computation is needed
for infiniteness.

The false step is l. 191 ("$P = K\underset{T}{*} \underline K$" with the gluing of l. 186),
repeated at l. 499.

## 6. Consequences and lessons for the counterexample lane

1. **Host list.** The root's Attempts entry "Bengi--Wise group: not classified here" can be
   replaced. `D(n)` is left-orderable, so it satisfies the zero-divisor conjecture over every field
   by unique products. It is not a candidate host, and it plants no Promislow subgroup.
2. **The source's question is reopened.** The source claims to answer Kionke--Raimbault (Doc.
   Math. 21 (2016) 873--915; bibliography entry only, not re-fetched), who asked whether every
   finitely generated residually finite torsion-free group is virtually diffuse. After §3, the paper
   gives no such group, and no group that fails to be virtually UP.

   The source says (l. 162) that "Recently Ng also produced residually finite groups that are not
   virtually diffuse". The bibliography entry is A. Ng, *Virtual First Betti Number of GGS Groups*,
   arXiv:2505.23269. It was not fetched on 2026-09-16, and whether those groups are torsion-free
   was not checked.
3. **Why doubling cannot plant non-UP subgroups.** The source proves residual finiteness of doubles
   by Boler--Evans (l. 293--307: a double of a residually finite group along a separable subgroup is
   residually finite). For elements of the two factors, that argument uses the fold. Lemma 2.4
   uses the same fold to transfer left-orderability.

   So iterated doubles, and more generally any amalgam with a homomorphism to a LO group that is
   injective on both factors, are LO whenever the base is. A construction that persistently plants
   `P` needs gluings that do not factor through a fold, such as the swap of §5(b). Its residual
   finiteness then needs a different argument.



