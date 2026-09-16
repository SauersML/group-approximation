# Three-element doubling sets are free bases, and what that excludes in K[F] (2026-09-16)

Agent: `hi-coun-zaremsky-2-01-thompson-f-amena` (counterexample / minimal-counterexample lane for
`zaremsky-2-01-thompson-f-amenable`). Not independently reviewed. Novelty is not claimed: Theorem 1 is
close to the Jónsson–Dekker characterization of Tarski number 4 and may well be folklore, but this
exact statement was not found in the sources listed in §6.

## 0. Conventions

`G` is a group. A finite set `S ⊆ G` **doubles** (in `G`) if `|S Y| >= 2|Y|` for every finite
`Y ⊆ G`, where `S Y = { s y : s ∈ S, y ∈ Y }`.

**Invariance.** For `g, h ∈ G` the set `g S h` doubles iff `S` doubles, because
`|g S h Y| = |S (h Y)|` and `Y -> h Y` is a bijection of finite subsets.

**Subsets.** If `S' ⊆ S` and `S` does not double, then `S'` does not double: a finite `Y` with
`|S Y| < 2|Y|` also has `|S' Y| <= |S Y| < 2|Y|`.

## 1. Theorem 1 (three-element doubling sets)

**Theorem 1.** Let `a, b ∈ G` with `1, a, b` pairwise distinct. The following are equivalent.

1. `{1, a, b}` doubles in `G`.
2. `a` and `b` freely generate a free group of rank 2.

### 1.1 Proof of (2) ⇒ (1)

Let `H = <a, b>`, free on `a, b`. For a letter `t ∈ {a^±1, b^±1}` let `W(t) ⊆ H` be the set of
reduced words beginning with `t`. Then `a W(a^-1) = H \ W(a)` and `b W(b^-1) = H \ W(b)`, so

`H = W(a) ⊔ a W(a^-1) = W(b) ⊔ b W(b^-1)`.

Define `μ_1, μ_2 : H -> H` by `μ_1(y) = a y` if `y ∈ a^-1 W(a)`, `μ_1(y) = y` otherwise (then
`y ∈ W(a^-1)`); and `μ_2(y) = b y` if `y ∈ b^-1 W(b)`, `μ_2(y) = y` otherwise (then `y ∈ W(b^-1)`).
`μ_1` is a bijection `H -> W(a) ⊔ W(a^-1)` and `μ_2` a bijection `H -> W(b) ⊔ W(b^-1)`. The four
sets `W(t)` are pairwise disjoint, so `(y, i) -> μ_i(y)` is injective on `H × {1, 2}`, with
`μ_i(y) ∈ {1, a, b} y`. Hence `|{1, a, b} Y| >= |μ_1(Y) ⊔ μ_2(Y)| = 2|Y|` for finite `Y ⊆ H`.

For finite `Y ⊆ G`, split `Y` along right cosets: `Y = ⊔_c Y_c c` with `Y_c ⊆ H` and `c` in a set
of representatives of `H \ G`. Since `{1, a, b} Y_c c ⊆ H c`, the sets `{1, a, b} Y_c c` are
disjoint, and `|{1, a, b} Y| = Σ_c |{1, a, b} Y_c| >= Σ_c 2|Y_c| = 2|Y|`.

### 1.2 Proof of (1) ⇒ (2)

Put `S = {1, a, b}` and `H = <a, b>`. `H` is countable.

**Step 1 (a 2-fold matching).** Consider the bipartite graph with left vertices `H × {1, 2}`,
right vertices `H`, and an edge from `(y, i)` to each of `y, a y, b y`. Every left vertex has
degree 3. For a finite set `W` of left vertices with projection `Y ⊆ H`, its neighbourhood is
`S Y`, and `|S Y| >= 2|Y| >= |W|` by (1). So Hall's condition holds for every finite set of left
vertices, and there is an injective map `μ : H × {1, 2} -> H` with `μ(y, i) ∈ S y`.

*Proof of this infinite Hall step.* Enumerate the left vertices `v_1, v_2, ...`. For each `n` let
`T_n` be the set of injective maps `f : {v_1, ..., v_n} -> H` with `f(v_j)` a neighbour of `v_j`.
`T_n` is finite (degrees are 3) and nonempty (finite Hall theorem). Restriction maps `T_(n+1)` into
`T_n`, so the `T_n` form an infinite, finitely branching rooted tree. By König's lemma it has an
infinite branch `f_1 ⊆ f_2 ⊆ ...`; `μ = ∪ f_n` is defined everywhere, and it is injective because
any two left vertices lie in the domain of some `f_n`. (This is M. Hall's 1948 theorem on
distinct representatives; the argument above is self-contained.)

Write `μ_i(y) = μ(y, i)`. Then `μ_1(y) ≠ μ_2(y)`. Say that `z ∈ H` **keeps itself** if `z = μ_i(z)`
for some `i`. By injectivity, if `z` keeps itself then `z ≠ μ_j(y)` for all `y ≠ z` and all `j`.

**Step 2 (the sets A, B).** Let `B` be the set of `y ∈ H` that keep themselves and `A = H \ B`.

- For `y ∈ A`, both `μ_1(y), μ_2(y)` lie in `{a y, b y}` and are distinct, so
  `{μ_1(y), μ_2(y)} = {a y, b y}`.
- For `y ∈ B`, exactly one of `μ_1(y), μ_2(y)` equals `y`; call the other one `φ(y)`. It lies in
  `{a y, b y}`.

**Step 3 (three facts).**

- (A1) `a A ⊆ A` and `b A ⊆ A`. If `y ∈ A` then `a y = μ_i(y)` for some `i`. If `a y ∈ B`, then
  `a y` keeps itself and is also `μ_i(y)` with `y ≠ a y` (as `a ≠ 1`), contradicting injectivity.
  The same argument works for `b`.
- (A2) `a A ∩ b A = ∅`. If `a y = b y'` with `y, y' ∈ A`, then `μ_i(y) = a y = b y' = μ_j(y')` for
  some `i, j`, so `y = y'` by injectivity, and then `a = b`, a contradiction.
- (A3) `φ` is an injection `B -> C := A \ (a A ∪ b A)`. First, `φ(y) ∈ A`: otherwise `φ(y)` keeps
  itself and equals `μ_j(y)` with `y ≠ φ(y)`. Second, if `φ(y) = a y'` with `y' ∈ A`, then
  `μ_j(y) = φ(y) = a y' = μ_i(y')` for some `i, j`, while `y ∈ B`, `y' ∈ A` are different; so
  `φ(y) ∉ a A`, and likewise `φ(y) ∉ b A`. Injectivity of `φ` is inherited from `μ`.

**Step 4 (the pieces).** Let `B_a = {y ∈ B : φ(y) = a y}` and `B_b = {y ∈ B : φ(y) = b y}`. Since
`a ≠ b`, `B = B_a ⊔ B_b`, and `φ(B_a) = a B_a`, `φ(B_b) = b B_b`. Put

`P_1 = a A`, `P_2 = B`, `Q_1 = b A ∪ b B_b`, `Q_2 = a B_a`.

They are pairwise disjoint: `P_1 ⊆ A` by (A1) and `P_2 = B`; `Q_1 ⊆ A \ a A` by (A1), (A2), (A3);
`Q_2 ⊆ C` by (A3), which is disjoint from `a A`, `b A` and `B`; and `a B_a ∩ b B_b = φ(B_a) ∩ φ(B_b) = ∅`
by injectivity of `φ`. Moreover

`H = a^-1 P_1 ⊔ P_2 = b^-1 Q_1 ⊔ a^-1 Q_2`,

because `a^-1 P_1 = A`, `b^-1 Q_1 = A ⊔ B_b` and `a^-1 Q_2 = B_a`. Multiplying on the left by `a`,
respectively by `b`, and writing `h = b a^-1`:

`H = P_1 ⊔ a P_2 = Q_1 ⊔ h Q_2`.   (★)

**Step 5 (nonemptiness).** `A ≠ ∅`, since otherwise `φ` injects the nonempty set `B = H` into
`C ⊆ A = ∅`. `B ≠ ∅`, since otherwise `A = H` and (A2) says `a H ∩ b H = ∅`. `B_a ≠ ∅`, since
otherwise `B = B_b`, so `Q_1 = b H = H`, contradicting `Q_1 ⊆ A` and `B ≠ ∅`. Hence all four pieces
are nonempty (`Q_1 ⊇ b A`).

**Step 6 (ping-pong).** Put `X(a) = P_1`, `X(a^-1) = P_2`, `X(h) = Q_1`, `X(h^-1) = Q_2`. From (★),

`a (H \ X(a^-1)) = X(a)`, `a^-1 (H \ X(a)) = X(a^-1)`, `h (H \ X(h^-1)) = X(h)`, `h^-1 (H \ X(h)) = X(h^-1)`.

For instance `H = P_1 ⊔ a P_2` gives `a (H \ P_2) = H \ a P_2 = P_1`, and left multiplication of
`H = P_1 ⊔ a P_2` by `a^-1` gives `a^-1 (H \ P_1) = P_2`; the `h` lines come from `H = Q_1 ⊔ h Q_2`
in the same way. Let `w = t_1 t_2 ... t_k` (`k >= 1`) be a reduced word in `a^±1, h^±1`. Choose a
letter `u` with `u ≠ t_k^-1` and `u ≠ t_1`, and `x ∈ X(u)`. Then `x ∉ X(t_k^-1)`, so
`t_k x ∈ X(t_k)`. Since `t_(k-1) ≠ t_k^-1`, the set `X(t_k)` is disjoint from `X(t_(k-1)^-1)`, so
`t_(k-1) t_k x ∈ X(t_(k-1))`; inductively `w x ∈ X(t_1)`. As `x ∉ X(t_1)`, `w x ≠ x` and `w ≠ 1`.
So `a, h` freely generate a free group of rank 2. Since `(a, b) = (a, h a)` is obtained from
`(a, h)` by a Nielsen transformation, `a, b` freely generate the same group. ∎

**Remark.** Steps 2–5 turn a 2-fold matching for `{1, a, b}` into a four-piece paradoxical
decomposition `(★)` of `H`; Step 6 is the ping-pong half of the Jónsson–Dekker theorem
(Tarski number 4 iff a non-abelian free subgroup), done by hand so that the free basis is explicit.

## 2. Corollary 2 (no free subgroups, no small doubling sets)

**Corollary 2.** If `G` has no non-abelian free subgroup, then no finite `S ⊆ G` with `|S| <= 3`
doubles: there is a finite nonempty `Y ⊆ G` with `|S Y| < 2|Y|`.

*Proof.* `|S| = 3`: write `S = s_0 {1, a, b}` with `1, a, b` distinct. By invariance and Theorem 1,
`S` doubles iff `a, b` are a free basis, which is impossible. `|S| = 2`: `S = s_0 {1, c}` with
`c ≠ 1`; `Y = {1, c}` gives `|S Y| = |{1, c, c^2}| <= 3 < 4`. `|S| <= 1`: `Y = {1}`. ∎

## 3. Theorem 3 (joint supports of size three in group rings)

**Theorem 3.** Let `G` have no non-abelian free subgroup, let `K` be a field, and suppose
`R = K[G]` has no zero divisors. Let `a, b ∈ R` be nonzero, and suppose there are `h_1, h_2 ∈ G`
with `|supp(a) h_1 ∪ supp(b) h_2| <= 3`. Then `a R ∩ b R ≠ 0`. Symmetrically, if
`|h_1 supp(a) ∪ h_2 supp(b)| <= 3` then `R a ∩ R b ≠ 0`.

*Proof.* `a R = a h_1 R` and `b R = b h_2 R`, so replace `a, b` by `a h_1, b h_2` and put
`S = supp(a) ∪ supp(b)`, `|S| <= 3`. By Corollary 2 there is a finite nonempty `Y` with
`|S Y| < 2|Y|`. The `K`-linear map `K^Y ⊕ K^Y -> K^(S Y)`, `(u, v) -> a u - b v` (with
`u = Σ_(y ∈ Y) u_y y`), goes from dimension `2|Y|` to dimension `|S Y| < 2|Y|`, so it has a nonzero
kernel vector `(u, v)`. If `u = 0` then `b v = 0`, so `v = 0` as `R` has no zero divisors and
`b ≠ 0`; hence `u ≠ 0`, similarly `v ≠ 0`, and `a u = b v ≠ 0`. The left version follows by
applying this to the anti-automorphism `g -> g^-1` of `G` (extended linearly), which maps
`h_1 supp(a) ∪ h_2 supp(b)` to a set of the same size. ∎

**For Thompson's group F.** `F` has no non-abelian free subgroup (Brin–Squier; graph node
`thompson-f-has-no-free-subgroups`) and is bi-orderable (`thompson-f-is-bi-orderable`). For a
bi-invariant order `<` and nonzero `x, y ∈ K[F]` with largest support elements `g_x, g_y`, every
`g ∈ supp x`, `h ∈ supp y` satisfies `g h <= g_x h <= g_x h_y`, with equality only for
`g = g_x`, `h = h_y`; so `g_x g_y ∈ supp(x y)` and `K[F]` has no zero divisors. Theorem 3 applies.

**Special cases in K[F]** (every field `K`, all nonzero coefficients):

1. Any two elements with at most two terms each: `supp(a) = {u_1, u_2}`, `supp(b) = {w_1, w_2}`,
   `h_1 = u_1^-1`, `h_2 = w_1^-1`. This is item 2 of the graph claim
   `thompson-f-twisted-binomial-pairs-have-common-multiples`, obtained here by a different argument.
2. A binomial `a` with `supp(a) = {u, v}` against a trinomial `b` with `supp(b) = {w_1, w_2, w_3}`,
   whenever `v u^-1 = w_j w_i^-1` for some `i ≠ j`. Take `h_1 = u^-1`, `h_2 = w_i^-1`. A 2-set
   and a 3-set have union of size 3 exactly when the 2-set is inside the 3-set, so for
   (binomial, trinomial) pairs this is precisely the case covered by Theorem 3. Example:
   `(1 + λ g, 1 + μ g + ν k)` for all `g ≠ 1`, `k ∉ {1, g}` and all `λ, μ, ν ∈ K^x`; the multi-bump
   `g` of `thompson-f-every-twisted-binomial-is-ore-with-every-element` are included.
3. Two trinomials with `supp(b) = supp(a) h` for some `h ∈ F`.

**Structural constraint on minimal counterexamples.** If `(a, b)` is a pair in `K[F]` with
`a R ∩ b R = 0` (such a pair exists iff `F` is not amenable, by `thompson-f-amenable-iff-group-ring-is-ore`),
then `|supp(a) h_1 ∪ supp(b) h_2| >= 4` for all `h_1, h_2 ∈ F`. Likewise every doubling set
witnessing `thompson-f-is-not-amenable` through `thompson-f-nonamenable-iff-some-monomial-set-doubles`
has at least four elements.

## 4. Sharpness: the bound 3 in Corollary 2 cannot be raised using only "no free subgroups"

**Definition used** (Ershov–Golan–Sapir, arXiv:1401.2202v4, Definition 1.1). `G` admits a paradoxical
decomposition if there are integers `m, n >= 1`, pairwise disjoint subsets `P_1, ..., P_m, Q_1, ..., Q_n`
of `G` and elements `g_1, ..., g_m, h_1, ..., h_n` with `G = ∪_i P_i g_i = ∪_j Q_j h_j`; the Tarski number
`T(G)` is the least `m + n`. EGS note `m, n >= 2`, and attribute to Jónsson and Dekker the theorem
`T(G) = 4` iff `G` contains a non-abelian free subgroup. Golan (arXiv:1406.2097v1, "Groups with Tarski
number 5") constructs a group with `T(G) = 5`; the abstract of arXiv:1401.2202 also states that groups
with Tarski numbers 5 and 6 exist.

**Proposition 4.** If `T(G) = 5`, then `G` has no non-abelian free subgroup and `G` contains a doubling
set with exactly four elements.

*Proof.* First, `m, n >= 2` in every decomposition: if `m = 1` then `P_1 g_1 = G`, so `P_1 = G` and every
`Q_j` is empty, contradicting `G = ∪ Q_j h_j`. Second, `G` has no non-abelian free subgroup (the easy
direction of Jónsson–Dekker, done here): if `a, b` freely generated `H <= G`, let `C` be a set of
representatives of the right cosets `H c` and use the sets `W(t)` of §1.1. The four sets `W(t) C` are
pairwise disjoint and `G = W(a) C ∪ a W(a^-1) C = W(b) C ∪ b W(b^-1) C`; inverting,
`G = P_1 ∪ P_2 a^-1 = Q_1 ∪ Q_2 b^-1` with `P_1 = (W(a) C)^-1`, `P_2 = (W(a^-1) C)^-1`,
`Q_1 = (W(b) C)^-1`, `Q_2 = (W(b^-1) C)^-1` pairwise disjoint, so `T(G) = 4`. Now take a decomposition
with `m + n = 5`; one of `m, n` is 2 and the other 3, and the definition is symmetric in `(P, g)` and
`(Q, h)`, so say `m = 2`, `n = 3`. Right multiplication by `g_1^-1` is a
bijection of `G`, so `G = P_1 ∪ P_2 g_2 g_1^-1`; likewise `G = Q_1 ∪ Q_2 h_2 h_1^-1 ∪ Q_3 h_3 h_1^-1`. So we
may assume `g_1 = h_1 = 1`. For `y ∈ G` let `μ_1(y) = y g_i^-1` for the least `i` with `y ∈ P_i g_i`, and
`μ_2(y) = y h_j^-1` for the least `j` with `y ∈ Q_j h_j`. Then `μ_1(y) ∈ P_i`, and `μ_1(y) = μ_1(y')`
forces equal indices (the `P_i` are disjoint), hence `y = y'`; similarly `μ_2` is injective, and its image
lies in `∪ Q_j`, which is disjoint from `∪ P_i`. So `(y, i) -> μ_i(y)` is injective on `G × {1, 2}` with
`μ_i(y) ∈ y T_0`, `T_0 = {1, g_2^-1, h_2^-1, h_3^-1}`, and `|Y T_0| >= 2|Y|` for finite `Y`. For
`T = T_0^-1 = {1, g_2, h_2, h_3}` and finite `Y`, `|T Y| = |(Y^-1 T_0)^-1| = |Y^-1 T_0| >= 2|Y|`, so `T`
doubles in the sense of §0. `|T| <= 4`, and `|T| >= 4` by Corollary 2. ∎

**Consequence.** Corollary 2 is optimal among statements that use only the absence of non-abelian free
subgroups: Golan's group has none and has 4-element doubling sets. Whether Thompson's group `F` has a
4-element doubling set is therefore a question about `F` specifically (it has none if `F` is amenable).
The same applies to extending Theorem 3 to joint supports of size four: the linear-algebra step needs a
non-doubling joint support, and no-free-subgroups alone does not supply one.

## 5. Census of subsets of Guba's nine monomials

(census section follows)

## 6. Sources (all fetched 2026-09-16 unless marked)

- V. Guba, "Amenability problem for Thompson's group F: state of the art", arXiv:2305.07113v4
  (2023-10-19), J. Groups Complex. Cryptol. 15 (1) (2023). Source of the nine-monomial set `S_(3,5)` of
  Problem `P_(2,2)` as recorded in the graph.
- M. Ershov, G. Golan, M. Sapir, "The Tarski numbers of groups", arXiv:1401.2202v4 (2014-07-10),
  Adv. Math. 284 (2015) 21–53. Definition 1.1 and the Jónsson–Dekker attribution were read from the
  arXiv PDF (introduction); the Jónsson–Dekker original was **not fetched**.
- G. Golan, "Groups with Tarski number 5", arXiv:1406.2097v1 (2014-06-09); only the abstract was read.
- P. A. Linnell, "Noncommutative localization in group rings", arXiv:math/0311071v2 (2004-07-26), in
  LMS Lecture Note Ser. 330 (2006); background for the Ore-condition formulation, abstract only.
- Brin–Squier (no free subgroups in `F`) and Cannon–Floyd–Parry (normal forms, relations) are used through
  the graph nodes `thompson-f-has-no-free-subgroups` and `thompson-f-is-bi-orderable` and their cited
  sources; they were **not refetched** here.
- M. Hall, Jr., distinct representatives for infinite families (Bull. Amer. Math. Soc. 1948) is
  **unverified**; it is not needed, since §1.2 Step 1 proves the required statement from the finite Hall
  theorem and König's lemma.
