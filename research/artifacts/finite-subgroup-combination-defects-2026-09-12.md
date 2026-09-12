# Finite-subgroup combination defects: every join, laminar families, sofic amalgams

Lane `w4-kap-join`, 2026-09-12. Supports
`sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`. Section 3 (added in a
later landing) records the surviving shapes on
`leavitt-units-have-laminar-finite-subgroup-defect`.

**Conventions.**
- `p` is prime, `G` is any group, and `S = F_p[G]`.
- Matrices act on column vectors `F_p[G]^n` by left multiplication. Projectives are right
  modules `e S^n`.
- For a finite `H <= G` and an idempotent `e in M_n(F_p[H])`, write
  `r(e) = dim_(F_p)(e F_p[H]^n) / |H|`, a rational number.
- By LFT1 of `lifted-trace-detects-finite-subgroup-projectives`, `t_p([e S^n]) = r(e)`.
- `r(e)` does not depend on the finite subgroup chosen to contain the support: `F_p[H']` is a
  free `F_p[H]`-module of rank `[H':H]`.

## 1. The infinite-join survivor was already dead

`mixed-finite-subgroup-defects-need-infinite-generation` (lane `w3-kap-kernel`, b820c4ec6e)
treats defects `e - f` with `f < e`, `e` supported in a finite `H_1` and `f` in a finite `H_2`.
- It excludes them when `<H_1, H_2>` is finite.
- It records the infinite join as the one surviving shape.

The infinite join does not survive.
- **Additivity.** For idempotents `f < e`, `[e S^n] = [f S^n] + [(e - f) S^n]`. So
  `t_p([(e - f) S^n]) = r(e) - r(f)` for every join.
- **Strict rank.** `nested-two-finite-subgroup-idempotents-have-strict-rank` (TFR1, established
  2026-09-07 by `two-finite-subgroup-nesting-amalgam-proof`) proves `r(e) > r(f)` whenever
  `ef = fe = f != e`, with no hypothesis on `<H_1, H_2>`.
- **Consequence.** `t_p(e - f) > 0`, so `e - f` is never a Kaplansky defect, whatever the join.

The established proof lifts the two multiplication rectangles to `H_1 *_D H_2` and compares
ranks in a finite quotient. The following second proof stays inside the two finite groups. It is
recorded here only as a cross-check.

**Proposition 1.1 (coset dimension count).** Let `H_1, H_2 <= G` be finite, put `D = H_1 n H_2`,
and let `e in M_n(F_p[H_1])` and `f in M_n(F_p[H_2])` be idempotents with `ef = f`.
Then `r(e) >= r(f)`. If also `fe = f` and `e != f`, then `r(e) > r(f)`.

*Proof.*
1. **Coset pieces.**
   - Take a left transversal `T` of `D` in `H_1` with `1 in T`, and write
     `e = sum_(a in T) [a] eps_a` with `eps_a in M_n(F_p[D])`.
   - Take a right transversal `Y` of `D` in `H_2`, and write `f = sum_(y in Y) f_y [y]` with
     `f_y in M_n(F_p[D])`.
   - If `a H_2 = a' H_2` for `a, a' in T`, then `a'^(-1) a in H_1 n H_2 = D`, so `a = a'`. The
     terms `[a] eps_a f` of `ef` therefore lie in pairwise disjoint cosets `a H_2`.
   - So `ef = f` is equivalent to `eps_1 f = f` together with `eps_a f = 0` for `a != 1`.
   - Left multiplication by `eps_a` preserves each right coset `D y`. So these equations read
     `eps_1 f_y = f_y` and `eps_a f_y = 0` for all `y`.
2. **The common submodule.**
   - Put `V = sum_y f_y F_p[D]^n`, a right `F_p[D]`-submodule of `F_p[D]^n`.
   - For `v = f_y w`: `e v = sum_a [a] eps_a f_y w = f_y w = v`.
   - Left multiplication by `e` commutes with right multiplication, so `e` fixes `V F_p[H_1]`.
   - `F_p[H_1]` is a free left `F_p[D]`-module, so `dim V F_p[H_1] = [H_1 : D] dim V`.
   - This subspace lies in `e F_p[H_1]^n`, so `r(e) >= dim V / |D|`.
3. **The upper bound.**
   - Every vector of `F_p[H_2]^n` is a sum of terms `u h` with `u in F_p^n` and `h in F_p[H_2]`.
   - So `f F_p[H_2]^n = sum_y f_y [y] F_p[H_2]^n` is contained in `V F_p[H_2]`, which has
     dimension `[H_2 : D] dim V`.
   - Hence `r(f) <= dim V / |D| <= r(e)`.
4. **Strictness.**
   - If `r(e) = r(f)`, both inclusions are equalities: `e F_p[H_1]^n = V F_p[H_1]` and
     `f F_p[H_2]^n = V F_p[H_2]`.
   - Inducing to `G` gives `e S^n = V S = f S^n`.
   - An idempotent acts as the identity on its image, so `fe = e`. With `fe = f` this gives
     `e = f`. QED

Only `ef = f` is used for the inequality; strictness uses both products.

## 2. Laminar families with a sofic amalgam

Two finite subgroups always have a residually finite amalgam, which is why TFR1 needs no
hypothesis on the join. With three or more finite subgroups, nested and orthogonal idempotents
can interact through intersections that close up into a cycle. The rectangle transfer still
carries every equation, but only to the amalgam of the whole configuration.

**Setup.**
- Let `H_0, ..., H_k <= G` be finite, and put `D_ij = H_i n H_j`.
- Let `A` be the colimit of the inclusions `H_i <- D_ij -> H_j` over all `i < j`. The inclusions
  induce `q : A -> G`, which restricts to the inclusion on each `H_i`.
- A *laminar family* is a finite set of distinct idempotents `x_i in M_n(F_p[H_i])` such that for
  `i != j`, `x_i x_j = x_j x_i` lies in `{0, x_i, x_j}`. Several `x_i` may use the same subgroup.
- A *laminar combination* is an idempotent of the commutative algebra `B` spanned by `1` and the
  `x_i`.

**Theorem 2.1.** If `A` is sofic, every nonzero laminar combination `d in M_n(S)` satisfies
`t_p([d S^n]) > 0`. So `[d S^n]` has infinite order in `K_0(S)`, and for every `m >= 0`,
`d (+) 0_m` is not the defect `I - ac` of any pair `ca = I` in `M_(n+m)(S)`.

**Lemma 2.2 (transfer).**
- Each `H_i` embeds in `A`.
- `H_i n H_j = D_ij` inside `A`.
- `q` is injective on every product set `H_i H_j` of `A`.

Consequently each relation `x_i x_j in {0, x_i, x_j}` holds in `M_n(F_p[A])` if and only if it
holds in `M_n(S)`.

*Proof.*
- `q` restricted to `H_i` is the inclusion, so `H_i` embeds.
- If `x in H_i n H_j` inside `A`, then `q(x)` lies in `H_i n H_j = D_ij` in `G`. Since `q` is
  injective on `H_i`, `x` lies in `D_ij`.
- If `ab = a'b'` in `G` with `a, a' in H_i` and `b, b' in H_j`, then `a'^(-1) a = b' b^(-1)` lies
  in `D_ij`, and the same identity holds in `A`. So `q` is injective on `H_i H_j`.
- The coefficient of `x_i x_j` at a point of `H_i H_j` is a sum over one `D_ij`-orbit of
  factorizations, and that orbit structure is the same in `A` and in `G`.
- The possible right-hand sides `0`, `x_i`, `x_j` are supported in `H_i u H_j`, which lies inside
  `H_i H_j`. QED

**Lemma 2.3 (sofic rank on finite subgroups).** Let `Gamma` be a countable sofic group. There is
a function `rk` on matrices over `F_p[Gamma]` with the following properties:
- `rk(a (+) b) = rk(a) + rk(b)` and `rk(I_n) = n`;
- `rk(u a v) = rk(a)` for invertible `u, v`;
- `rk(a) > 0` for `a != 0`;
- `rk(e) = r(e)` for every idempotent `e in M_n(F_p[H])` with `H <= Gamma` finite.

On idempotents `rk` is additive for orthogonal sums, so it induces a state on `K_0(F_p[Gamma])`.

*Proof.*
- **The rank function.**
  - Take sofic approximations `sigma_N : Gamma -> Sym(V_N)` along a free ultrafilter. They are
    asymptotically multiplicative in normalized Hamming distance, and for `g != 1` the density
    of fixed points of `sigma_N(g)` tends to `0`.
  - Extend linearly to matrices and put `rk(a) = lim_omega rank sigma_N(a) / |V_N|`.
  - Asymptotic multiplicativity in normalized rank makes `rk` a Sylvester matrix rank function
    (Elek--Szabo, *Sofic groups and direct finiteness*, J. Algebra 280 (2004)). That gives the
    first two properties and additivity on orthogonal idempotents.
- **Faithfulness.**
  - It suffices to treat one nonzero entry `a`, because the rank of a matrix dominates the rank
    of any entry. Let `Sigma` be its support and `a_(g_0) != 0`.
  - The points `v` at which the `sigma_N(g) v`, `g in Sigma`, are pairwise distinct have density
    tending to `1`.
  - Choose among them greedily a set `W` with `sigma(g) v != sigma(g_0) w` for all distinct
    `v, w in W` and all `g in Sigma`. Each choice excludes at most `|Sigma|^2 + |Sigma|` further
    points, so `|W| >= (1 - o(1)) |V_N| / (|Sigma|^2 + |Sigma| + 1)`.
  - Each vector `sigma_N(a) delta_v` with `v in W` has the nonzero coordinate `a_(g_0)` at
    `sigma(g_0) v`, where all the others vanish. So these vectors are linearly independent, and
    `rk(a) >= 1 / (|Sigma|^2 + |Sigma| + 1) > 0`.
- **Normalization.**
  - Let `Omega_N` be the set of points `v` with `sigma(g) sigma(h) v = sigma(gh) v` for all
    `g, h in H`, `sigma(1) v = v`, and `sigma(g) v != v` for `g != 1`. Its density tends to `1`.
  - For `v in Omega_N`, `g -> sigma(g) v` is injective, since `sigma(g) v = sigma(g') v` gives
    `sigma(g'^(-1) g) v = v`.
  - Its image `O_v` is invariant: `sigma(h) sigma(g) v = sigma(hg) v`. On `O_v`, `sigma` is a
    genuine free transitive action of `H`.
  - Two such orbits are equal or disjoint. So `U_N`, the union of the `O_v`, is a disjoint union
    of regular `H`-orbits, with density tending to `1`. Each `sigma(h)` maps `U_N` onto itself,
    hence also maps its complement onto itself.
  - As `sigma(H)`-modules, `F_p^(V_N) = F_p^(U_N) (+) F_p^(V_N \ U_N)`, and `F_p^(U_N)` is free
    over `F_p[H]` of rank `|U_N| / |H|`.
  - So `rank sigma_N(e) = (|U_N| / |H|) dim(e F_p[H]^n) + O(n |V_N \ U_N|)`, and dividing by
    `|V_N|` gives `rk(e) = r(e)`. QED

**Proof of Theorem 2.1.**
- **Lift the family.**
  - Lift each `x_i` to `X_i in M_n(F_p[A])` through the copy of `H_i` in `A`.
  - By Lemma 2.2 the `X_i` form a laminar family with the same multiplication table.
  - Write `d = c 1 + sum c_i x_i` and put `d_A = c 1 + sum c_i X_i`. It is idempotent because
    the table is the same.
  - `d_A != 0`, because `q(d_A) = d != 0`.
- **The atoms.**
  - The members of the family lying above a given `X_i` form a chain, so each `X_i` has a unique
    parent: the smallest member strictly above it, or `1`.
  - For `y = 1` or `y = X_i`, let `C(y)` be the set of children of `y`. They are pairwise
    orthogonal and below `y`, so `alpha_y = y - sum_(z in C(y)) z` is an idempotent.
  - The `alpha_y` are pairwise orthogonal and sum to `1`: each `X_i` appears once with sign `+`
    and once, under its parent, with sign `-`.
  - `B` is a finite commutative algebra spanned by idempotents, so `B ~= F_p^m`, and its nonzero
    idempotents are sums of distinct nonzero `alpha_y`.
- **Classes and traces.**
  - Additivity on orthogonal sums gives `[alpha_y] = [y] - sum_(z in C(y)) [z]`.
  - So `[d S^n] = m [S^n] + sum m_i [x_i S^n]` for integers `m, m_i`, and the same integers
    express `[d_A]`. Hence `t_p([d S^n]) = m n + sum m_i r(x_i)`.
- **Conclusion.**
  - `A` is countable (it is generated by finitely many finite groups) and sofic. By Lemma 2.3,
    `rk(d_A) = m n + sum m_i rk(X_i) = m n + sum m_i r(x_i) = t_p([d S^n])`.
  - Faithfulness gives `rk(d_A) > 0`.
  - A defect `I - ac` has class `[S^(n+m)] - [S^(n+m)] = 0`, hence `t_p = 0`. QED

**Corollary 2.4 (forest configurations).** Let `Phi` be the graph on `{0, ..., k}` with an edge
`i -- j` whenever `D_ij != 1`. If `Phi` is a forest, `A` is the fundamental group of a finite tree
of finite groups, hence virtually free, residually finite and sofic. Then Theorem 2.1 holds with
no hypothesis on `G` or on the join `<H_0, ..., H_k>`.

*Proof that `A` is virtually free.*
- **The tree.** Trivial edges only contribute free products, so add them to make `Phi` a tree.
- **The action.**
  - Take a finite set `X` whose size is divisible by every `|H_i|`, and root the tree.
  - Give the root group a free action on `X`.
  - Along each edge from a parent `i` to a child `j`, give `H_j` a free action on `X`. The two
    restrictions to `D_ij` are free `D_ij`-sets of equal size, hence conjugate, so conjugate the
    child's action until they agree on `D_ij`.
- **The kernel.**
  - This defines `A -> Sym(X)`, injective on each `H_i`.
  - Its kernel meets every conjugate of every vertex group trivially, so it acts freely on the
    Bass--Serre tree. It is therefore free, and it has finite index.
  - Free groups are residually finite, so `A` is residually finite. This is the tree version of
    the argument in `two-finite-subgroup-nesting-amalgam-proof`. QED

**Corollary 2.5 (two subgroups; sofic joins).**
- `k = 1` is always a forest. So Theorem 2.1 recovers TFR1 in characteristic `p`, strictness
  included.
- If the join `<H_0, ..., H_k>` is itself sofic, positivity already follows from Lemma 2.3 applied
  to the join. Amenable, LEF, residually finite and finitely generated linear joins are sofic.
- Theorem 2.1 is stronger than this: a forest configuration has a sofic amalgam however
  nonsofic its join is.

**Scope.** The theorem concerns laminar combinations, whose `K_0` classes are integer
combinations of finite-subgroup classes. It says nothing about idempotents similar to such
combinations through units of unbounded support. That module shape is the open part.

## 3. What survives, and the directive's candidates

Here `R^x = L_(F_2)(1,2)^x` and `p = 2`.

### 3.1 Candidates tested

- **Dyadic permutation subgroups at different prefix levels.**
  - For a 2-group `P`, `F_2[P]` is local, so its only idempotents are `0` and `1`. A laminar
    family in characteristic two uses only odd-order parts.
  - Two subgroups are excluded at every join, by TFR1 or Theorem 2.1 with `k = 1`.
  - Three or more with pairwise trivial intersections give a graph `Phi` with no edges. Then `A`
    is a free product of finite groups, so they are excluded too.
  - Constants at any levels lie in one finite subgroup `Theta(GL_(2^K)(F_2))`, through the tower
    identity `Theta_(2^(k+1))(a (x) I_2) = Theta_(2^k)(a)`. This is the computation of Section 8.2
    of `research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md`, carried out
    over `F_2`. So LFT1 alone excludes them.
- **Order-two and order-three elements generating `Z/2 * Z/3` inside `V`.** `F_2[Z/2]` has no
  nontrivial idempotents, so any family lives in `F_2[Z/3]` together with `1`. That is one finite
  subgroup, excluded by LFT1.

No candidate was constructed that survives Theorem 2.1.

### 3.2 Survivor S2: cyclic configurations with a nonsofic amalgam

A laminar defect needs all of the following:
- `k >= 2`;
- a cycle of nontrivial pairwise intersections in `Phi`, among non-constant finite subgroups (in
  `R^x`, for instance Thompson conjugates `u H u^(-1)`);
- a nonsofic intersection amalgam `A`;
- trace balance `m n + sum m_i r(x_i) = 0` with `d != 0`.

**The question lives in `A`.** Lemma 2.2 works in both directions. A nonzero laminar combination
with zero trace inside `F_p[A]` maps to one in every group `G` containing the configuration, since
the supports stay in the `H_i`, where `A -> G` is injective. So the first question is intrinsic:

> Does the intersection amalgam of some cyclic configuration of finite groups carry a nonzero
> laminar combination with zero lifted trace?

A positive answer is necessary for S2. A defect in `G` needs more: the class `[d S^n]` must vanish
in `K_0(S)`, and the trace alone does not give that.

**Soficity of such amalgams.**
- If `A` is residually finite or finitely generated linear, the configuration is excluded. This
  covers finite colimits and the linear lattices of `A_2~`-buildings.
- Colimits of triangles of finite groups include hyperbolic groups (Gersten--Stallings) and exotic
  `A_2~`-lattices. Their soficity is open, and a candidate has to live there.

### 3.3 Survivor S1: non-literal comparisons

S1 is `Q (+) Ind_(H_2) P_2 ~= Ind_(H_1) P_1`, with intertwiners of unbounded support and
`r(P_1) = r(P_2)`. This is the general Kaplansky problem for `R^x` plus a trace-balance condition,
and Theorem 2.1 does not reach it. Constraints already on main:
- `split-comparisons-balance-induced-brauer-characters`: Brauer balance in chart-injective finite
  images.
- `one-sided-shear-conjugates-cannot-strictly-nest`: one-orientation shears die.
- `finite-subgroup-copy-circuits-have-no-recurrent-branching`: recurrent copying cannot branch.
- Section 8.0 of the ternary normal-forms artifact: vanishing Hattori--Stallings class sums.

### 3.4 Where a positive proof would have to go

Suppose one wants to show that cyclic configurations never balance, in every group.
- By Lemma 2.2 the laminar table sees only `A`. So such a proof must either use relations of `G`
  beyond the pairwise rectangles, or prove positivity in `F_p[A]` for every configuration amalgam
  `A`.
- The second is an Atiyah-type positivity statement for laminar forests of idempotents over a
  2-complex of finite groups. No approach was found. Soficity of `A` is the only mechanism
  available.

### 3.5 A finite certificate of nonsoficity

Fix a group `G` (for instance `R^x`) and `n`. A *balanced configuration in `G`* consists of:
- finite subgroups `H_0, ..., H_k <= G`;
- a laminar family `x_i in M_n(F_p[H_i])`;
- a nonzero combination `d = c 1 + sum c_i x_i` that is an idempotent with
  `m n + sum m_i r(x_i) = 0`.

Given the finite subgroups and their intersections, every condition is a computation in the
finite groups:
- the laminar table is checked on the rectangles `(H_i x H_j)/D_ij`;
- idempotence of `d` follows from the table;
- `d != 0` is checked on the union of the `H_i`;
- the balance is a rational identity.

By Lemma 2.2 the same data give a nonzero zero-trace laminar combination in `F_p[A]`. So, by
Theorem 2.1:

> A balanced configuration in any group certifies that its intersection amalgam `A` is not sofic.

**Consequences.**
- A search for S2 candidates is automatically a search for finite certificates of nonsoficity of
  colimits of finite groups. A candidate therefore cannot be cheap.
- If the table lifts exactly to finite-support idempotents over `Z_p`, characteristic-zero trace
  positivity kills the configuration (Section 8.1 of the ternary normal-forms artifact). So a
  certificate needs modular cancellation in the table.
- A balanced configuration in `R^x` gives no defect by itself: `[d S^n] = 0` is still required.
