# Thompson V rank gate: sofic-configuration and characteristic-uniform firewalls

Lane `w5-v-nonamenable`, 2026-09-12.

**Target.** V's rank gate for abstract Sylvester rank functions: every Sylvester matrix rank function on `F[V]`,
`char F = p > 0`, is the augmentation rank. Over `F_3` this is `thompson-v-ternary-rank-functions-are-augmentation`;
over `F_2` it is the abstract form of `thompson-v-has-no-nontrivial-f2-rank-model`.

**What this artifact does.** It decides neither gate. It proves two firewalls that say where a proof has to live,
and it names the first configurations they leave open.
- **Section 1:** no finitary argument confined to a sofic configuration can push `rk(1 - [g])` below `1 - 1/ord(g)`.
  No import is needed, and free products are covered. This complements Proposition 3.2 of
  `thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`. It widens the group class but drops the
  tuple-level premises that proposition allows, so the two are incomparable (Remark 1.4).
- **Section 2:** the instances inside `V`: lamp groups, free products, Thompson's `F`.
- **Section 3:** any argument built from identities that also hold over a subring of `C` fails, because of the
  von Neumann rank. So a proof must use a `p`-sensitive identity.
- **Section 4:** both requirements together, and the first natural `p`-sensitive structure question: the
  order-`char F` cycle law.

## 0. Setting

- **Rank functions.** A Sylvester matrix rank function on a ring `A` assigns `rk(M) >= 0` to every rectangular
  matrix over `A`, with:
  - (S0) `rk(1) = 1`;
  - (S1) `rk(MN) <= min(rk M, rk N)`;
  - (S2) `rk(M ⊕ N) = rk M + rk N`;
  - (S3) `rk [[M, C], [0, N]] >= rk M + rk N`.
- **Derived facts used below.**
  - Unit invariance: `rk(UMW) = rk(M)` for invertible `U, W`.
  - Frobenius: `rk(ABC) + rk(B) >= rk(AB) + rk(BC)`.
    - The lower-triangular form of (S3) gives `rk [[AB, 0], [B, BC]] >= rk(AB) + rk(BC)`.
    - Multiplying on the left by `[[1, -A], [0, 1]]` and on the right by `[[1, -C], [0, 1]]` turns this matrix into
      `[[0, -ABC], [B, 0]]`, whose rank is `rk(ABC) + rk(B)` by (S2) and unit invariance.
  - Pullback: a rank function on `F[V]` restricts to one on `F[K]` for every `K <= V`.
- **Terms.**
  - The augmentation rank is the one induced by `F[V] -> F`.
  - A rank function is detecting if `rk(1 - [g]) > 0` for all `g != 1`.
  - A clopen `n`-cycle is an element `s` of order `n` with disjoint nonempty clopen sets `U_0, ..., U_(n-1)` and
    `s(U_i) = U_(i+1)` (indices mod `n`), which is the identity on the complement of their union. That complement
    must be nonempty. A clopen transposition is a clopen `2`-cycle.
  - All clopen `n`-cycles are conjugate in `V`. Put `h = s'^i h_0 s^-i` on `U_i` for a `V`-map `h_0 : U_0 -> U'_0`,
    together with a `V`-map between the complements. The complement condition is needed, since `hsh^-1` fixes
    exactly `h(Fix s)`.
  - By `simple-group-rank-functions-are-augmentation-or-detecting`, every rank function on `F[V]` is one or the
    other, because `V` is simple.

**Confined arguments.** Fix a finite set `S ⊆ V` and put `K = <S>`. An argument about a rank function `rk` on
`F[V]` is *confined to `S`* if its conclusion is a statement about values of `rk` on matrices over `F[K]`, and each
premise is of one of three kinds:
- (P1) an instance of (S0)–(S3), or a consequence of them, applied to matrices over `F[K]`;
- (P2) an equality between matrices over `F[K]` that holds in `F[K]` (equivalently in `F[V]`);
- (P3) single-element conjugacy data: `rk(q([g])) = rk(q([g']))` for `g, g'` in `K` that are conjugate in `V`,
  and `q` in `F[t]`.

The conjugator in (P3) may lie outside `K`. Using that `h` in `V` conjugates a *tuple* of `K` to another tuple is a
(P2) premise once `h` is put into `S`; otherwise it is not confined.

## 1. Sofic configurations are inert

**Lemma 1.1 (sofic rank functions; standard, proof included).** Let `K` be a countable sofic group, `F` any field.
Then `F[K]` carries a Sylvester matrix rank function `rk_K` such that, for `g` in `K` and nonzero `q` in `F[t]`:
- `rk_K(q([g])) = 1 - deg gcd(q, t^n - 1)/n` if `g` has finite order `n`;
- `rk_K(q([g])) = 1` if `g` has infinite order.

In particular `rk_K(1 - [g]) = 1 - 1/ord(g)`, read as `1` for infinite order, and `rk_K` is detecting.

*Proof.*
1. **The approximations.** Take maps `sigma_k : K -> Sym(n_k)` with `d_H(sigma_k(gh), sigma_k(g)sigma_k(h)) -> 0`
   and `d_H(sigma_k(g), 1) -> 1` for `g != 1`. Extend `sigma_k` linearly to `F[K]`, sending `g` to its permutation
   matrix, and entrywise to matrices.
2. **The rank function.** Put `rk_K(M) = lim_omega rank(sigma_k(M))/n_k` along a free ultrafilter.
   - (S0), (S2) and (S3) hold at every `k`.
   - For (S1): `sigma_k(MN) - sigma_k(M)sigma_k(N)` is a finite combination of differences
     `P_(sigma(gh)) - P_(sigma(g))P_(sigma(h))`. Each difference has rank at most the number of points where the two
     permutations differ, so the normalized rank of the whole combination tends to `0`, and (S1) passes to the
     limit by subadditivity of rank.
3. **Cycle structure.** If `g^j != 1`, then `sigma_k(g)^j` is Hamming-close to `sigma_k(g^j)`, which moves almost
   every point. So the proportion of points on `sigma_k(g)`-cycles of length `l` tends to `0`:
   - for every `l` below the order of `g`;
   - for every bounded `l`, when `g` has infinite order.

   For finite order `n`, `sigma_k(g)^n` is close to the identity, so almost every point lies on an `n`-cycle.
4. **Ranks on a cycle.** On one `n`-cycle, `q(C_n)` is multiplication by `q` on `F[t]/(t^n - 1)`. Its kernel is the
   ideal generated by `(t^n - 1)/gcd(q, t^n - 1)`, of dimension `deg gcd(q, t^n - 1)`.
   - On an `l`-cycle, `rank q(C_l) >= l - deg q`. Averaging over the cycles gives the two formulas.
   - For `q = 1 - t`, `gcd(q, t^n - 1) = t - 1` has degree `1`.
   - This computes `q(sigma_k(g))`, while `sigma_k(q([g])) = sum_j q_j sigma_k(g^j)`. Their difference has normalized
     rank at most `sum_(q_j != 0) d_H(sigma_k(g^j), sigma_k(g)^j)`, which tends to `0` by step 3. So the values
     stand. ∎

**Theorem 1.2 (sofic configurations are inert).** Let `S ⊆ V` be finite with `K = <S>` sofic. Then no argument
confined to `S` concludes any of the following, for any `g` in `K`:
- `rk(1 - [g]) < 1 - 1/ord(g)`;
- `rk(q([g])) < 1 - deg gcd(q, t^n - 1)/n` for some `q != 0`, where `n = ord(g)`;
- that `rk` is the augmentation rank on `F[K]`, when `K != 1` (on `F[1] = F` that conclusion is true).

*Proof.* Restrict attention to matrices over `F[K]`; every premise and the conclusion only mention those.
- **(P1) and (P2)** hold for `rk_K`, since it is a rank function on `F[K]`.
- **(P3)** holds for `rk_K`: by Lemma 1.1, `rk_K(q([g]))` depends only on `q` and `ord(g)`, and elements conjugate
  in `V` have equal order.

So `rk_K` satisfies every premise, and by Lemma 1.1 it violates each conclusion. ∎

**Remark 1.3 (partial progress is blocked too).** A confined argument over a sofic configuration can't even prove
an upper bound `rk(1 - [g]) <= theta` with `theta < 1 - 1/ord(g)`. Every step of a gate proof that lowers
`rk(1 - [g])` below the sofic value has to go through a configuration that is not known to be sofic.

**Remark 1.4 (comparison with Proposition 3.2 of the fixed-rank artifact).**
- **That proposition:** covers amenable `H` together with tuple-level `V`-conjugacy premises for tuples in `H`,
  whose conjugators lie outside `H`. It imports Elek–Szabó uniqueness of sofic approximations of amenable groups.
- **Theorem 1.2:** needs no import, covers every sofic configuration, and allows single-element conjugacy with any
  conjugator.
- **Not covered by either:** tuple-level `V`-conjugacy of a non-amenable tuple whose conjugator, once added to `S`,
  makes `<S>` not known to be sofic.

**Remark 1.5 (the established V gate tools are sofic-shaped).** With `a_p = phi_V = 0`, `rk_K` satisfies on `K` the
conclusions of:
- the torsion law `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`, since finite subgroups act regularly;
- uniform displacement;
- `v-rank-models-act-freely-by-wandering-elements`, since infinite-order elements are free.

So quoting these theorems as premises doesn't escape Theorem 1.2 either, as long as the quoted instances concern
elements of `K`.

## 2. Instances inside V

### 2.1 Lamp configurations

**Proposition 2.1.** Let `x` in `V` have a nonempty clopen `W` with `x^j W`, `j` in `Z`, pairwise disjoint. Let `L`
be any subgroup of the rigid stabilizer `Rist_V(W)`, the elements supported in `W`. Then `<x, L> ≅ L wr Z`, the
restricted wreath product.

*Proof.*
- **The lamps.** `L_j = x^j L x^(-j)` is supported in `x^j W`. The supports are pairwise disjoint, so the `L_j`
  commute pairwise and generate their direct sum `⊕_j L_j`.
- **Normality.** `x` permutes the `L_j` by the shift, so this sum is normal in `<x, L>`, and
  `<x, L> = (⊕_j L_j)<x>`.
- **Trivial intersection.** Every element of the sum preserves each `x^j W`, while `x^k` with `k != 0` moves `W`
  off itself. So `<x>` meets the sum trivially.
- **Infinite order.** `x` has infinite order because the translates are disjoint. ∎

**Consequences.**
- **Finite or amenable `L`:** `L wr Z` is amenable, hence sofic, and Theorem 1.2 applies with no import. This covers
  every "mixed element of the lamp group `<x, g>`" with `g` supported in `W`, and every lamp configuration built
  from a finite subgroup of `Rist_V(W)`.
- **Sofic `L`:** `L wr Z` is sofic. This is imported at statement level, not re-read: Hayes–Sale, wreath products of
  a sofic group by an amenable group are sofic.

### 2.2 Free products and residually finite configurations

- **Sofic by standard facts:** residually finite implies LEF, and LEF implies sofic.
- **Free products:** by Gruenberg's theorem, free products of finite groups are residually finite. This is standard
  and was not re-read.
- **Consequence:** if `<S>` is isomorphic to `P_1 * ... * P_r` with finite `P_i`, or is residually finite or LEF,
  then Theorem 1.2 applies. Examples are pairs of clopen `p`-cycles that generate a free product, and depth-changing
  torsion pairs that do.
- **What stays uncovered** (Remark 1.4): using that a free-product tuple is `V`-conjugate to another tuple, through
  a conjugator that isn't in `S`.

### 2.3 Thompson's F

- **The subgroup:** `F = <x_0, x_1> <= V`.
- **If `F` is amenable** (`thompson-f-is-amenable`, OPEN): `F` is sofic, so every configuration inside `F` is inert,
  and so is every configuration inside an amenable extension of `F` in `V`.
- **So:** an argument confined to `F` that proves either gate would show that `F` is not sofic, which is stronger
  than non-amenability.

### 2.4 Live configurations after Section 1

A gate proof must contain a finitary step confined to some `S` with `<S>` not known to be sofic. Examples:
- `F` itself;
- Thompson's `T` and `V`;
- groups generated by `F` together with one clopen `p`-cycle;
- the two generators of `T`. By Lochak–Schneps, `T` is generated by an element of order `4` and one of order `3`;
  this presentation was not re-read.

Section 3 adds a second requirement that any such step must meet.

## 3. Characteristic-uniform arguments are inert

**Setting.**
- **Constants:** `R ⊆ C` is a subring, `F` a field, and `phi : R -> F` a ring homomorphism.
- **Matrix expressions:** built from symbols `[g]` (`g` in `V`), constants in `R`, sums, products and block
  matrices.
  - `E~` is the evaluation of an expression `E` in `R[V]`; `E_F` is its image in `F[V]` under `phi`.
  - Every argument with finitely many constants has such lifts. `F_p` is the image of `Z`, `F_q` the image of
    `Z[zeta_(q-1)]`, and transcendental constants lift to transcendentals.
- **`R`-uniform arguments.** An argument about a rank function on `F[V]` is *`R`-uniform* if its conclusion concerns
  values of `rk` on evaluated expressions `E_F`, and each premise is one of:
  - (U1) a Sylvester axiom, or a consequence of the axioms, applied to evaluated expressions;
  - (U2) an equality `E_1 = E_2` whose evaluations `E~_1 = E~_2` already hold in `R[V]`;
  - (U3) single-element conjugacy data `rk(q([g])) = rk(q([g']))`, with `q` in `R[t]` and `g, g'` conjugate in `V`.

**Theorem 3.1 (von Neumann rank; statement-level import of standard von Neumann dimension facts).**
- **The rank function.** For every group `G`, `C[G]` carries a Sylvester matrix rank function `rk_vN`: a matrix acts
  on powers of `l^2(G)`, and its rank is the trace of the projection onto the closure of its range.
- **Its values.** For nonzero `q` in `C[t]`:
  - if `g` has finite order `n`, `rk_vN(q([g])) = 1 - #{zeta : zeta^n = 1, q(zeta) = 0}/n`;
  - if `g` has infinite order, `rk_vN(q([g])) = 1`.

*Proof of the values.*
- **Finite order.** Put `e_zeta = (1/n) sum_j zeta^(-j) u_g^j`. Since `tau(u_h) = 0` for `h != 1`,
  `tau(e_zeta) = 1/n`. And `q(u_g) = sum_zeta q(zeta) e_zeta`, so its kernel projection is the sum of the `e_zeta`
  with `q(zeta) = 0`.
- **Infinite order.** The spectral measure of `u_g` at `delta_1` has moments `tau(u_g^j) = 0` for `j != 0`, so it is
  Haar measure. The kernel projection of `q(u_g)` is the spectral projection of a finite set, which has trace `0`. ∎

**Corollary 3.2 (uniform firewall).** Let `char F = p >= 0` and fix `R`, `phi`. No `R`-uniform argument concludes
`rk(1 - [g]) < 1 - 1/ord(g)` for some `g != 1`, or that `rk` is the augmentation rank on `F[K]` for a subgroup `K`
containing such a `g`.

*Proof.* Define `rho(E) = rk_vN(E~)` on expressions.
- (U1) holds for `rho`, because `rk_vN` is a rank function and evaluation respects sums, products and blocks.
- (U2) holds, because the equalities hold in `R[V] ⊆ C[V]`.
- (U3) holds, because by Theorem 3.1 `rk_vN(q([g]))` depends only on `q` and `ord(g)`.

The derivation only uses these premises, so it would conclude `rho(1 - [g]) < 1 - 1/ord(g)`. That contradicts
Theorem 3.1. ∎

**Corollary 3.3 (a proof must be `p`-sensitive).** A proof of V's rank gate over `F` with `char F = p > 0` must use an
equality between matrix expressions that holds in `F[V]` but fails in `R[V]` for the chosen lifts.
- **Examples:** for `s` of order `p`, `(1 - [s])^p = 0`. Over `C`, `(1 - u_s)^p` is nonzero on every eigenspace with
  `zeta != 1`. For `p = 2` this is `(1 + [t])^2 = 0` for an involution `t`.
- **So:** the decisive identity has to come from elements whose order is divisible by `p`, or from coefficients that
  vanish mod `p`.

**Corollary 3.4 (the established tools can't be the decisive step).** `rk_vN` on `C[V]` satisfies the conclusions of
all of these, each stated over any field:
- `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`, with `a = 0`, since `tau(e_chi) = 1/|P|`;
- `v-rank-torsion-constant-equals-global-fixed-rank`, both sides being `0`, since `l^2(V)` has no invariant vectors;
- `thompson-v-rank-models-displace-every-element-uniformly`;
- `v-rank-models-act-freely-by-wandering-elements`, where the ranks are `1`;
- the augmentation-or-detecting dichotomy, `rk_vN` being detecting.

So quoting them as premises, alongside uniform steps, doesn't escape Corollary 3.2. I haven't re-derived their
proofs. This corollary only checks that `rk_vN` satisfies their conclusions.

## 4. Both requirements, and the order-char cycle law

**Corollary 4.1.** Any proof of V's rank gate over `F` with `char F = p > 0` must do both of the following:
1. **Leave the sofic configurations.** Theorem 1.2 excludes every argument confined to a sofic configuration. So
   either the group generated by all elements the proof uses is not known to be sofic, or the proof uses tuple-level
   `V`-conjugacy through conjugators it doesn't include.
2. **Be `p`-sensitive.** By Corollary 3.3, it must use at least one equality that holds over `F` and not over the
   lifts.

The two requirements need not be met in the same step.

**The natural `p`-sensitive object** is a clopen `p`-cycle `s`, where `p = char F`. Put `y = 1 - [s]`. Then `y^p = 0`
in `F[V]`. All clopen `p`-cycles are conjugate in `V`.

**Proposition 4.2 (proved on paper).** Let `rk` be a rank function on `F[V]` with `char F = p > 0`, and put
`d_i = rk(y^i) - rk(y^(i+1))`.
- (a) `rk(y^j)` doesn't depend on which clopen `p`-cycle `s` is used.
- (b) `d_0 >= d_1 >= ... >= d_(p-1) >= 0`, and `sum_(i<p) d_i = 1`.
  - Monotonicity is the Frobenius inequality with `A = C = y` and `B = y^i`.
  - The sum is `1` because `y^p = 0`.
- (c) `rk(y^j) <= (p - j)/p`, and `rk(y) <= 1 - phi_V`.
  - The first holds because the last `p - j` terms of a non-increasing sequence have average at most the overall
    average `1/p`.
  - For the second, `1 - [ab] = (1 - [a]) + [a](1 - [b])` and `1 - [a^(-1)] = -[a^(-1)](1 - [a])`. So `1 - [s]` is a
    combination of the `1 - [s_i]` over a generating set, and its rank is at most `rk col(1 - [s_i]) = 1 - phi_V`.
  - Combining them: for `j >= 1`, the last `p - j` of the `p - 1` drops `d_1, ..., d_(p-1)`, whose sum is
    `rk(y) <= 1 - phi_V`, give `rk(y^j) <= (1 - phi_V)(p - j)/(p - 1)`.
- (d) **Calibration.** Both the augmentation rank and the sofic values of Lemma 1.1 satisfy
  `rk(y^j) = (1 - phi)(p - j)/p` for `1 <= j <= p`, with `phi = 1` and `phi = 0` respectively. At `j = 0` every rank
  function gives `1`. Sofic values give `1 - deg gcd((1-t)^j, (t-1)^p)/p = 1 - j/p`.
  Over `C`, `rk_vN((1 - u_s)^j) = (p - 1)/p` for every `j >= 1`, so the pattern is genuinely `p`-sensitive.

**Open (the order-char cycle law).** Does every rank function on `F[V]` satisfy `rk(y^j) = (1 - phi_V)(p - j)/p` for
`1 <= j <= p`? Equivalently `d_0 = phi_V + (1 - phi_V)/p` and `d_i = (1 - phi_V)/p` for `1 <= i < p`: weight `phi_V`
of the trivial module plus weight `1 - phi_V` of the regular module. (The first version of this section wrote
`0 <= j <= p`, which fails at `j = 0` whenever `phi_V > 0`.) This is the `p = char F` analogue of the torsion law, and
would be the first `p`-sensitive structure theorem on V's rank functions.
- **What single-level data allow.** For `p >= 3`, finite data at one tree level can't force it. Take
  `A = F_p[(Z/p)^r]` with augmentation ideal `m`. On `A/m^2` every nonidentity element acts with Jordan type
  `[2, 1^(r-1)]`, giving ranks `1/(r+1)` and `0`, and those ranks are the same for every clopen `p`-cycle in the
  level.
- **Why that example isn't a counterexample.** Its normalized rank `1/(r+1)` changes with `r`. So it isn't compatible
  with the tree embeddings `E_r ⊆ E_(r')` inside `V`.
- **The open question:** whether tree-compatibility across all levels, together with `V`'s depth-changing elements,
  forces the law.

## 5. Where it stops

- **No decision.** I found no rank identity in a non-sofic configuration that forces `a_p = phi_V = 1`, and no
  construction of a non-augmentation rank function on `F[V]`.
- **What a proof must still use** (Corollary 4.1):
  - a configuration not known to be sofic, or tuple-level `V`-conjugacy of non-amenable tuples through outside
    conjugators;
  - a `p`-sensitive identity.
- **First live configurations meeting both:**
  - the Lochak–Schneps generators of `T`, of orders `4` and `3`, which carry `2`- and `3`-torsion (presentation not
    re-read);
  - `<x_0, x_1, t>` with `t` a clopen transposition, in characteristic `2`;
  - `<x_0, x_1, s>` with `s` a clopen `3`-cycle, in characteristic `3`.

  In each, `(1 - [s])^p = 0` has to be combined with relations of the non-sofic-known group generated.
- **Open node:** `v-rank-order-char-cycles-are-trivial-plus-regular`. Its proved parts (a)–(d) and the
  single-level calibration are recorded there.
