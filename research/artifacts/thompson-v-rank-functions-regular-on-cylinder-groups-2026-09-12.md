# Rank functions on F[V] are trivial plus regular on finite cylinder groups

Lane `w7-v-cycle-c2`, 2026-09-12. **Verified** by `w3-vf-linear` (PASS on ce8be16cd1, Section 32 of
`research/artifacts/w3-vf-linear-verification-2026-09-12.md`).
Everything is for ABSTRACT Sylvester matrix rank functions over any field. Nothing here decides a gate.

Cited:
- [TS] `research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md`, Theorem 1.3
  (`v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`), valid abstractly by [FR] Section 3.1.
- [FR] `research/artifacts/thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`: Section 0
  ((S1)–(S6), scalar extension, fixed rank) and Theorem 1.2 (`v-rank-torsion-constant-equals-global-fixed-rank`).
- [FW] `research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md`.

## 0. Setting and results

- `X = {0,1}^N`, `V` acting by prefix replacement, `F` any field, `rk` a Sylvester matrix rank function on
  `R = F[V]`, and `phi = phi_V = 1 - rk col(1 - [s] : s in S)` for a finite generating set `S`.
- **Cylinder group.** A finite subgroup `G <= V` together with a finite partition `Pi` of `X` into cylinders
  such that every `g in G` maps each `[u] in Pi` onto some `[v] in Pi` by `uw -> vw`. So `G` permutes `Pi`. An
  element mapping `[u]` to itself is the identity on `[u]`, so `G` acts faithfully on `Pi`.
- **Examples.** A cylinder model of a clopen `p`-cycle, for every prime `p`; since all clopen `p`-cycles are
  conjugate, every clopen `p`-cycle is conjugate to one. Also disjoint tuples of clopen transpositions, the
  dihedral configurations of Section 2, and `Sym(Pi_k)` for the partition `Pi_k` into level-`k` cylinders.
- **Regular rank.** For `A in M_n(F[G])` write `A = sum_x a_x [x]` with `a_x in M_n(F)`, and set
  `eps(A) = sum_x a_x` and `Reg(A) = (a_(g h^-1))_(g,h in G) in M_(n|G|)(F)`. `Reg(A)` is the matrix of left
  multiplication by `A` on `F[G]^n` in the basis `[g]`.

**Theorem 1.1.** For every cylinder group `G` and every `A in M_n(F[G])`,

```text
rk(A) = phi_V rank_F eps(A) + (1 - phi_V) rank_F Reg(A) / |G|.
```

On every cylinder group, a rank function on `F[V]` is a fraction `phi_V` of the augmentation rank plus a
fraction `1 - phi_V` of the regular rank. This holds in every characteristic, including primes dividing `|G|`.

**Corollary 1.2 (order-characteristic law).** Let `char F = p > 0` and `s` a clopen `p`-cycle. Then for
`1 <= j <= p`, `rk((1 - [s])^j) = (1 - phi_V)(p - j)/p`. In characteristic two, `rk(1 + [t]) = (1 - phi_V)/2`
for every clopen transposition `t`.

*Proof.* Conjugate `s` to a cylinder model (S1) and take `G = <s>`. Then `eps((1 - [s])^j) = 0`. In
`F[Z/p] = F[y]/(y^p)` with `y = 1 - [s]`, left multiplication by `y^j` has rank `p - j`. Theorem 1.1 gives
`(1 - phi_V)(p - j)/p`. ∎

This proves `v-rank-order-char-cycles-are-trivial-plus-regular` for every prime (verified by `w3-vf-linear`, Section 32).

**Other sections.**
- Section 2 is a character-free cross-check for transpositions in characteristic two, through dihedral groups.
- Section 3 is a calibration. Invariance under disjoint-support endomorphisms on `F_2[E_infinity]` can't prove
  Corollary 1.2: some rank function invariant under every injective endomorphism violates it.
- Section 4 covers what this means for the binary gate, and where it stops.

## 1. Proof of Theorem 1.1

**Sylvester facts used**, beyond [FR] (S1)–(S6):
- (S3') **Corner additivity.** If `f` is an idempotent, `a = f a f` and `b = (1 - f) b (1 - f)`, then
  `rk(a + b) = rk(a) + rk(b)`. The proof is as for (S3): `a + b = (1 1) diag(a, b) (1 1)^T`, and
  `diag(a, b) = (f; 1 - f)(a + b)(f, 1 - f)`. By induction, if orthogonal idempotents `f_i` sum to `1` and commute
  with the entries of a matrix `A`, then `rk(A) = sum_i rk(f_i A)`.
- (S7) **Sylvester nullity in a corner.** If `a, b in f R f`, then `rk(ab) >= rk(a) + rk(b) - rk(f)`. Apply
  `rk(AB) >= rk(A) + rk(B) - 1` to `a + 1 - f` and `b + 1 - f`, whose product is `ab + 1 - f`, and use (S3'). The
  inequality itself follows from the axiom `rk [[A, 0], [1, B]] >= rk A + rk B`, since that matrix is equivalent to
  `[[0, -AB], [1, 0]]`. Only Section 2 uses (S7).

**Step 1: an auxiliary cycle group.** Fix an odd prime `p != char F`. In each `G`-orbit on `Pi`, pick one
cylinder `[u]` and `p` disjoint cylinders inside `[u0]`. Let `c_u` be a clopen `p`-cycle that permutes them by
prefix replacement and fixes everything else. For `[v] = g[u]`, set `c_v = g c_u g^(-1)`. This is well defined:
if `g[u] = g'[u]`, then `g^(-1) g'` is the identity on `[u]`, which contains the support of `c_u`.
- `c_v` is supported in `[v0]`, since `g` maps `[u0]` onto `[v0]` by prefix replacement. So the `c_v` commute,
  and `Q = <c_v : [v] in Pi>` is isomorphic to `(Z/p)^Pi`.
- `[h] c_v [h]^(-1) = c_(hv)` for `h in G`. So `G` normalizes `Q` and permutes its coordinates.
- Every nonidentity `q = prod_(v in T) c_v^(a_v)`, with `T` nonempty and every `a_v` nonzero mod `p`, is a clopen
  `p`-cycle. Let `B_v` be one of the cylinders moved by `c_v`. Then `q` maps
  `C_j = union_(v in T) c_v^(j a_v)(B_v)` onto `C_(j+1)`. The `C_j` for `j in Z/p` are disjoint and nonempty, and
  `q` fixes their complement, which contains every `[v1]`. So `Q` is a clopen-cycle subgroup in the sense of [TS].

**Step 2: characters.** Let `F' = F(mu_p)`, and let `rk'` be the scalar extension of [FR] Section 0. It agrees
with `rk` on matrices over `F`, so it has the same `phi_V`. For a character `chi : Q -> mu_p(F')`, set
`e_chi = p^(-|Pi|) sum_(q in Q) chi(q)^(-1) [q]`. By [TS] Theorem 1.3 and [FR] Theorem 1.2,

```text
rk'(e_chi) = phi [chi = 1] + (1 - phi) p^(-|Pi|).
```

- `G` acts on characters by `(g chi)(q) = chi(g^(-1) q g)`, and `[g] e_chi [g]^(-1) = e_(g chi)`.
- For a `G`-orbit `O` of characters, `f_O = sum_(chi in O) e_chi` is an idempotent commuting with `F'[Q]` and with
  every `[g]`. So it commutes with every matrix over `F[G]`. The `f_O` are orthogonal and sum to `1`.
- `e = e_1 = |Q|^(-1) sum_q [q]` is defined over `F`.

**Step 3: the trivial character.** *Claim:* `rk col(e(1 - [g]) : g in G) <= rk(e) - phi = (1 - phi) p^(-|Pi|)`.
Let `Y = {1 - [c_v]} ∪ {1 - [g] : g in G}` and `Y' = {1 - e} ∪ {e(1 - [g]) : g in G}`.
- (a) `rk col(Y) <= 1 - phi`. Every element of `Y` lies in the augmentation ideal of `F[V]`, which is the left
  ideal generated by the `1 - [s]`, `s in S`. Apply (S5), then delete rows.
- (b) `Y` and `Y'` generate the same left ideal of `R`, so `rk col(Y) = rk col(Y')` by (S5).
  - `Y'` from `Y`: `1 - e = |Q|^(-1) sum_q (1 - [q])`, and each `1 - [q]` lies in the left ideal of the `1 - [c_v]`.
    Also `e(1 - [g]) = (1 - [g]) - (1 - [g])(1 - e)`, since `e` commutes with `[g]`.
  - `Y` from `Y'`: `1 - [c_v] = (1 - [c_v])(1 - e)` and `1 - [g] = e(1 - [g]) + (1 - [g])(1 - e)`.
- (c) `rk col(Y') = rk(1 - e) + rk col(e(1 - [g]))`. With `C = col(Y')`, `C (1 - e, e)` is the block matrix
  `diag(1 - e, col(e(1 - [g])))`, because `e(1 - [g])(1 - e) = 0`. And `diag(1 - e, col(e(1 - [g]))) (1; 1) = C`.
- (d) `rk(1 - e) = 1 - rk(e)` by (S3). So `rk col(e(1 - [g])) <= (1 - phi) - (1 - rk e) = rk(e) - phi`.

*Consequence.* Let `A in M_n(F[G])`.
- The entries of `A - eps(A)` lie in the augmentation ideal of `F[G]`, the left ideal generated by the `1 - [g]`.
  So `A - eps(A) = B (I_n ⊗ col(1 - [g] : g in G))` with `B` over `F[G]`.
- Since `e` commutes with `B`, `e(A - eps(A)) = B (I_n ⊗ col(e(1 - [g])))`, of rank at most `n (1 - phi) p^(-|Pi|)`.
- `rk(e eps(A)) = rk(e) rank_F eps(A)` by (S1) and (S3).

By (S2),

```text
| rk'(eA) - phi rank_F eps(A) | <= 2 n (1 - phi) p^(-|Pi|).
```

**Step 4: free nontrivial orbits.** Call `chi` *free* if `chi != 1` and `g chi != chi` for every `g != 1`. For a free orbit `O` containing
`chi` and `A in M_n(F[G])`,

```text
rk'(f_O A) = rk'(e_chi) rank_F Reg(A).
```

- For `x in G`, `e_chi [x] = [x] e_(x^(-1) chi)`, so `e_chi [x] e_chi = [x = 1] e_chi`.
- Let `Cc = col_(g in G)(e_chi [g]^(-1))` and `Rr = row_(g in G)([g] e_chi)`. Then `Rr Cc = sum_g e_(g chi) = f_O`,
  and `Cc Rr = (e_chi [g^(-1) h] e_chi)_(g,h) = I_|G| ⊗ e_chi`. Hence `Cc Rr Cc = Cc` and `Rr Cc Rr = Rr`.
- Put `Â = (I_n ⊗ Cc) A (I_n ⊗ Rr)`. Its `((i,g),(j,h))` entry is `sum_x (a_x)_(ij) e_chi [g^(-1) x h] e_chi`,
  which equals `(a_(g h^-1))_(ij) e_chi`. So `Â = Reg(A) ⊗ e_chi`, of rank `rank_F Reg(A) rk'(e_chi)` by (S1) and (S3).
- `f_O A = f_O A f_O = (I_n ⊗ Rr) Â (I_n ⊗ Cc)`, and `Â = (I_n ⊗ Cc)(f_O A)(I_n ⊗ Rr)`. So `rk'(f_O A) = rk'(Â)`.

**Step 5: counting.** If `G = 1` the claim is (S1), so let `|G| >= 2`. A character fixed by some `g != 1` is
constant on the `g`-orbits in `Pi`. Since `g` moves some cylinder, it has at most `|Pi| - 1` orbits there. So at most
`(|G| - 1) p^(|Pi| - 1)` characters are fixed by some `g != 1`. The trivial character is one of them, and every other
character is free.
By (S3'),

```text
rk(A) = rk'(eA) + sum_(O free) rk'(f_O A) + sum_(O not free, O != {1}) rk'(f_O A).
```

- **Free nontrivial orbits.** They contribute `(N_free/|G|)(1 - phi) p^(-|Pi|) rank_F Reg(A)`, with
  `p^|Pi| - (|G| - 1) p^(|Pi| - 1) <= N_free <= p^|Pi|`. Since `rank_F Reg(A) <= n|G|`, this is
  `(1 - phi) rank_F Reg(A)/|G|` up to `n(|G| - 1)/p`.
- **Non-free nontrivial orbits.** `rk'(f_O A) <= n rk'(f_O)`, and in total this is at most `n(1 - phi)(|G| - 1)/p`.
- **Trivial orbit.** Step 3.

Adding the three errors `2n/p`, `n(|G| - 1)/p` and `n(|G| - 1)/p` gives
`| rk(A) - phi rank_F eps(A) - (1 - phi) rank_F Reg(A)/|G| | <= 2 n |G| / p`. The left side does not depend on `p`,
and `p` ranges over infinitely many primes. ∎

**Remarks.**
- **Inputs.** Only [TS] Theorem 1.3 for the elementary abelian group `Q`, [FR] Theorem 1.2, and the Sylvester
  axioms. There is no matricial step.
- **Scope.** Every finite subgroup `H <= V` is a cylinder group, with the coarsest partition `P_H` of
  `finite-subgroups-of-thompson-v-permute-a-canonical-partition` (ESTABLISHED). So Theorem 1.1 covers every
  finite subgroup of `V`. The proof uses the partition only to build a group `Q` that `G` normalizes, with `G`
  acting faithfully on its coordinates.
- **Consistency.**
  - It agrees with [TS] Proposition 2.1: the trivial-plus-regular model of a finite subgroup meets every
    conjugacy constraint.
  - It agrees with the sofic firewall [FW]: ultraproduct permutation-module ranks are regular on finite subgroups.
  - It does not conflict with `thompson-v-rank-models-through-displacing-sym-reps-are-trivial`. That theorem
    concerns the stage maps of an approximation, not restrictions to finite subgroups of `V`.

## 2. Cross-check in characteristic two, without characters

Let `char F = 2` and let `q` be an odd prime.
- Take disjoint cylinders `[w_0], ..., [w_(q-1)]` with nonempty complement `D`.
- `c : w_i x -> w_(i+1) x` (indices mod `q`) fixes `D`. It is a clopen `q`-cycle.
- `t : w_i x -> w_(-i) x` fixes `[w_0] ∪ D`. It swaps `union_(1 <= i <= (q-1)/2) [w_i]` with `union [w_(-i)]`, so it
  is a clopen transposition, and `t c t = c^(-1)`.
- `e = sum_(i=0)^(q-1) [c]^i`. Since `q = 1` in `F`, `e^2 = e` and `e = e_1` for `P = <c>`. So
  `rk(e) = phi + (1 - phi)/q` by [TS] Theorem 1.3 and [FR] Theorem 1.2. Also `[t] e [t] = e`.
- `x = 1 + [t]` and `r = rk(x)`. By conjugacy `r` does not depend on the clopen transposition.

**Lower bound.** Let `u = sum_(i=1)^((q-1)/2) [c]^i` and `u' = [t] u [t] = sum_(i=1)^((q-1)/2) [c]^(-i)`. Then
`u x = u + u[t]` and `x u' = u' + u[t]`. So `u x + x u' = u + u' = 1 + e = 1 - e`, and
`(1 - phi)(q - 1)/q = rk(1 - e) <= 2r`.

**Upper bound.**
- `x` commutes with `e`, so `r = rk((1 - e)x) + rk(ex)` by (S3').
- `y = (1 - e)x` lies in the corner `(1 - e)R(1 - e)` and `y^2 = (1 - e)x^2 = 0`. By (S7), `rk(y) <= rk(1 - e)/2`.
- `{1 - [c], x}` and `{1 - e, ex}` generate the same left ideal:
  - `1 - e = sum_(i=0)^(q-1) (1 - [c]^i)` (using `q = 1`) and `ex = x - x(1 - e)`;
  - `1 - [c] = (1 - [c])(1 - e)` and `x = ex + x(1 - e)`.
- As in Step 3(c), `rk col(1 - e, ex) = rk(1 - e) + rk(ex)`. This is at most `1 - phi`, so `rk(ex) <= (1 - phi)/q`.

So `(1 - phi)(q - 1)/(2q) <= r <= (1 - phi)(q + 1)/(2q)`. Let `q -> infinity`: `r = (1 - phi)/2`, which is
Corollary 1.2 for `p = 2`. The only inputs are [TS] Theorem 1.3 for the cyclic group `<c>` and [FR] Theorem 1.2.

## 3. Calibration: invariance inside the 2-group does not force the law

The law node's next test asks whether a rank function on `F_2[E_infinity]` can be invariant under every
disjoint-support endomorphism without being trivial plus regular. It can.

**Construction.**
- `E_infinity = ⊕_(i >= 1) Z/2` with basis `t_i` and `t_S = prod_(i in S) t_i`.
- `K = F_2(lambda_1, lambda_2, ...)` is purely transcendental, and `N = e_12 in M_2(K)`.
- `rho(t_i) = 1 + lambda_i N`. Since `N^2 = 0`, `rho(t_S) = 1 + lambda_S N` with `lambda_S = sum_(i in S) lambda_i`. So
  `rho : E_infinity -> GL_2(K)` is an injective homomorphism.
- `rk_lambda(A) = rank_K rho(A)/2` is a Sylvester matrix rank function on `F_2[E_infinity]`.

**Properties.**
- **Invariance.**
  - Let `sigma` be an injective endomorphism, `sigma(t_i) = t_(S_i)` with the `S_i` linearly independent over `F_2`.
  - The `mu_i = lambda_(S_i)` are linearly independent linear forms, so they are algebraically independent.
  - For `A` involving `t_1, ..., t_m`, the map `lambda_i -> mu_i` extends to a field embedding
    `iota : F_2(lambda_1, ..., lambda_m) -> K` with `rho(sigma(A)) = iota(rho(A))`. Field embeddings preserve rank.
  - Disjoint-support endomorphisms are the case of disjoint `S_i`.
- **The identity holds.** `rk_lambda(1 + [t_S]) = rank(lambda_S N)/2 = 1/2` for every `S != ∅`. So
  `rk_lambda(x_1 + x_2) = rk_lambda(x_1)`.
- **Not trivial plus regular.**
  - `col(1 + [t_i] : i <= k)` maps to `col(lambda_i N)`, of rank `1`. So the joint fixed rank of
    `E_k = <t_1, ..., t_k>` is `1/2` for every `k`.
  - A trivial-plus-regular function with constant `alpha` has `rk(1 + [t_1]) = (1 - alpha)/2` and joint fixed rank
    `alpha + (1 - alpha)/2^k`.
  - The first forces `alpha = 0`. Then the second is `2^(-k)`, which is not `1/2` for `k >= 2`.

**Which premise it breaks.** Realize `E_k` in `V` by `k` disjoint clopen transpositions with nonempty complement. By
Theorem 1.1 every rank function on `F_2[V]` restricts to a trivial-plus-regular one on `F_2[E_k]`, so `rk_lambda`
is the restriction of none. The first premise of Section 1 that no extension can meet is Step 2 for `G = E_k`: an
odd-cycle group `Q` normalized by `E_k` and obeying the torsion law. So a proof of the law from inside the 2-group
can't work.

## 4. What this does to the binary gate, and where it stops

**4.1 Torsion is spent, 2-torsion included.**
- **Determined by `phi_V`.** By Theorem 1.1 and the Scope remark, a rank function on `F[V]` is determined on every
  finite subgroup by the one number `phi_V`. The same holds on every locally finite subgroup, since a matrix involves
  finitely many elements.
- **These values are already sofic.** They are `phi_V` times the augmentation rank plus `1 - phi_V` times a
  permutation-module rank. So by `sofic-configurations-cannot-force-v-rank-triviality`, no argument confined to such
  subgroups and conjugacy between their elements can force the gate.
- **The gate's open item.** This settles `v-rank-order-char-cycles-are-trivial-plus-regular`. The 2-sensitive
  identity `(1 + [t])^2 = 0` gives exactly `rk(1 + [t]) = (1 - phi_V)/2`, the mixed sofic value, and nothing more.

**4.2 The gate in terms of `phi_V`.** Let `sigma : V -> M^x` be a model over a field of characteristic two, with
`rk_sigma(A) = rk(sigma(A))`.
- **Local formula.** `phi_V(rk_sigma) = 1 - 2 rk(1 + sigma(t))` for every clopen transposition `t`.
- **Convexity.**
  - Block sums `diag(I, sigma)` in larger ultraproducts realize `beta rk_aug + (1 - beta) rk_sigma` for every
    `beta in [0, 1]`, and `phi_V` is affine.
  - So a nontrivial model yields models with every value of `phi_V` in `[phi_V(rk_sigma), 1]`. The gate is equivalent
    to `phi_V in {0, 1}` for every model.
  - Asking whether the law plus `x_0`, `x_1`-conjugation forces `phi_V in {0, 1}` is asking the gate itself. The law
    carries no information beyond `phi_V`.
- **Reduced models.** By [FR] Corollary 1.3(5) ([matricial]), a nontrivial model compresses to a nontrivial model with
  `phi_V = 0`. By Theorem 1.1 that model is regular on every finite subgroup. So the gate is equivalent to each of:
  - no characteristic-two model of `V` has `rk(1 + sigma(t)) = 1/2`;
  - no characteristic-two model of `V` restricts to the regular rank on every finite subgroup.
- **Abstract compression is open.**
  - On each finite subgroup, Theorem 1.1 gives `rk = phi_V rk_aug + (1 - phi_V) rk_reg`, with both terms rank
    functions.
  - It is not known whether an abstract `rk` on `F[V]` splits globally as `phi_V rk_aug + (1 - phi_V) rk_0` with
    `rk_0` a rank function. Corollary 1.3(5) needs an idempotent generating the fixed ideal.

**4.3 Where it stops.** A proof of the gate must use all three of these:
- infinite-order elements, because finite and locally finite subgroups are spent (4.1);
- a configuration not known to be sofic, by the sofic firewall;
- 2-torsion, by `char-uniform-identities-cannot-force-v-rank-triviality`.

The first live configuration is still `<x_0, x_1, t>` ([FW] Section 5). By 4.2 and
`v-rank-models-act-freely-by-wandering-elements`, a counterexample may be sought among models that are regular on
all finite subgroups and free on wandering elements. This is not decided here.

**4.4 Characteristic three** (for `w7-v-cycle-c3`; not pursued here).
- Corollary 1.2 with `p = 3` gives `rk((1 - [s])^j) = (1 - phi_V)(3 - j)/3` for clopen 3-cycles.
- Abstract rank functions on `F_3[V]` form a convex set containing the augmentation rank. So
  `thompson-v-ternary-rank-functions-are-augmentation` is equivalent to `phi_V in {0, 1}` for every abstract `rk`,
  with `phi_V = 1 - (3/2) rk(1 - [s])`.

**Status.** `w3-vf-linear` re-derived Theorem 1.1, Corollary 1.2, and Sections 2 and 3 (PASS, Section 32 of
`research/artifacts/w3-vf-linear-verification-2026-09-12.md`). Theorem 1.1 is ESTABLISHED through route
`v-rank-trivial-plus-regular-on-cylinder-groups-proof` and Corollary 1.2 through `v-rank-order-char-cycle-law-proof`.
Section 4 only reorganizes the gate and decides nothing. Both gates stay OPEN.
