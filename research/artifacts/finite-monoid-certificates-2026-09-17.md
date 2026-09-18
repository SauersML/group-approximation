# Finite-monoid certificates for Bernoulli witness patterns

Agent swarm-0917-w11-w11-gs-pull, 2026-09-17. Target `every-group-has-positive-rokhlin-entropy-action`,
role obstruction-miner, family finite-models.

**Summary.**
- Theorem M: if the partial multiplication table of a witness pattern, restricted to the products
  the configuration uses, embeds injectively into a finite monoid, then `Phi >= log q`. Letters may map
  to non-invertible elements, so this is not a local embedding into finite groups.
- Theorem M' (converse): the finite functional models of Lemma 1 whose coincidences hold at every point
  certify exactly these patterns. So Theorem M is the full reach of exact finite models.
- Corollary A: Theorem A of `height-graded-germ-models-2026-09-17.md` (finite-core height potentials) is
  a special case, via a transformation monoid with a sink.
- Proposition R: for read-complete patterns (every letter in a read pair) Theorem M collapses to local
  embedding into finite groups. So the monoid gain sits entirely on the non-read letters.
- Corollary R: every configuration over `G` is finite-monoid embeddable if and only if `G` is LEF.
  So exact finite models prove nothing at group level beyond LEF. Their gain over finite groups is
  per pattern.
- Filter and kill: every deficit witness has a Q-table that is not finite-monoid embeddable. Any
  finite-model certificate for such a table is non-exact. At every finite stage, no invariant set of
  points containing a good point carries the relations identically.

Notation follows `bernoulli-rokhlin-deficit-has-a-finitary-witness` and the germ-model artifact:
- `G` is a countable group, and `(k, E, F, psi)` is a configuration with `psi` valued in a finite `R`.
- `Phi = (1/k)[H(psi(x|_E)) + H(x(1) | y_F)]`, where `y_f = psi((x(fe))_(e in E))` and `x` is iid
  uniform on `A^k`, with `|A| = q`.
- `Q = {1} ∪ E ∪ FE`.

An *expression* is one of the formal symbols `1`, `e` (for `e in E`) or `fe` (for `f in F`, `e in E`).
Each expression names an element of `Q`.

## 1. Tables and certificates

**Definition (Q-table embedding).** Let `M` be a finite monoid. A *Q-table embedding* is a map
`lambda : E ∪ F -> M` such that the rule

    [1] = 1_M,   [e] = lambda(e),   [fe] = lambda(f) lambda(e)

is well defined as a function `[·] : Q -> M`, and that function is injective. Well defined means that
two expressions naming the same element of `G` get the same value in `M`. The conditions include:
- `lambda(f)lambda(e) = lambda(f')lambda(e')` whenever `fe = f'e'`;
- `lambda(f)lambda(e) = lambda(e')` whenever `fe = e'`;
- `lambda(f)lambda(e) = 1_M` whenever `fe = 1`;
- `lambda(e) = 1_M` if `e = 1`.

Injective means that distinct elements of `Q` get distinct values. Nothing is required of letters
`f in F` beyond their products, so `lambda|_F` may be non-injective.

*Convention.* Here `E ∪ F` means the disjoint union `E ⊔ F`. A group element lying in both `E` and
`F` has an `E`-copy and an `F`-copy, and `lambda` may give them different values. The same convention
applies to the maps `phi_u` below, to the letter heights in Section 4, and to `T_f`, `S_e` in Lemma 1.
If `1 in E`, the `F`-copy of any `f` is forced: `[f] = [f · 1] = lambda(f) 1_M`.

**Definition (pointed act).** Equivalently, a *finite certificate* is a finite set `Y`, maps
`phi_u : Y -> Y` for `u in E ∪ F`, and a point `y_0 in Y` such that:
- (W) the rule `[1] = id`, `[e] = phi_e`, `[fe] = phi_f ∘ phi_e` is a well-defined function from `Q` to
  the maps `Y -> Y`, with equality meaning equality at every point of `Y`;
- (I) `q -> [q](y_0)` is injective on `Q`.

The two notions are equivalent:
- A Q-table embedding gives a certificate with `Y = M`, `phi_u(m) = lambda(u) m` and `y_0 = 1_M`.
- A certificate gives a Q-table embedding into the finite monoid of self-maps of `Y` under composition,
  with `lambda(u) = phi_u`. Here (I) forces injectivity of `[·]`, since maps that differ at `y_0` differ.

Say a pattern is *finite-monoid embeddable* when it has a Q-table embedding.

## 2. Theorem M

**Lemma 1 (functional count; Section 1 of `height-graded-germ-models-2026-09-17.md`, restated with
proof).** Let `X` be a finite set with arbitrary maps `T_f : X -> X` (`f in F`) and `S_e : X -> X`
(`e in E`). Call `w` *good* when the rule `1 -> w`, `e -> S_e w`, `fe -> S_e T_f w` is a well-defined
injective map `chi_w : Q -> X`. If a `beta`-fraction of `X` is not good, then

    log q <= Phi + beta (log|R|/k + log q).

*Proof.* Put `x` iid uniform on `A^k` over `X` and `c(w) = psi((x(S_e w))_(e in E))`. Since `c` is a
function of `x`, subadditivity and dropping conditioning give

    k|X| log q = H(x) <= sum_w H(c(w)) + sum_w H(x(w) | (c(T_f w))_(f in F)).

At a good `w`, the variables `c(w)`, `x(w)` and `c(T_f w)` are the same functions of iid values at the
points `chi_w(q)` as `psi(x|_E)`, `x(1)` and `y_f` are of the values at `q in G`. Those points coincide
exactly as the elements of `Q` do. So the two terms of `w` sum to `k Phi`. At a bad `w`, bound them by
`log|R| + k log q`. Divide by `k|X|`. ∎

**Theorem M.** If the pattern of `(k, E, F, psi)` is finite-monoid embeddable, then `Phi >= log q`.
This holds for every countable group `G`, with no assumption on `G` or on `<E ∪ F>`.

*Proof.* Take a finite certificate `(Y, phi, y_0)` as in Section 1, and fix `N >= 2`.

*Model.* Put `X = [N]^Y`, and define `(T_f c)(y) = c(phi_f y)` and `(S_e c)(y) = c(phi_e y)`.

*Exact coincidences.* For every `c in X`:
- `S_e T_f c = (T_f c) ∘ phi_e = c ∘ phi_f ∘ phi_e = c ∘ [fe]`;
- `S_e c = c ∘ [e]`;
- `c = c ∘ [1]`.

By (W) the rule `q -> c ∘ [q]` is a well-defined function on `Q`, at every point `c`. So `c` is good
exactly when that function is injective.

*Separation.* Take `q != q'` in `Q`. By (I), `[q](y_0) != [q'](y_0)`. So `c ∘ [q] = c ∘ [q']` forces
`c([q] y_0) = c([q'] y_0)`, which has probability `1/N` for uniform `c`. A union bound gives

    beta <= C(|Q|, 2) / N.

*Conclusion.* Lemma 1 gives `log q <= Phi + (|Q|^2 / 2N)(log|R|/k + log q)`. Let `N -> infinity`. ∎

**Remarks.**
1. *No padding.* The relations are exact at every point of `X`, not just at a top level. So there are
   no junk points or level-counting, unlike the germ model of Theorem A.
2. *Associativity is used.* It enters only through `phi_f ∘ phi_e`, a composition of maps.
   `research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md` records patterns realized in
   finite loops with small value at a special site, in the Rokhlin-window setting. That setting
   differs, so no claim is made here about loop models of `Phi`.

## 3. Theorem M' (converse): exact finite models are exactly finite-monoid embeddings

Call a finite model `(X, T_f, S_e)` *exact* when, for every two expressions naming the same element of
`Q`, the corresponding maps (`id`, `S_e`, or `S_e ∘ T_f`) agree at every point of `X`.

**Theorem M'.** If the pattern has an exact finite model with at least one good point, then it is
finite-monoid embeddable.

*Proof.* Let `M` be the monoid of self-maps of `X` with the opposite product `a * b = b ∘ a`. It is
finite. Put `lambda(f) = T_f` and `lambda(e) = S_e`. Then
- `[fe] = lambda(f) * lambda(e) = S_e ∘ T_f`;
- `[e] = S_e`;
- `[1] = id`.

Exactness says `[·]` is well defined on `Q`. At a good `w`, the points `[q](w)` are pairwise distinct,
so the maps `[q]` are pairwise distinct. ∎

The same holds if exactness is only asked on a subset of `X` that is invariant under all `T_f` and
`S_e` and contains a good point. Restrict to that subset.

**Consequence.** Theorem M is the full reach of exact finite models. A pattern that is not
finite-monoid embeddable has no exact finite model with a good point. Any finite-model certificate for
it must be approximate. At each finite stage, no subset that is invariant under all the maps and
contains a good point has the relations holding identically on it.

## 4. Corollary A: finite-core height potentials

**Corollary A** (Theorem A of `height-graded-germ-models-2026-09-17.md`). Suppose the pattern admits a
height potential `(a, b)` whose core `K_Z` is finite. Then it is finite-monoid embeddable, and so
`Phi >= log q`.

*Proof.* Use the notation of Theorem A:
- `K = <E ∪ F>` with word length for `E ∪ F`;
- `D = max_(K_Z) |·|` and `mu = 1 + D`;
- `R_r = K_Z B(r)`, which is finite because `K_Z` and `B(r)` are finite;
- `L = mu max_Q ht`;
- `t(u)` is the height of the letter `u`: `a(u)` for `u in F`, `b(u)` for `u in E`.

*The act.* Let `Y = {⊥} ⊔ ⊔_(0<=r<=L) {r} × R_r`, and put `phi_u(⊥) = ⊥`. For a point `(r, g)`:
- if `r + mu t(u) <= L`, then `phi_u(r, g) = (r + mu t(u), u g)`;
- otherwise `phi_u(r, g) = ⊥`.

*The maps land in `Y`.*
- If `t(u) = 0`, then `u in K_Z`, so `u R_r = R_r`.
- If `t(u) >= 1`, take `kappa in K_Z` and `|g| <= r`. Then `|u kappa g| <= 1 + D + r <= r + mu t(u)`,
  so `u R_r ⊂ B(r + mu t(u)) ⊂ R_(r + mu t(u))`.

*(W).* Off `⊥`:
- `phi_f phi_e (r, g) = (r + mu ht(fe), fe g)` if `r + mu ht(fe) <= L`, and `⊥` otherwise.
  The intermediate level `r + mu b(e)` is at most the final one.
- `phi_e(r, g) = (r + mu ht(e), e g)`, again cut off at `L`.
- `id(r, g) = (r + mu ht(1), 1 g)`.

Each value depends only on the named element `q` and on `ht(q)`. By the definition of a height
potential, `ht` is a function on `Q`. So expressions naming the same element give the same map on all
of `Y`.

*(I).* Put `y_0 = (0, 1)`. Then `[q](y_0) = (mu ht(q), q)`, and this is not `⊥` because
`mu ht(q) <= L`. Distinct `q` give distinct points. ∎

The transformation monoid generated by the `phi_u` is finite. If some letter has positive height,
the monoid contains the constant map to `⊥`, since `L + 1` applications of that letter push every
level past `L`. Zero letters act by permutations of each level, and positive letters are many-to-one
onto `⊥`. The script
`experiments/finite-monoid-certificates-2026-09-17/check_monoid_model.py` checks (W) and (I)
exhaustively for the example `Z/2 * Z` with `E = F = {1, z, s}` from the germ-model artifact. There
`|Y| = 115`, the generated monoid has 15 elements, and the sampled bad fraction lies under
`C(|Q|,2)/N`.

## 5. Proposition R: read letters are units

**Proposition R.** In any Q-table embedding `lambda`, every letter in a read pair maps to a unit of
`M`. If every letter of `E ∪ F` is in a read pair, then `[Q]` lies in the finite group `U(M)`.

*Proof.* A read pair `fe = 1` gives `lambda(f) lambda(e) = [1] = 1_M`. In a finite monoid, `xy = 1`
implies `yx = 1`:
- `m -> y m` is injective, since `y m = y m'` gives `m = x y m = x y m' = m'`;
- so it is bijective, and `y z = 1` for some `z`;
- then `x = x y z = z`, so `y x = 1`.

So `lambda(f)` and `lambda(e)` are units, and products of units are units. ∎

**Corollary R (group level).** Let `G` be a countable group. Every configuration over `G` is
finite-monoid embeddable if and only if `G` is LEF (locally embeddable into finite groups).

*Proof.*
- (⇐) Given `(E, F)`, put `S = {1} ∪ E ∪ F ∪ FE`, and take an injective partial homomorphism
  `eta : S -> H` with `H` a finite group. Put `lambda = eta` on the letters. Then
  `[fe] = eta(f) eta(e) = eta(fe)`, so `[·]` is `eta|_Q`. It is well defined and injective.
- (⇒) Given a finite `S ∋ 1`, put `E = F = S ∪ S^(-1)`. Every letter is a read letter, so by
  Proposition R `lambda` takes values in `U(M)`. Put `eta(s) = lambda(E-copy of s) = [s]` for
  `s in S`. Since `1 in E`, the convention of Section 1 gives `lambda(F-copy of s) = [s]` as well.
  - It is injective, because `S ⊂ E ⊂ Q` and `[·]` is injective.
  - For `s, t, st in S`, the element `st` is named both by the expression `e = st` and by
    `fe` with `f = s`, `e = t`. So `eta(st) = [st] = lambda(F-copy of s) lambda(t) = eta(s) eta(t)`.
  - `eta(1) = [1] = 1_M`.

  So `G` is LEF. ∎

So the monoid freedom gains nothing at the level of groups. Every group-level theorem proved by exact
finite models is at most "LEF groups are Rokhlin-maximal". The gain is per pattern:
- Theorem M certifies individual patterns in non-LEF groups, even nonsofic ones.
- The finite-core patterns of Corollary A are examples. Their positive letters are non-read, so they
  may map to non-units.

## 6. Place among the filters, and what is left

**Filter.** In every Bernoulli Rokhlin deficit witness `(k, E, F, psi)` over any group, the Q-table has
no injective partial homomorphism into any finite monoid. By Theorem M' it therefore has no exact
finite functional model with a good point.

**Relation to existing nodes.**
- `finite-core-height-potential-forbids-bernoulli-deficit` (Theorem A) is Corollary A. The proof here is
  shorter: exact at every point, with no level padding.
- `rokhlin-maximality-closed-under-local-embeddings`, applied with the class of finite groups, is the
  special case where `lambda` lands in a group. This assumes finite groups count as Rokhlin-maximal for
  that node. Theorem M does not need that: it proves the finite-group case directly.
- `sofic-radical-localizes-bernoulli-deficit-witnesses` and the OPEN
  `amenable-core-height-potential-forbids-bernoulli-deficit` use approximate models, which Theorem M
  does not cover. Conversely, Theorem M does not need soficity or amenability of anything, only
  finiteness of one monoid.
- `reading-model-entropy-certificates-are-soficity`: for configurations with `B_r ⊂ E ∩ F`,
  double-count certificates are equivalent to soficity. Corollary R is the exact counterpart: exact
  finite certificates of all configurations are equivalent to LEF.

**Class killed.** The class is exact finite models:
- permutation models with exact relations;
- finite quotient and finite transformation-monoid models;
- any germ-type model whose relations hold on an invariant set containing a good point, such as the
  sink model of Corollary A.

*Invariant.* Finite-monoid embeddability of the Q-table.

*Where every member dies.* The step is Theorem M': an exact model with one good point is already a
Q-table embedding. So on a pattern with no Q-table embedding, every exact model has no good point.
At group level, the step is Corollary R: exact models of the ball configurations `E = F = S ∪ S^-1`
force LEF.

**Open prerequisites for a deficit witness.** A witness needs, independently:
- (D1) a Q-table that is not finite-monoid embeddable (Theorem M; necessary);
- (D2) failure of every approximate model: no sofic-type localization (sofic radical) and no
  amenable-core height potential if Theorem B holds;
- (D3) a finite value computation `Phi < log q` over some group.

(D1) is a property of one finite table. Embeddability is semi-decidable, by enumerating finite
monoids. Non-embeddability needs an obstruction argument, for example a non-LEF relation among read
letters, which by Proposition R must hold in a finite group.

**Questions.**
1. Is there a pattern that is finite-monoid embeddable but not finite-group embeddable, and has no
   finite-core height potential? Such a pattern would show that Theorem M is strictly stronger than
   Theorem A together with finite-group local embeddings. None is exhibited here.
2. In the nonsofic group `EL_D(R)` of `openai-leavitt-unit-nonsofic`, which configurations are
   finite-monoid embeddable? Only those can be ruled out as witnesses by this filter.
