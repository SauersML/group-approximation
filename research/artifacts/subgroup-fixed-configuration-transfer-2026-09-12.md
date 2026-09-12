# Surjectivity on subgroup-fixed configurations, and its exact reach

Lane `w4-free-pos-b`, 2026-09-12. Mathematics on paper; no computation.

**The approach.** A strict automaton has a closed invariant image `X`. Every subgroup `H` gives a
subshift `Fix_H` of configurations constant on right cosets of `H`, and the automaton acts on it as an
automaton on the labelled Schreier graph `H\G`. If that graph admits a surjunctivity argument (finite,
or amenable with enough recurrence), then `Fix_H` lies in `X`. If the admissible subgroups separate
finite sets, the union of the `Fix_H` is dense and `X` is everything. This note proves the transfer,
proves it for finite and repetitive amenable Schreier graphs, determines exactly which groups it can
decide (Section 3), and records that it says nothing on the recorded negative hosts (Section 4).

The open claim `co-amenable-fixed-configurations-lie-in-injective-images` is what the approach aims at.
It is implied by the conjecture.

## 0. Conventions

- `G` is a group and `A` is a finite alphabet with `q = |A| >= 2`.
- An automaton with memory `M` and rule `mu : A^M -> A` is `tau(x)(g) = mu((x(g m))_(m in M))`.
- The shift is `(g.x)(h) = x(g^-1 h)`, and automata commute with it.
- `sigma` has memory `N` and rule `nu`, and `sigma tau = id`. Put `X = tau(A^G)`.
- For `H <= G`, `Fix_H = { x : h.x = x for all h in H }`. Since `(h.x)(g) = x(h^-1 g)`, these are the
  configurations constant on each right coset `Hg`.
- `S = H\G` is the set of right cosets, with the right action `(Hg).k = Hgk`, which is well defined.
- For a finite label set `D`, the labelled Schreier graph `S_D` has an edge `v -> v.d` labelled `d`
  for each `v in S` and `d in D`. `B_R(v)` is the rooted ball of radius `R` in the graph with labels
  `D cup D^-1`.

## 1. Theorem A: restriction to the Schreier graph

**Theorem A.** Let `tau, sigma` be automata over `G` with `sigma tau = id`, and let `H <= G`.

1. `tau(Fix_H) = X cap Fix_H`.
2. The bijection `A^S -> Fix_H`, `y |-> x` with `x(g) = y(Hg)`, conjugates `tau` on `Fix_H` to the
   graph automaton
   `tau_S(y)(v) = mu((y(v.m))_(m in M))`,
   and `sigma` to `sigma_S(y)(v) = nu((y(v.n))_(n in N))`. Moreover `sigma_S tau_S = id`.
3. `Fix_H` is contained in `X` exactly when `tau_S` is surjective, and exactly when `sigma_S` is
   injective.
4. If `H` is normal, `S` is the group `G/H` and `tau_S` is the automaton over `G/H` with memory
   `MH/H`. So `Fix_H` lies in `X` whenever `G/H` is surjunctive.

**Proof.**
1. `tau` commutes with the shift, so it maps `Fix_H` into `Fix_H`. Conversely, suppose `tau(x)` lies in
   `Fix_H`. For `h in H`, `tau(h.x) = h.tau(x) = tau(x)`, and injectivity gives `h.x = x`.
2. If `x(g) = y(Hg)`, then `tau(x)(g) = mu((x(gm))_m) = mu((y(Hgm))_m) = tau_S(y)(Hg)`. The same holds for
   `sigma`. The identity `sigma tau = id` restricts to `Fix_H`, which gives `sigma_S tau_S = id`.
3. `sigma_S tau_S = id` makes `tau_S` injective and `sigma_S` surjective. So `tau_S` is onto iff it is
   bijective, iff `sigma_S` is its inverse, iff `sigma_S` is injective. Part 1 translates `tau_S` onto
   into `Fix_H` contained in `X`.
4. For normal `H`, `Hgm = (gH)(mH)`, so `tau_S` is the displayed automaton. Surjunctivity of `G/H`
   makes the injective automaton `tau_S` onto. QED.

Part 4 is the case recorded under `every-injective-ca-preserves-uniform-bernoulli-measure`. The
content of Theorem A is that the same restriction works for every subgroup, with the group replaced
by its coset space. `X` is invariant, so `Fix_H` lies in `X` iff `Fix_(gHg^-1) = g.Fix_H` does.

**Garden of Eden filter.** Suppose `Fix_H` lies in `X`. Let `p` be a pattern on a finite `E <= G` that
is constant on each class `E cap Hg`. Then `p` extends to a configuration in `Fix_H`, which lies in
`X`, so `p` is not a Garden of Eden pattern. So every Garden of Eden pattern of a strict automaton
takes two different values at two sites `e, e'` of `E` with `e' e^-1 in H`, for every admissible `H`
and every conjugate of it.

## 2. Theorem B: finite and repetitive amenable Schreier graphs

**Definitions.**
- Fix a finite `D <= G` containing `M`, `N` and `1`. Distances on `S` are taken in `S_D`.
- `∂_R Φ` is the set of vertices of a finite `Φ <= S` within distance `R` of `S \ Φ`.
- A Følner sequence is a sequence of finite `Φ_k <= S` with `|∂_R Φ_k| / |Φ_k| -> 0` for every `R`.
  Its existence says that `S_D` is amenable. When `D` generates `G`, `S_D` is connected, and this is
  co-amenability of `H` in `G`.
- `S_D` is repetitive along `(Φ_k)` if for every `v_0 in S` and every `R`,
  `liminf_k |O_k(v_0, R)| / |Φ_k| > 0`, where `O_k(v_0, R)` is the set of `v in Φ_k` with a rooted,
  label-preserving isomorphism `psi_v : B_R(v_0) -> B_R(v)`.

**Uniform recurrence suffices.** Suppose every rooted labelled ball that occurs recurs within distance
`L` of every vertex. Each `v in Φ_k \ ∂_L Φ_k` has an occurrence within distance `L`, inside `Φ_k`, and
one occurrence serves at most `(2|D|+1)^L` such `v`. So `|O_k| >= (|Φ_k| - |∂_L Φ_k|) / (2|D|+1)^L`,
and `S_D` is repetitive along every Følner sequence. Cayley graphs of amenable quotients `G/H` are
uniformly recurrent, since they are homogeneous.

**Theorem B.** Let `sigma tau = id` over `G` and `H <= G`.
- (a) If `S = H\G` is finite, then `Fix_H` lies in `X`.
- (b) If `S_D` has a Følner sequence along which it is repetitive, then `Fix_H` lies in `X`.

In both cases the Garden of Eden filter of Section 1 holds for `H` and each of its conjugates.

**Proof of (a).** `tau_S` is an injective self-map of the finite set `A^S`, so it is onto. Theorem A(3)
finishes.

**Proof of (b).** Suppose `tau_S` is not onto, and put `Y = tau_S(A^S)`.
1. **A missing pattern.** `A^S` is compact, so `Y` is closed. So there are a finite `W <= S` and a
   pattern `p` on `W` that is the restriction of no element of `Y`. The value `tau_S(y)|_W` depends only
   on `y|_(W.M)`, and every pattern on `W.M` extends to `S`. So `p` is missing exactly when no `z` on
   `W.M` satisfies `mu((z(w.m))_m) = p(w)` for all `w in W`.
2. **Transport.** Fix `v_0 in W` and `R >= 1` with `W.M <= B_R(v_0)`. A rooted labelled isomorphism
   `psi_v : B_R(v_0) -> B_R(v)` satisfies `psi_v(w.m) = psi_v(w).m` for `w in W`, `m in M`. So the pattern
   `p o psi_v^-1` on `W_v = psi_v(W)` is missing from `Y` in the same sense.
3. **Disjoint copies.** Let `delta > 0` be the liminf density of `O_k(v_0, R)`. For large `k` the set
   `O_k \ ∂_R Φ_k` has at least `(delta/2)|Φ_k|` elements. Choose greedily a subset `V_k` with pairwise
   distances `> 2R`. Then `|V_k| >= c |Φ_k|` with `c = delta / (2 (2|D|+1)^(2R))`, and the sets `W_v`
   (`v in V_k`) are disjoint and lie in `Φ_k`.
4. **Upper bound.** Every restriction `y|_(Φ_k)` with `y in Y` avoids `p o psi_v^-1` on every `W_v`. So
   `|Y|_(Φ_k)| <= q^|Φ_k| (1 - q^(-|W|))^(c |Φ_k|)`.
5. **Lower bound.** Let `I_k = { v in Φ_k : v.N <= Φ_k }`, which contains `Φ_k \ ∂_1 Φ_k`. The identity
   `y(v) = sigma_S(tau_S(y))(v)` reads `tau_S(y)` on `v.N`. So `tau_S(y)|_(Φ_k)` determines `y|_(I_k)`, and
   as `y` ranges over `A^S` this gives `|Y|_(Φ_k)| >= q^|I_k| >= q^(|Φ_k| - |∂_1 Φ_k|)`.
6. **Contradiction.** Steps 4 and 5 give `|∂_1 Φ_k| / |Φ_k| >= c · (-log_q(1 - q^(-|W|))) > 0` for all
   large `k`, which contradicts the Følner property. So `tau_S` is onto, and Theorem A(3) finishes.
   QED.

**What the proof uses.**
- It uses the exact decoder identity on the coset space (Theorem A), Følner sets of that one coset space,
  and positive-density recurrence of the certificate's labelled neighbourhood.
- It uses no finite model of `G`, and translations of `G` do not act on `S`. The group may be
  nonsofic.
- It is Gromov–Weiss counting moved from the group to one coset space. `S = G/H` for normal `H` recovers
  the amenable-quotient case.

**Where it stops.**
- Take a co-amenable `H` whose certificate neighbourhood occurs with zero density along every Følner
  sequence. Then step 3 yields `o(|Φ_k|)` copies. Step 5 loses `q^(|∂_1 Φ_k|)`, which is also
  `q^(o(|Φ_k|))`, and the two cannot be compared. This is the open residue of
  `co-amenable-fixed-configurations-lie-in-injective-images`.
- Weak-* limits of the Følner averages of the conjugates `g^-1 H g`, over `Hg in Φ_k`, give an invariant
  random subgroup whose Schreier graphs are Benjamini–Schramm limits of finite graphs. Counting with the
  mass transport principle on that limit is a natural next step. It is not carried out or claimed here,
  and it would put `Fix_(H')` in `X` only for almost every `H'` of the limit, not for `H` itself.

## 3. Theorem C: the exact reach of the transfer

**Density needs separation.** `X` is closed and invariant. So the transfer gives `X = A^G` as soon as
the union of the admissible `Fix_H` is dense. For a finite `F <= G` and an alphabet with `q >= |F|`,
the pattern with `|F|` distinct values on `F` extends into `Fix_H` only when the points of `F` lie in
distinct right cosets, that is, `H cap F F^-1 = {1}`. So a proof of surjectivity over every alphabet by
density needs admissible subgroups separating every finite set. For one small alphabet, refining each
colouring is enough, and that is weaker.

**Theorem C.** Let `G` be a group. Suppose that for every finite `F <= G` containing `1` there is a
subgroup `H_F` with `H_F cap F F^-1 = {1}` whose `D`-labelled Schreier graph, with `D = F cup F^-1`,
has a Følner sequence along which the rooted labelled 1-ball of the base vertex has positive lower
density. Then `G` is sofic.

**Proof.** Soficity means: for every finite `E` and `epsilon > 0` there are a finite set `Ω` and a map
`phi : G -> Sym(Ω)` with `d(phi(g)phi(h), phi(gh)) < epsilon` for `g, h in E`, and
`d(phi(g), 1) > 1 - epsilon` for `g in E \ {1}`. Here `d` is the normalized Hamming distance.
1. **Partial action.** Put `F = E cup EE cup {1}`, `H = H_F`, and `S = H\G` labelled by
   `D = F cup F^-1`. Let `delta > 0` be the density of the base 1-ball along the Følner sequence
   `(Φ_k)`. For `g in F`, let `phi(g)` be any permutation of `Φ_k` extending the partial injection
   `v |-> v.g^-1` on `{ v in Φ_k : v.g^-1 in Φ_k }`. Elsewhere `phi` is arbitrary.
2. **Defect.** For `g, h in E` and `v in Φ_k \ ∂_2 Φ_k`, both steps stay in `Φ_k`, and
   `(v.h^-1).g^-1 = v.(gh)^-1` with `gh in F`. So `d(phi(g)phi(h), phi(gh)) <= |∂_2 Φ_k| / |Φ_k|`.
3. **Separation.** Let `v in Φ_k \ ∂_1 Φ_k` have 1-ball isomorphic to the base 1-ball. For
   `g in E \ {1}`, `g^-1 = 1 . g^-1` lies in `F F^-1 \ {1}`, so `H.g^-1 != H`. The edge labelled `g^-1`
   at the base is not a loop, hence neither is it at `v`, and `phi(g)` moves `v`. For large `k` this
   gives `d(phi(g), 1) >= delta/2`.
4. **Amplification.** On `Ω = Φ_k^r` put `phi_r(g) = phi(g) x ... x phi(g)`. A point is fixed by
   `phi_r(g)` iff all coordinates are fixed, so `d(phi_r(g), 1) >= 1 - (1 - delta/2)^r`. The defect is
   at most `r |∂_2 Φ_k| / |Φ_k|` by a union bound. Choose `r` with `(1 - delta/2)^r < epsilon`, then `k`
   with `r |∂_2 Φ_k| / |Φ_k| < epsilon`. QED.

**Corollary C.1 (reach).** Call `H` admissible if it has finite index, has a repetitive amenable
Schreier graph, or is normal with surjunctive quotient. Suppose admissible subgroups separate every
finite set.
- **Sofic case.** If finite-index or repetitive amenable ones do so cofinally, `G` is sofic by
  Theorem C. A finite Schreier graph `S` is its own Følner set, and the base ball has density at least
  `1/|S|`.
- **Local embedding case.** Otherwise there is `F_0` such that every finite `F` containing `F_0` is
  separated by a normal `H` with `G/H` surjunctive. The quotient map is injective and multiplicative on
  `F`, so `G` is locally embeddable into surjunctive groups. Surjunctivity then already follows from
  `strict-pairs-transfer-to-table-realizations`.

**What this means.** The transfer proves surjunctivity only on groups where existing theorems already
reach. On every other group it supplies Garden of Eden filters and nothing more. The same phenomenon
kills the Hamming transports of `hamming-transports-of-weak-sofic-models-are-soficity`. The difference
is the starting data. Theorem C starts from exact infinite coset spaces with separation at a
positive-density set of vertices, while that result starts from finite actions with uniform separation.

## 4. Proposition D: the transfer is vacuous on the recorded hosts

Let the label set `D` generate `G`. That is the situation on a strict design's table group, which is
generated by its memory letters (`table-groups-are-memory-holonomy-groups`). Then `S_D` is connected,
and Følner sets for `S_D` are an invariant mean on `H\G`, that is, co-amenability of `H`.

**Proposition D.**
1. **Simple Kazhdan hosts.** If `G` is infinite, simple and Kazhdan, the only subgroup with an amenable
   Schreier graph is `G` (`simple-kazhdan-groups-have-no-proper-co-amenable-subgroups`). So Theorem B
   gives only `Fix_G`, the constant configurations. An injective automaton permutes these `q` points,
   so they lie in every injective image in any case. The only normal subgroups are `1` and `G`. So the
   transfer yields no information beyond "Garden of Eden patterns are nonconstant".
2. **Measure-free actions.** Let `G` act continuously on a compact Hausdorff space `Y` with no
   `G`-invariant Borel probability measure. Then no point stabilizer `G_y` is co-amenable.
   - **Proof.** An invariant mean `m` on `G/G_y` gives `Lambda(f) = m(g G_y |-> f(g y))` on `C(Y)`, which
     is positive, unital and invariant. By Riesz it is integration against an invariant probability
     measure, a contradiction.
3. **Thompson's V.** `V` acting on the Cantor set has no invariant probability measure `mu`.
   - The prefix map `0 -> 00, 10 -> 01, 11 -> 1` carries `[0]` onto `[00]`, so `mu[0] = mu[00]`.
   - The transposition `00x <-> 01x` gives `mu[00] = mu[01]`. So `mu[0] = mu[00] + mu[01] = 2 mu[0]`,
     and `mu[0] = 0`.
   - The swap `0x <-> 1x` gives `mu[1] = mu[0] = 0`, so `mu = 0`.

   So no point stabilizer of `V` is admissible.

**Consequence.**
- **Reduced hosts.** On `gottschalk-reduces-to-fg-simple-kazhdan-groups`'s hosts, such as the Leavitt
  unit groups recorded as Kazhdan, the fixed-configuration transfer is empty.
- **Thompson's V.** Its natural subgroups, the point stabilizers of the Cantor action, are not
  admissible.
- **Beyond Theorem B.** A positive use of fixed configurations on these hosts would need surjectivity
  of graph automata with local left inverses on nonamenable Schreier graphs. There the decoder boundary
  factor is linear in the volume. The end-fixing tree calibration
  (`end-fixing-tree-symmetries-carry-strict-automata`) shows that nonamenable graphs without unimodular
  structure carry strict graph automata.
