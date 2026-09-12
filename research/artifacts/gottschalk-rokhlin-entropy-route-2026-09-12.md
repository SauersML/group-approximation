# Surjunctivity from Rokhlin entropy of Bernoulli shifts

Lane `gk-rokhlin`, 2026-09-12. Supports the Cairn claims
`strict-automaton-lowers-bernoulli-rokhlin-entropy`,
`bernoulli-rokhlin-maximality-passes-to-subgroups`,
`bernoulli-rokhlin-deficit-has-a-finitary-witness` and
`window-entropy-deficits-are-not-isomorphism-invariant`, and the open claims
`bernoulli-rokhlin-entropy-maximal-for-every-group` and
`bernoulli-rokhlin-entropy-maximal-on-fixed-tester`. Everything below is proved
on paper. No computation was run and no source was re-read for this artifact.

## Summary

* A strict injective automaton over `G` on `q` symbols forces some amplified
  uniform Bernoulli shift over `G` to have Rokhlin entropy strictly below its
  base entropy (Theorem 1). The same holds for every invariant measure on a
  proper subshift that is isomorphic to the uniform Bernoulli shift.
* Maximal Rokhlin entropy of the uniform Bernoulli shifts over `G` therefore
  makes `G` surjunctive. Over all groups it gives Gottschalk's conjecture, and
  Kaplansky's direct finiteness conjecture over finite fields through linear
  automata.
* Maximality passes to subgroups and up finite index (Proposition 2).
* A failure of maximality is witnessed by one finite configuration: finite sets
  `E, F` in `G` and a function `psi` of the coordinates in `E` whose
  `F`-translates know more about one coordinate than `psi` costs (Theorem 3).
  Maximality is therefore closed under directed colimits with arbitrary
  structure maps. By the fixed tester theorem it holds for every group exactly
  when it holds for the tester host `U`.
* Window-counting entropy is not an isomorphism invariant over a nonamenable
  group (Proposition 4). The proof must use an invariant, here Rokhlin entropy,
  and it pays for markers with amplification.
* Maximality for every group is open. For sofic groups it follows from sofic
  entropy, which rests on the same finite models as Gromov--Weiss. No nonsofic
  group is known to satisfy it, and none is known to fail it.

## Conventions

* `G` is a countable group, `A` a finite alphabet, `q = |A| >= 2`, and `mu_A` the
  uniform product measure on `A^G`. The shift is `(g.x)(h) = x(g^-1 h)`. A cellular
  automaton is `tau(x)(g) = m((x(g s))_(s in M))` for a finite memory `M` and a local
  rule `m`. It commutes with the shift.
* For a measure-preserving action `G ~ (Y, lambda)` on a standard probability
  space, a countable Borel partition `alpha` is *generating* if the smallest
  `G`-invariant sigma-algebra containing `alpha` is the Borel sigma-algebra modulo
  null sets. The **Rokhlin entropy** is

  ```text
  h^Rok_G(Y, lambda) = inf { H_lambda(alpha) : alpha generating }.
  ```

  It is an isomorphism invariant. The coordinate partition `beta(x) = x(1)` of
  `A^G` is generating, so `h^Rok_G(A^G, mu_A) <= log q`.
* Write `f_q(k) = h^Rok_G((A^k)^G, mu_(A^k))`. The join of generating partitions
  of two systems generates their product, so `f_q` is subadditive, and the
  per-copy limit

  ```text
  rho_q(G) = lim_k f_q(k)/k = inf_k f_q(k)/k
  ```

  exists. Since `f_q(k) <= k log q`, **maximality** `rho_q(G) = log q` holds
  exactly when `f_q(k) = k log q` for every `k`.
* `(A^G)^k` with the diagonal shift and the product measure is the uniform
  Bernoulli shift `(A^k)^G`.

## 1. Strict automata lower Rokhlin entropy

**Theorem 1.** Let `G` be countably infinite and `nu` a shift-invariant Borel
probability measure on `A^G` such that `(A^G, nu)` is isomorphic to
`(A^G, mu_A)`. Suppose `nu([p]) = 0` for a pattern `p in A^Omega`, `Omega` finite.
Put

```text
delta = -log(1 - q^(-|Omega|)) > 0,        D = |Omega Omega^-1|.
```

Then for every `k >= 1`

```text
h^Rok_G((A^k)^G, mu_(A^k)) <= k (log q - delta/D) + log 3.
```

In particular `rho_q(G) <= log q - delta/D`, and `f_q(k) < k log q` whenever
`k > D log 3 / delta`.

*Proof.*

**Normalization.** Assume `1 in Omega`. Since `nu` is invariant, `g.[p]` is
again a null cylinder, with window `g Omega`. So translating the pattern puts `1`
in its window without changing `|Omega|`, `delta`, or `D`, because
`g Omega Omega^-1 g^-1` is conjugate to `Omega Omega^-1`. Step 4 uses this. It
makes `C` a subset of `B = Omega^-1 . C`, so `{C, B \ C, Y_0 \ B}` partitions
`Y_0`, and it makes `y(1)` an entry of the pattern recorded at `y in C`. (Added
by gk-verify-pos, 2026-09-12.)

**Step 0 (amplify).** Let `Y = (A^G)^k` with the diagonal shift and
`lambda = nu^(x k)`. The `k`-fold product of the isomorphism gives
`(Y, lambda) ~= ((A^k)^G, mu_(A^k))`, so it suffices to bound `h^Rok_G(Y, lambda)`.
By invariance and countable additivity, `lambda`-almost every `y` has no copy
`y_i` with `(g.y_i)|_Omega = p` for any `g`. The Bernoulli shift over an infinite
group is essentially free, and freeness transfers through the isomorphism.
Let `Y_0` be the invariant conull Borel set on which both hold.

**Step 1 (reading windows).** Let `beta(y) = (y_1(1), ..., y_k(1))`. It is a
generating partition of `Y`. Since `(w^-1 . y)(1) = y(w)`, the `Omega`-pattern of
`y` is

```text
( beta(w^-1 . y) )_(w in Omega).
```

For `y in Y_0` no copy of this pattern equals `p`, so it takes at most
`(q^|Omega| - 1)^k` values.

**Step 2 (an independent marker set).** Let `S = Omega Omega^-1 \ {1}`, a symmetric
set. There is a Borel set `C` in `Y_0` with

```text
(S . c) cap C = empty for c in C,          C union S.C = Y_0.
```

Fix a countable family of Borel sets separating points and closed under
complements. For `g in S` and `y in Y_0` we have `g.y != y`, so some member
`U` of the family contains `y` and not `g.y`. For each function `j` from `S` to
the index set let

```text
W_j = { y in Y_0 : y in U_(j(g)) and g.y not in U_(j(g)) for every g in S }.
```

These countably many Borel sets cover `Y_0` and satisfy `g.W_j cap W_j = empty`
for `g in S`. Enumerate them `W_1, W_2, ...` and put `C_1 = W_1`,
`C_n = W_n \ S.(C_1 union ... union C_(n-1))` and `C = union_n C_n`.

* *Independent.* If `c in C_n` and `g.c in C_m` with `g in S`: for `m < n`,
  `c = g^-1.(g.c) in S.C_m`, which `C_n` excludes; `m > n` is symmetric; `m = n`
  contradicts `g.W_n cap W_n = empty`.
* *Maximal.* A point of `W_n \ C_n` lies in `S.C_m` for some `m < n`.

So `lambda(C)(1 + |S|) >= lambda(C union S.C) = 1`, that is
`s := lambda(C) >= 1/D`.

**Step 3 (disjoint blocks).** Put `B = Omega^-1 . C`. If `w^-1.c = w'^-1.c'`, then
`c' = w' w^-1 . c`. Independence forces `w' w^-1 = 1`, so `w = w'` and `c = c'`.
Thus `B` is the disjoint union of the `|Omega|` translates `w^-1.C`, and
`lambda(B) = |Omega| s`.

**Step 4 (the partition).** Define

```text
alpha(y) = (o, Omega-pattern of y)   if y in C,
alpha(y) = *                         if y in B \ C,
alpha(y) = (b, beta(y))              if y in Y_0 \ B.
```

* *Generating.* Off `B`, `beta(y)` is read from `alpha(y)`. For `y in B` exactly
  one `w in Omega` has `w.y in C` (Step 3), and `beta(y)` is the `w`-entry of the
  pattern `alpha(w.y)`. So `beta` is measurable for the sigma-algebra generated
  by the translates of `alpha`, and `beta` generates.
* *Entropy.* `alpha` refines the three-set partition `{C, B \ C, Y_0 \ B}`, so

  ```text
  H(alpha) <= log 3 + s log((q^|Omega| - 1)^k) + (1 - |Omega| s) k log q
            = log 3 + k log q - s k delta
           <= log 3 + k log q - k delta / D.
  ```

So `h^Rok_G(Y, lambda) <= k(log q - delta/D) + log 3`. QED

**Corollary 1.1 (surjunctivity).** If `tau` is an injective cellular automaton on
`A^G` that is not surjective, then `X = tau(A^G)` is a proper closed invariant
set and misses some cylinder `[p]`. `tau` is an equivariant homeomorphism onto
`X`, so `nu = tau_* mu_A` satisfies Theorem 1. Consequently:

* `rho_q(G) = log q` implies that every injective automaton on `q` symbols over
  `G` is surjective;
* maximality for every `q` makes `G` surjunctive;
* maximality for every `q = p^n` makes `F_p[G]` stably finite, because a one-sided
  inverse pair in `M_n(F_p[G])` gives a strict linear automaton on `F_p^n`
  (`stable-finiteness-failure-refutes-surjunctivity`).

Finite groups need no argument.

**Remark 1.2 (why the product).** For `k = 1` the marker cost `log 3` swamps the
saving `s delta`, and without amplification a saving needs almost perfect
tilings of orbits by `Omega`-blocks. These need not exist. For
`G = Z/3 x Z` and `Omega = {(0,0), (1,0)}`, each block lies in one `Z/3`-coset
of an orbit, so blocks cover at most two thirds of every orbit. Amplifying the
alphabet multiplies the saving per block by `k` and leaves the marker cost fixed.
The proof uses no finite model, no Folner set and no ordering of `G`.

## 2. Heredity

**Proposition 2.** Let `L` be a finite set and `H <= G`.

1. `h^Rok_G(L^G, mu_L) <= h^Rok_H(L^H, mu_L)`.
2. If `[G:H] = n` is finite, then `h^Rok_H(Y) <= n h^Rok_G(Y)` for every
   measure-preserving `G`-action `Y`, and the restriction of `G ~ L^G` to `H` is
   the uniform Bernoulli shift `H ~ (L^n)^H`.

Consequently `rho_q(G) = log q` implies `rho_q(H) = log q`, and `rho_q(H) = log q`
implies `rho_q(G) = log q` when `H` has finite index.

*Proof.*

(1) Restriction `pi(x) = x|_H` is `H`-equivariant, since `(eta.x)|_H = eta.(x|_H)`
for `eta in H`, and it pushes `mu_L` on `L^G` to `mu_L` on `L^H`. If `alpha` is
`H`-generating on `L^H`, then `alpha' = pi^-1(alpha)` has the same entropy. The
`G`-invariant sigma-algebra generated by `alpha'` contains every coordinate `x(h)`,
`h in H`, and so every coordinate `x(g h) = (g^-1.x)(h)`. So `alpha'` is
`G`-generating.

(2) Write `G` as the disjoint union of the right cosets `H t`, `t in T`. For
`G`-generating `alpha`, `g.alpha = eta.(t.alpha)` when `g = eta t`, so
`gamma = join_(t in T) t.alpha` is `H`-generating, and `H(gamma) <= n H(alpha)`.
The map `x -> (h -> (x(h t))_(t in T))` is an `H`-equivariant isomorphism of
`L^G` onto `(L^T)^H` carrying product measure to product measure.

For the consequences:

* Part 1 gives `f_q(k)` over `G` at most `f_q(k)` over `H`, and both are at most
  `k log q`.
* Part 2 with `L = A^k` gives `n k log q = f_q(nk)` over `H`, which is at most
  `n f_q(k)` over `G`. QED

## 3. A finitary witness for a deficit

For `k >= 1`, finite sets `E, F` in `G` and a function `psi` from `(A^k)^E` to a
finite set, let `x = (x(g))_(g in G)` be iid uniform on `A^k` and put

```text
U_f = psi( (x(f e))_(e in E) )   for f in F,
Phi(k, E, F, psi) = (1/k) [ H(psi(x|_E)) + H( x(1) | (U_f)_(f in F) ) ].
```

`Phi` depends only on the finite incidence pattern `(f, e) -> f e` on
`F x E`: which products coincide, and which equal `1`.

**Theorem 3.** `rho_q(G) = inf Phi(k, E, F, psi)` over all configurations. So
`rho_q(G) = log q` if and only if every configuration satisfies

```text
H(psi(x|_E)) + H( x(1) | (psi((x(f e))_e))_(f in F) ) >= k log q.
```

*Proof.*

**Upper bound.** Fix a configuration and `eps > 0`. Take `k'` independent copies:
`y = (y_1, ..., y_k')` uniform on `((A^k)^G)^k' = (A^(k k'))^G`.

* Put `alpha'(y) = (psi(y_i|_E))_(i <= k')`.
* For each `i` put `U_i(y) = (psi((y_i(f e))_e))_(f in F)` and `V_i(y) = y_i(1)`.
  The pairs `(U_i, V_i)` are iid over `i`.
* The conditional typical-set lemma gives sets `S(u)` of `V`-sequences with
  `|S(u)| <= exp(k'(H(V|U) + eps))` and `P(V in S(U)) -> 1`.
* Let `xi(y)` be `(0, index of V(y) in S(U(y)))` when `V in S(U)`, and `(1, V(y))`
  otherwise. Then

  ```text
  H(xi) <= log 2 + k'(H(V|U) + eps) + P(V not in S(U)) k k' log q.
  ```

* Since `(f^-1.y)_i(e) = y_i(f e)`, `U(y)` is the list of values `alpha'(f^-1.y)`,
  `f in F`. So the translates of `gamma = alpha' join xi` determine `U`, then `V`,
  and `V` generates. So `gamma` is generating, and

  ```text
  f_q(k k') <= H(gamma) <= k' H(psi(x|_E)) + H(xi).
  ```

Divide by `k k'` and let `k' -> infinity`: `rho_q(G) <= Phi + eps/k`.

**Lower bound.** Fix `k` and a generating `alpha` for `(A^k)^G` with
`H(alpha) < f_q(k) + eps`.

* Since `beta` is measurable for the sigma-algebra generated by the translates of
  `alpha`, continuity of conditional entropy gives a finite `F` with
  `H(beta | alpha^F) < eps`, where `alpha^F = join_(f in F) f.alpha`.
* Truncating `alpha` to finitely many cells and approximating each cell by a
  finite union of cylinders gives a partition `alpha_0 = psi(x|_E)`, `E` finite,
  with `H(alpha|alpha_0) + H(alpha_0|alpha) < eps/|F|`.
* Then `H(alpha_0) <= H(alpha) + eps` and

  ```text
  H(beta | alpha_0^F) <= H(beta | alpha^F) + sum_(f in F) H(f.alpha | f.alpha_0) < 2 eps.
  ```

* `f.alpha_0` reads the coordinates in `f E`, so `alpha_0^F` is the tuple `(U_f)`
  of the configuration `(k, E, F, psi)`.

So `k Phi < f_q(k) + 3 eps`. Letting `eps -> 0` and taking the infimum over `k`
gives `inf Phi <= rho_q(G)`. QED

**Corollary 3.1 (closure).**

1. A configuration in a subgroup is a configuration in the group. This is part 1
   of Proposition 2 again.
2. Let `G` be a directed colimit of countable groups `G_i` with arbitrary
   structure maps, and suppose `rho_q(G) < log q`.
   * Take a configuration with `Phi < log q`.
   * Lift `E` and `F` to some `G_i`. Every coincidence `f e = f' e'` or `f e = 1`
     in `G` already holds in some `G_j` further along, and non-coincidences never
     become coincidences under the maps to `G`.
   * So in some `G_j` the lifted configuration has the same incidence pattern,
     hence the same `Phi`, and `rho_q(G_j) < log q`.

   Maximality is closed under directed colimits.
3. Let `C_q` be the class of groups all of whose finitely generated subgroups
   `K` satisfy `rho_q(K) = log q`.
   * `C_q` is closed under subgroups.
   * It is closed under directed colimits with arbitrary structure maps. A finitely
     generated subgroup of a colimit is a directed colimit of finitely generated
     subgroups of the `G_i`.
   * For countable `G`, `G in C_q` exactly when `rho_q(G) = log q`, by parts 1 and
     2 applied to `G` as the union of its finitely generated subgroups.

   By `universal-all-group-subgroup-colimit-class-tester`, the fixed two-generator
   host `U` satisfies `rho_q(U) = log q` if and only if every countable group does.

**Remark 3.2.** For `k = 1` and `q = p` prime, a nonzero `F_p`-linear functional
`psi` of iid uniform coordinates is uniform, so `H(psi) = log q` and no linear
`psi` witnesses a deficit. Witnesses are genuinely nonlinear. The same pattern
appears in `invariant-output-automata-have-only-nonlinear-decoders`.

## 4. Window entropy is not an invariant over nonamenable groups

**Proposition 4.** Let `G` be nonamenable. There are a finite `S` containing `1`
and `c > 0` with `|F S| >= (1 + c)|F|` for every nonempty finite `F`. On
`(A^G, mu_A)` both `beta` and `gamma = join_(s in S) s.beta` are generating, and

```text
inf_F H(beta^F)/|F| = log q,        inf_F H(gamma^F)/|F| >= (1 + c) log q,
```

with `alpha^F = join_(f in F) f.alpha` and `F` over nonempty finite sets.

*Proof.* `(f.beta)(x) = x(f)`, so `beta^F` reads the coordinates in `F` and
`H(beta^F) = |F| log q`. `gamma^F` reads the coordinates in `F S`, so
`H(gamma^F) = |F S| log q`. The expansion inequality is Folner's criterion for
right translates. QED

So the window entropy of a generating partition depends on the partition. The
inference "the coordinate process of a proper image subshift has window entropy
below `log q`, while the coordinate process of the Bernoulli shift has exactly
`log q`, so the two are not isomorphic" is invalid over every nonamenable group.
Over amenable groups the Folner limit of `H(beta^(F_n))/|F_n|` is the
Kolmogorov--Sinai entropy of any generating partition and the inference is the
classical proof. Theorem 1 replaces the window quantity by the invariant
`h^Rok`.

## 5. Status of maximality

* **Sofic groups.** Sofic entropy of a Bernoulli shift equals its base entropy
  and is at most the Shannon entropy of any generating partition, so sofic groups
  are maximal. This is context, not imported: its sources were not re-read here,
  and it uses the finite models of Gromov--Weiss.
* **Seward's per-group theory.** This is now imported verbatim by another lane
  as `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`; see Section 6.
* **Nonsofic groups.** No nonsofic group is known here to be maximal or to fail
  maximality. A deficit over `G` would make `G` nonsofic, because sofic groups
  are maximal.
* **Counterexample hosts.** A strict automaton on `q` symbols over `G` gives
  `rho_q(G) < log q` (Theorem 1), hence a finite configuration with
  `Phi < log q` (Theorem 3), hence the same deficit in every group realizing its
  incidence pattern. Every host for a Gottschalk counterexample is a group whose
  uniform Bernoulli shifts, after amplification, have generating partitions of
  Shannon entropy below the base entropy.
* **What would decide the open claim.** Prove the inequality of Theorem 3 for
  every finite incidence pattern that occurs in some group. Every argument known
  to this lane that bounds Bernoulli Rokhlin entropy from below uses finite models
  or Folner sets. Restriction to an infinite amenable subgroup `Lambda` gives only
  the upper bound of Proposition 2(1), `h^Rok_G(L^G) <= h^Rok_Lambda(L^Lambda)`,
  and the reverse inequality would already settle every group containing an
  element of infinite order. Information about the coordinates in `Lambda` can
  spread over the other cosets of `Lambda`, and this lane has no density argument
  along `G/Lambda`.

## 6. Relation to Seward's per-group theory

Another lane imported the following verbatim from arXiv:1501.03367v4 as
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`:

* Theorem 1.10: `h^Rok_G(L^G) = min{H(L), h_sup(G)}` when `H(L) < infinity`;
* Theorem 1.11: `(for all G, POS) => (for all G, INF)`;
* Corollary 4.1: `h^Rok_G(k^G) = log k` for every `k` gives Gottschalk and
  Kaplansky for `G`.

With it, this artifact reads as follows.

1. **Maximality is INF.** The uniform bases `A^k` have unbounded entropy, so
   `min{k log q, h_sup(G)} = k log q` for all `k` exactly when
   `h_sup(G) = infinity`. So:
   * Theorem 1 is a self-contained quantitative proof of the Gottschalk half of
     Corollary 4.1;
   * Theorem 3 and Corollary 3.1 make INF closed under subgroups and under directed
     colimits with arbitrary structure maps;
   * INF for the fixed tester host `U` is equivalent to INF for every countable
     group.
2. **An explicit bound on the supremum.** Let `k_0 = floor(D log 3/delta) + 1`.
   Theorem 1 at `k_0` gives

   ```text
   h^Rok((A^(k_0))^G) <= k_0 log q - k_0 delta/D + log 3 < k_0 log q,
   ```

   and by Theorem 1.10 the left side is `min{k_0 log q, h_sup(G)}`. So a group
   carrying a strict automaton has `h_sup(G) < k_0 log q`
   (`strict-automaton-bounds-rokhlin-supremum`).
3. **Universal forms.** The all-groups claim of Section 5 is `for all G, INF`. It
   follows from `for all G, POS` by Theorems 1.11 and 1.10. It implies
   `for all G, POS`, because the Bernoulli 2-shift is free and ergodic with
   Rokhlin entropy `log 2`. Two routes record the equivalence with
   `every-group-has-positive-rokhlin-entropy-action`.
4. **Unchanged.** Per group, POS => INF is open (Seward). The self-copy dichotomy
   `rokhlin-supremum-dichotomy-with-centralized-self-copies` closes that gap for
   groups that contain their own square and finite subgroups of unbounded order.
   No lower bound on `h_sup` is known for any nonsofic group.
