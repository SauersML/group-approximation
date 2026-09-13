# Quantitative surjunctivity from measurable markers on subshift tracks

Lane `w7-quant-residue`, 2026-09-12. Supports the Cairn claims
`subshift-track-injections-lower-rokhlin-entropy` and
`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`, the open claim
`sofic-product-surjunctivity-forces-quantitative-deficits`, and the routes
`quantitative-surjunctivity-via-maximal-rokhlin-entropy`,
`uqs-via-maximal-bernoulli-rokhlin-entropy` and
`quantitative-surjunctivity-via-sofic-product-surjunctivity`. Everything below is proved on
paper. No computation was run. Seward's theorems are used only as imported in
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

## Summary

* **Theorem R.** Let an injective automaton map `(B^n x D^j)^G` into
  `Y_1 x ... x Y_n x (D^(j'))^G`, each `Y_i` a subshift missing a pattern. Then the Rokhlin
  entropy of the amplified uniform Bernoulli shift falls below its base entropy by a deficit
  linear in `n`, at a fixed marker cost of `log 3` per distinct window. The proof uses no
  finite model and never evaluates an invariant configuration. The case `n = 1`, `j = j' = 0`
  is `strict-automaton-lowers-bernoulli-rokhlin-entropy`.
* **Corollary U.** Suppose every uniform Bernoulli shift over `G` has Rokhlin entropy equal to
  its base entropy, that is INF(G). Then every such map has margin
  `(j' - j) log|D| >= sum_i eta_i / D_i`. So `G` is uniformly quantitatively surjunctive with
  `delta(B, w) = -log(1 - |B|^-w) / w^2`, and quantitatively surjunctive with
  `delta_Y = -log(1 - |B|^-|W|) / |W W^-1|`. On such groups this covers the residue of
  `quantitative-surjunctivity-constants-lift-from-quotients`.
* **Proposition U'.** Over any countably infinite group, one map with margin below that
  threshold bounds `h^Rok_sup(G)` explicitly. So a surjunctive group that is not
  quantitatively surjunctive has finite Rokhlin supremum. On hosts whose supremum is `0` or
  `infinity`, such as the binary Leavitt unit group and Thompson's `V`, one such map forces
  the supremum to be `0`.
* **Routes.** `bernoulli-rokhlin-entropy-maximal-for-every-group` implies
  `surjunctive-groups-are-quantitatively-surjunctive` and its uniform version.
* **The converse.** Write T for the quantitative claim, P for
  `products-with-a-sofic-factor-are-surjunctive`, and C for "if `G x K` is surjunctive for
  every sofic `K`, then `G` is quantitatively surjunctive". Then T holds iff C and P both
  hold. Products with the LEF permanence closure are already surjunctive, so a proof of C that
  does not prove T constructs a sofic group outside that closure. C stays open.
* **What stays open.** No nonsofic group is known to have maximal Bernoulli Rokhlin entropy.
  So no new group becomes quantitatively surjunctive, and the residue stays open over every
  nonsofic group.

## 0. Conventions

* `G` is a countable group, `B` a finite alphabet with `b = |B| >= 2`, `D` a finite alphabet,
  and `n >= 1`, `j, j' >= 0` integers. The shift is `(g.x)(h) = x(g^-1 h)`. Points of
  `(B^n x D^(j'))^G = (B^G)^n x (D^(j'))^G` are written `y = (y_1, ..., y_n, z)`.
* A map from `(B^n x D^j)^G` into `... x (D^(j'))^G` has *margin* `mu = (j' - j) log|D|`.
* A subshift `Y_i <= B^G` *misses* `r_i in B^(W_i)` if `(g.y)|_(W_i) != r_i` for every
  `y in Y_i` and `g in G`. Every proper subshift misses some pattern. If `Y_i` misses `r_i` on
  `W_i`, it misses the translated pattern on `w_0^-1 W_i` for `w_0 in W_i`. This changes
  neither `|W_i|` nor `|W_i W_i^-1|`, so assume `1 in W_i`. Put

  ```text
  eta_i = -log(1 - b^(-|W_i|)),     D_i = |W_i W_i^-1|,     Sigma = sum_i eta_i / D_i,
  ```

  and let `m` be the number of distinct sets among `W_1, ..., W_n`.
* `h^Rok_G` is Rokhlin entropy, the infimum of the Shannon entropies of generating countable
  partitions. It is an isomorphism invariant. `h^Rok_sup(G)` and INF are as in
  `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.
* QS and UQS are as in `surjunctive-groups-are-quantitatively-surjunctive` and
  `amenable-extensions-of-uqs-groups-are-surjunctive`.

## 1. Theorem R

**Theorem R.** Let `G` be countably infinite, and `Phi` an injective cellular automaton from
`(B^n x D^j)^G` into `Y_1 x ... x Y_n x (D^(j'))^G`, where `Y_i` misses `r_i in B^(W_i)`. Then
for every `k >= 1`

```text
h^Rok_G( (B^(nk) x D^(jk))^G, uniform ) <= k (n log b + j' log|D| - Sigma) + m log 3.
```

*Proof.*

**Step 0 (amplify).** The product `Phi^(k)(x_1, ..., x_k) = (Phi(x_1), ..., Phi(x_k))` is an
injective automaton from `(B^(nk) x D^(jk))^G` into a product of `nk` tracks, `k` copies of each
`Y_i`, times `(D^(j'k))^G`. It has the same `m` windows, and its `Sigma` is `k Sigma`. So the
case `k = 1` gives the theorem.

**Step 1 (transfer).** Let `u` be the uniform product measure on `X = (B^n x D^j)^G`. `Phi` is a
continuous equivariant injection of a compact space, so it is a homeomorphism onto its image, and
`nu = Phi_* u` is invariant on `Z = (B^n x D^(j'))^G`. `Phi` is an isomorphism of `(X, u)` with
`(Z, nu)`, so `h^Rok_G(X, u) = h^Rok_G(Z, nu)`. The Bernoulli shift over an infinite group is
essentially free, and freeness transfers. Let `Z_0 <= Phi(X)` be an invariant conull Borel set
of free points. Every `y in Z_0` has `y_i in Y_i`.

**Step 2 (markers, one per window).** For each distinct window `W` put `S_W = W W^-1 \ {1}`.
Step 2 of Section 1 of `research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md` uses
only freeness on `Z_0` and a countable separating family of Borel sets. It gives a Borel set
`C_W <= Z_0` with

```text
(S_W . c) cap C_W = empty  for c in C_W,          C_W union S_W . C_W = Z_0,
```

so `s_W = nu(C_W) >= 1/|W W^-1|`. By Step 3 there, `B_W = W^-1 . C_W` is the disjoint union of
the `|W|` sets `w^-1 . C_W`, so `nu(B_W) = |W| s_W`. Since `1 in W`, `C_W <= B_W`.

**Step 3 (the partition).** Let `T_W = { i : W_i = W }` and define

```text
alpha_W(y) = (o, ((y_i(w))_(w in W))_(i in T_W))     if y in C_W,
alpha_W(y) = *                                        if y in B_W \ C_W,
alpha_W(y) = (b, (y_i(1))_(i in T_W))                 if y in Z_0 \ B_W,
zeta(y)    = z(1).
```

Let `alpha` be the join of `zeta` and the `m` partitions `alpha_W`.

* *Generating.* The coordinate partition `beta(y) = (y_1(1), ..., y_n(1), z(1))` generates, and
  `z(1)` is read from `zeta`. Fix `i in T_W`. Off `B_W`, `y_i(1)` is read from `alpha_W(y)`. For
  `y in B_W` exactly one `w in W` has `w.y in C_W`, by Step 3 of the cited artifact. For
  `y` off `B_W` no `w in W` has `w.y in C_W`, since otherwise `y = w^-1.(w.y) in B_W`. So `y in B_W`
  iff some `alpha_W(w.y)`, `w in W`, carries the tag `o`, and that `w` is unique. Since
  `(w.y)_i(w) = y_i(1)`, the coordinate `y_i(1)` is the `w`-entry of the `i`-th pattern recorded
  at `w.y`. So `beta` is measurable for the invariant sigma-algebra generated by `alpha`.
* *Entropy.* At `y in C_W` each `y_i|_W` differs from `r_i`, because `y_i in Y_i` (take `g = 1`).
  So `alpha_W` takes at most `(b^|W| - 1)^|T_W|` values on `C_W`, one value on `B_W \ C_W`, and
  `b^|T_W|` values off `B_W`. Conditioning on the three-set partition,

  ```text
  H(alpha_W) <= log 3 + s_W |T_W| log(b^|W| - 1) + (1 - |W| s_W) |T_W| log b
              = log 3 + |T_W| (log b - s_W eta_W)
             <= log 3 + |T_W| (log b - eta_W / |W W^-1|).
  ```

  Summing over the `m` windows and adding `H(zeta) <= j' log|D|` gives
  `H(alpha) <= m log 3 + n log b + j' log|D| - Sigma`. QED

**Remark 1.1 (what the markers never see).** For a normal subgroup `N != 1`, `Fix_N` is `u`-null:
fix `t != 1` in `N`; infinitely many disjoint pairs `{h, t^-1 h}` must carry equal uniform
coordinates. `Phi(x) in Fix_N` iff `x in Fix_N`, because `Phi` is equivariant and injective. So
`Fix_N` is `nu`-null, the constant configurations included (`N = G`). Counting on invariant
configurations fails on the residue because `Y` contains them all. Theorem R never evaluates a
null set. What it spends instead is a lower bound on Rokhlin entropy, and that is the open part.

**Remark 1.2 (constants).** The sofic count of Section 3 of
`research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md` gives
`eta_W / (|W|^2 + 1)`, and periodic points over residually finite groups give `eta_W / |W|^2`.
Since `|W W^-1| <= |W|^2 - |W| + 1`, the constant `eta_W / |W W^-1|` below is at least as large.

## 2. Corollary U and the supremum bound

**Corollary U.** Let `G` be countably infinite with `h^Rok_G(A^G, uniform) = log|A|` for every
finite alphabet `A`. By item 1 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, this is INF(G), since
`min{log|A|, h^Rok_sup(G)} = log|A|` for every `A` iff `h^Rok_sup(G) = infinity`. Then every
`Phi` as in Theorem R has margin `mu >= Sigma`. Consequently:

1. `G` is UQS with `delta(B, w) = -log(1 - |B|^-w) / w^2`;
2. `G` is QS with `delta_Y = -log(1 - |B|^-|W|) / |W W^-1|` for any pattern on `W` missing from
   `Y`;
3. `G x K` is surjunctive for every sofic `K`, by Theorem Q of the product-fibre artifact.

*Proof.* By hypothesis the Rokhlin entropy of `(B^(nk) x D^(jk))^G` is its base entropy
`k(n log b + j log|D|)`. Theorem R gives
`k(n log b + j log|D|) <= k(n log b + j' log|D| - Sigma) + m log 3`, that is
`k(mu - Sigma) >= -m log 3`, for every `k`. Divide by `k` and let `k -> infinity`: `mu >= Sigma`.

For (1), `|W_i| <= w` gives `eta_i >= -log(1 - |B|^-w)` and `D_i <= |W_i|^2 <= w^2`, so
`Sigma >= n delta(B, w)`, and a margin below `delta(B, w) n` is impossible. For (2) every `W_i`
is `W`, so `Sigma = n eta_W / |W W^-1|`. (3) is Theorem Q applied to (2). QED

**Proposition U' (supremum bound).** Let `G` be countably infinite and `Phi` as in Theorem R
with `mu < Sigma`. Put `k_0 = floor(m log 3 / (Sigma - mu)) + 1`. Then

```text
h^Rok_sup(G) <= k_0 (n log b + j' log|D| - Sigma) + m log 3 < k_0 (n log b + j log|D|).
```

*Proof.* `k_0 (Sigma - mu) > m log 3` gives the strict inequality. So at `k = k_0` the bound of
Theorem R is below the base entropy. By item 1 of the import the Rokhlin entropy is
`min{base entropy, h^Rok_sup(G)}`, so it equals `h^Rok_sup(G)`, which is at most the bound. QED

For one strict automaton (`n = m = 1`, `j = j' = 0`, `mu = 0`) this recovers
`strict-automaton-bounds-rokhlin-supremum`, with the same `k_0`.

**Finite groups.** Let `|G| = N`. A maximal `C <= G` with `C C^-1 cap S_W` empty satisfies
`G = (S_W union {1}) C`, so `|C| >= N / |W W^-1|`. The windows `c^-1 W`, `c in C`, are disjoint,
and every `y in Y_i` avoids a pattern on each of them. So
`|Y_i| <= b^N (1 - b^(-|W_i|))^(N / D_i)`. Injectivity gives
`N (n log b + j log|D|) <= sum_i (N log b - N eta_i / D_i) + N j' log|D|`, that is `mu >= Sigma`,
with no hypothesis.

**Scope.**
* Every group known to satisfy the hypothesis of Corollary U is sofic (Scope of
  `rokhlin-maximality-ascends-co-amenable-subgroups`). INF is unknown for the surjunctive Kun--Thom
  wreaths (Attempts of `leavitt-units-have-zero-rokhlin-entropy-supremum`). So Corollary U
  makes no new group QS.
* **Amenable extensions.** For an infinite normal `N` with `G/N` amenable, INF(N) already gives
  maximality for `G` through `rokhlin-maximality-ascends-co-amenable-subgroups`. So part (1)
  adds no new group through `amenable-extensions-of-uqs-groups-are-surjunctive`.
* **Products.** For amenable `K`, part (3) also follows from co-amenable ascent. For nonamenable
  sofic `K` ascent does not apply, and part (3) goes through Theorem Q.
* **Self-copy hosts.** If `h^Rok_sup(G)` is `0` or `infinity`, POS(G) already gives INF(G) and
  so parts (1)-(3).

## 3. Candidates over V and the Leavitt units

A group that is surjunctive but not QS has, for some `Y` missing `r` on `W`, maps with margin
below `delta n` for every `delta > 0`, in particular below `Sigma = n eta_W / |W W^-1|`. By
Proposition U' one such map makes `h^Rok_sup(G)` finite. Thompson's `V` and
`U = L_(F_2)(1,2)^x` contain copies of their squares and finite subgroups of unbounded order, so
their suprema are `0` or `infinity` (`rokhlin-supremum-dichotomy-with-centralized-self-copies`).
Hence:

* over `U`, one sub-threshold map establishes `leavitt-units-have-zero-rokhlin-entropy-supremum`.
  By `self-copy-host-rokhlin-deficits-need-unbounded-windows` it then forces collapse at every
  alphabet through windows of unbounded size;
* over `V`, it refutes `thompson-v-has-positive-rokhlin-entropy-action`.

This weakens the hypothesis of `leavitt-zero-rokhlin-supremum-from-strict-automaton` from a
strict automaton (margin `0`, one track) to any injection below the threshold. The open claim
`leavitt-units-are-not-quantitatively-surjunctive` records this weaker target, with route
`leavitt-zero-rokhlin-supremum-from-sub-threshold-injection`. By the Residue item of
`quantitative-surjunctivity-constants-lift-from-quotients`, the subshift of a candidate must
contain every constant configuration. For the simple group `V` that is the only restriction the
quotient method imposes. No candidate is known. Building one is at least as strong as the
zero side of the dichotomy on its host.

## 4. The converse

* T = `surjunctive-groups-are-quantitatively-surjunctive`: every surjunctive group is QS.
* P = `products-with-a-sofic-factor-are-surjunctive`.
* C = `sofic-product-surjunctivity-forces-quantitative-deficits`: if `G x K` is surjunctive for
  every sofic `K`, then `G` is QS.

**Proposition 4.1.** T holds iff C and P both hold.

*Proof.* T gives P by Theorem Q. T gives C, because `K = 1` makes the hypothesis of C imply that
`G` is surjunctive. Conversely, let `G` be surjunctive. P makes `G x K` surjunctive for every
sofic `K`, and C then makes `G` QS. QED

Per group, Theorem Q gives QS(G) => (`G x K` surjunctive for all sofic `K`). So C(G) says exactly
that this hypothesis is equivalent to QS(G).

**Proposition 4.2 (the LEF permanence closure absorbs the hypothesis).** For every surjunctive
`G`, `G x K` is surjunctive for every `K in Cl(LEF)`
(`products-with-lef-permanence-closure-factors-are-surjunctive`). Hence:

1. if every sofic group lies in `Cl(LEF)`, the hypothesis of C is surjunctivity, and C is T;
2. if C holds and T fails, some sofic group lies outside `Cl(LEF)`. Take `G` surjunctive and not
   QS. C gives a sofic `K` with `G x K` not surjunctive, and `K` is not in `Cl(LEF)`.

No sofic group is known outside `Cl(LEF)` (Place in the graph of P). So a proof of C that does
not prove T must construct one. A refutation of C needs a surjunctive group that is not QS and
whose products with all sofic groups stay surjunctive.

**Proposition 4.3 (form of a counterexample to C).** A counterexample `G` is countably infinite
(finite groups satisfy the margin bound, Section 2), surjunctive and not QS. By Proposition U',
`h^Rok_sup(G) < infinity`. By item 3 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`,
`h^Rok_sup(P x G) = 0` for every countable `P` with arbitrarily large finite subgroups.

**Where constructions of C die.** C asks, from maps of small margin over `G`, for a strict
automaton over some `G x K`. Theorem Q runs the other way. Its transplant along a sofic model `V`
of `K` stores the model's defects on a free track of size `epsilon |V|`, and that track is what
the margin pays for. Running it backwards means laying the `n` tracks along the vertices of finite
models and correcting the defects. Models that realize the multiplication of `K` exactly at every
vertex on growing balls embed those balls into finite symmetric groups, so `K` is LEF and `G x K`
is surjunctive: there is nothing to build. The construction has to hide the defects inside the
margin, and no mechanism is known. This is Proposition 4.2(2) seen from the construction side.

## 5. Graph wiring

* Claim `subshift-track-injections-lower-rokhlin-entropy`, route
  `subshift-track-injections-lower-rokhlin-entropy-proof` (`requires: []`): Theorem R.
* Claim `maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`, route
  `maximal-bernoulli-rokhlin-entropy-makes-groups-uqs-proof`, requiring Theorem R and the Seward
  import: Corollary U, Proposition U', finite groups.
* Routes `quantitative-surjunctivity-via-maximal-rokhlin-entropy` into T and
  `uqs-via-maximal-bernoulli-rokhlin-entropy` into
  `surjunctive-groups-are-uniformly-quantitatively-surjunctive`, each requiring Corollary U and
  `bernoulli-rokhlin-entropy-maximal-for-every-group`. Neither fires today. That prerequisite is
  open, and `leavitt-units-have-zero-rokhlin-entropy-supremum` would refute it.
* Open claim C, with route `quantitative-surjunctivity-via-sofic-product-surjunctivity` into T
  requiring C and P (Proposition 4.1).
* Open claim `leavitt-units-are-not-quantitatively-surjunctive`, with route
  `leavitt-zero-rokhlin-supremum-from-sub-threshold-injection` into
  `leavitt-units-have-zero-rokhlin-entropy-supremum`. It requires that claim, Corollary U and
  `rokhlin-supremum-dichotomy-with-centralized-self-copies` (Section 3).
* `## Attempts` entries on T, on the uniform claim and on P.

Independent re-derivation of Theorem R, Corollary U and Proposition U' is requested from
`w4-vf-positive-b`.
