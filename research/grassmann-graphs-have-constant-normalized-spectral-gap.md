---
rg: 2
id: grassmann-graphs-have-constant-normalized-spectral-gap
kind: claim
title: The Grassmann graph Gr_q(n,l) is loop-free q[l][n-l]-regular with normalized spectral gap exactly [n]/(q[l][n-l]) > (q-1)/q, so every set has Phi(S) >= (1 - mu(S))(q-1)/q and the zoom-ins and zoom-outs attain that floor with equality
distinct_from:
  unique-games-on-expanding-constraint-graphs-are-easy: that is the imported rounding algorithm that consumes a spectral gap; this computes the gap of one graph family by an elementary recursion and says nothing about unique games.
  spectral-gap-ratio-reductions-cannot-prove-ugc: that turns a spectral gap into a gate on reductions; this supplies the number the gate needs for one family, and its (K4) bullet is the contrapositive of the expansion floor recorded here.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is the Bafna--Minzer algorithm, which uses a characterisation of the Grassmann graph's non-expanding sets and covers only affine constraints; this is the elementary second eigenvalue of the same graph, with no hypercontractivity, no algorithm and no constraint system.
  small-set-expansion-hypothesis: that is the open hardness statement about graph families carrying sets of expansion tending to 0; this proves one named family carries none, with the exact extremal sets.
  spread-support-overlap-forces-non-expanding-small-sets: that produces, from a spread support map, a set of measure in [delta, 10 delta] with Phi <= 1 - theta + rho/delta, which for Grassmann-like view graphs is a bound *above* 1 - theta; this is the matching unconditional bound *below*, Phi(S) >= (1 - mu(S))(q-1)/q. The two numbers agree (both put the zoom-ins near (q-1)/q), and the established node there reads that as "Grassmann view graphs cannot be NO outputs of an SSEH reduction"; nothing here contradicts it, since this claim is only the two-sided bound on Phi and draws no SSEH consequence.
artifacts:
  - experiments/grassmann-spectral-gap-2026-09-17/check_grassmann_gap.py
---

**OPEN** (demoted 2026-09-18 at landing: all three swarm-0917 referee lenses
returned `refuted` on the parent result
`unique-games-hard-on-non-sse-grassmann-constraint-graphs`, and the refuted
sentence lived in this file too --- see `## Attempts`). The proof is kept as the
attempt artifact
`research/artifacts/grassmann-spectral-gap-recursion-proof-2026-09-18.md`.
Everything in it is elementary and self-contained: no eigenvalue formula,
association scheme or high-dimensional-expander theorem is imported. Replay:
`experiments/grassmann-spectral-gap-2026-09-17/check_grassmann_gap.py`
(prints `ALL PASS`, exit 0).

All three referees re-derived Theorems 1-6 independently and confirmed them.
What they refuted is the small-set-expansion gloss that this file used to carry
under "What this fixes, in one line", which the route never proved. Theorems 1-6
are therefore expected to be restorable verbatim once that paragraph is
replaced; that restoration is not claimed here.

*Setting.* `q >= 2` a prime power, `n >= 2`, `1 <= l <= n - 1`. Write
`[m] = [m]_q = (q^m - 1)/(q - 1)`. `V_l` is the set of `l`-dimensional subspaces
of `F_q^n`, with the uniform probability measure `mu_l`;
`|V_l| = [n choose l]_q`. The **Grassmann graph** `Gr_q(n,l)` has vertex set
`V_l` and an edge `L ~ L'` exactly when `dim(L cap L') = l - 1`. For a weighted
graph, `lambda_2` is the second smallest eigenvalue of the normalized Laplacian
`I - D^(-1/2) A D^(-1/2)`, and
`Phi(S) = w(E(S, V \ S)) / vol(S)`, `mu(S) = vol(S)/vol(V)`.

**Theorem 1 (shape).** `Gr_q(n,l)` is loop-free, connected and regular of degree

```text
d_1 = q [l] [n-l].
```

**Theorem 2 (exact spectral gap).**

```text
lambda_2(Gr_q(n,l))  =  [n] / (q [l] [n-l]).
```

Equivalently the second largest eigenvalue of the normalized adjacency is
`1 - [n]/(q[l][n-l])`, which agrees with the classical
`theta_1 = q^2 [l-1][n-l-1] - 1` through the integer identity
`q[l][n-l] - q^2[l-1][n-l-1] + 1 = [n]` (replay (C3)).

**Theorem 3 (uniform floor).** For every prime power `q >= 2`, every `n >= 2`
and every `1 <= l <= n - 1`,

```text
lambda_2(Gr_q(n,l))  >  (q - 1)/q  >=  1/2,
```

and `lambda_2 -> (q-1)/q` as `l, n-l -> infinity`. The bound does **not**
degrade with `n`, `l` or the alphabet of anything placed on the graph. So the
Grassmann graphs are spectral expanders with an absolute constant gap.

**Theorem 4 (expansion floor, with its equality cases).** In any weighted graph,
`Phi(S) >= (1 - mu(S)) lambda_2` for every `S` (this is the contrapositive of
bullet (K4) of `spectral-gap-ratio-reductions-cannot-prove-ugc`; a one-line
proof is repeated in the route). On `Gr_q(n,l)` this reads

```text
Phi(S)  >=  (1 - mu(S)) [n]/(q [l] [n-l])  >  (1 - mu(S)) (q-1)/q,
```

and it is **tight**, attained with equality by the non-expanding sets that the
DKKMS/KMS analysis names:

```text
zoom-in   Z_x  = { L : x in L },        mu = [l]/[n],      Phi = q^(l-1)/[l];
zoom-out  Z^H  = { L : L subset H },    mu = [n-l]/[n],    Phi = q^(n-l-1)/[n-l];
```

`Phi(Z_x) = (1 - mu(Z_x)) lambda_2` and `Phi(Z^H) = (1 - mu(Z^H)) lambda_2`,
exactly, for all `q, n, l` (replay (C7), (C7c)).

**Theorem 5 (domination).** Let `W` be a nonnegative symmetric weighting of
`V_l` with all weighted degrees equal to `d`, and suppose `W >= c A_1`
entrywise, where `A_1` is the 0/1 adjacency of `Gr_q(n,l)` and `c > 0`. Then

```text
lambda_2(W)  >=  c d_1 lambda_2(Gr_q(n,l)) / d  >  (c d_1 / d) (q-1)/q.
```

Call `rho = c d_1 / d` the **Grassmann density** of `W`: the share of `W`'s
weight that is a uniform copy of the Grassmann graph. Then
`lambda_2(W) > rho (q-1)/q`. A `GL_n(F_q)`-invariant weighting supported on the
relation `dim(L cap L') = l - 1` has `rho = 1`, because `GL_n(F_q)` is
transitive on ordered pairs of subspaces at that relation, so such a weighting
is the uniform one.

**Theorem 6 (bipartite containment graph).** The biregular bipartite graph on
`V_(l-1) u V_l` with `M ~ L` iff `M subset L` has second largest singular value
(of the normalized biadjacency)

```text
sigma_2^2  =  1 - [n]/([l] [n-l+1])  <  1/q,
```

so its normalized-Laplacian gap is `1 - sigma_2 > 1 - q^(-1/2)`. This graph is
biregular but **not** regular when `|V_(l-1)| != |V_l|`, which matters for the
gates that quote regular hypotheses.

**What this used to claim, and what is left of it.** This paragraph used to read
that `Gr_q(n,l)` **is** a small-set expander "in the sense that
`small-set-expansion-hypothesis` and Raghavendra--Steurer use", and that its
non-expanding sets "carry no information beyond the single number `lambda_2`".
Both halves were refuted (see `## Attempts`). What Theorems 3 and 4 actually
support is only this:

* every set has `Phi(S) >= (1 - mu(S))(q-1)/q`, so `Gr_q(n,l)` carries no set of
  expansion tending to `0` --- it is not a YES instance of `Gap-SSE(eta, delta)`
  for `eta < (1 - delta)(q-1)/q`;
* it is **not** a small-set expander in the sense those sources use, which is
  *near-perfect* expansion `Phi(S) >= 1 - eta`: the zoom-ins have
  `mu(Z_x) = [l]/[n] -> 0` with `Phi(Z_x) = q^(l-1)/[l] -> (q-1)/q < 1`. So it
  is not an expanding NO instance either; it sits in the promise gap;
* attaining the floor `(1 - mu)lambda_2` at `mu = o(1)` is strictly more
  structure than `lambda_2`. A Ramanujan graph with the same `lambda_2` has
  `Phi(S) = 1 - o(1)` on all sets of measure `o(1)`. Equality only says
  `1_S - mu` lies in the second eigenspace; that the zoom-ins and zoom-outs are
  the *only* near-extremal small sets is the DKKMS/KMS structure theorem, not a
  consequence of `lambda_2`.

## Attempts

* **Small-set-expansion gloss on Theorems 3-4 (2026-09-18, swarm-0917,
  scale-shifter; refuted at landing, demoted from ESTABLISHED to OPEN).**
  Referee lenses 1, 2 and 3 all returned `refuted`. The verdict is recorded on
  the parent node `unique-games-hard-on-non-sse-grassmann-constraint-graphs`
  (verdicts `96bc7dfa`, `124cfa4b`, `17e004e3`) and repeated there in full; the
  short form for this file is:

  - Theorems 1-6 themselves **survive**. All three lenses re-derived
    `UD = alpha_l I + (1-alpha_l)Ahat_l` with `alpha_l = 1/[n-l+1]`,
    `DU = gamma_l I + (1-gamma_l)Ahat_(l-1)` with `gamma_l = 1/[l]`, the
    adjointness `U = D^*`, the telescoping, the closed form
    `lambda_2 = [n]/(q[l][n-l]) > (q-1)/q`, its agreement with the classical
    `theta_1 = q^2[l-1][n-l-1] - 1`, the floor `Phi(S) >= (1 - mu)lambda_2`, the
    zoom equalities `Phi(Z_x) = q^(l-1)/[l]`, the domination lemma, the
    `GL_n`-transitivity forcing `rho = 1`, and Theorem 6's
    `sigma_2^2 = 1 - [n]/([l][n-l+1]) < 1/q`. The replay
    `check_grassmann_gap.py` prints `ALL PASS`, exit 0.
  - The refuted step is the old "What this fixes, in one line" paragraph: a
    quantifier flip. "Small-set expander", in
    `small-set-expansion-hypothesis` and in Raghavendra--Steurer
    (arXiv:1011.2586 Cor. 3.3, quoted in that node as "near-perfect expansion of
    sets of measure in `[delta, M delta]`"), is the NO side
    `Phi_G(delta) >= 1 - eta`. The paragraph substituted the YES side, "no small
    set has `Phi <= eta`". Theorem 4's own numbers refute the substitution:
    `q=2, n=40, l=20` gives `mu(Z_x) = 9.54e-7` with `Phi(Z_x) = 0.500000`;
    `q=3, n=30, l=15` gives `mu = 7.0e-8` with `Phi = 0.666667`. `Gr_q(n,l)` is
    neither a YES instance nor a NO instance --- it lies in the promise gap.
    The paragraph even conceded the standard reading one sentence earlier
    ("true only in the sense *not an optimal one*") and then contradicted it.
  - Second refuted step, same paragraph: "they carry no information beyond the
    single number `lambda_2`". Equality in `Phi(S) >= (1 - mu)lambda_2` gives
    only that `1_S - mu` lies in the second eigenspace. That the second
    eigenspace holds `~q^n` such indicator differences at measure `mu -> 0` is a
    high-threshold-rank fact a Ramanujan graph with the same `lambda_2` does not
    have, and it is exactly what the KMS and Bafna--Minzer lines consume.
  - Repair the referees agree on: delete the two refuted sentences, keep
    Theorems 1-6 and the replay unchanged, and restore the route. Lens 3 adds
    that the `distinct_from` entry for
    `spread-support-overlap-forces-non-expanding-small-sets` must stop calling
    the two nodes "consistent" on the SSEH reading, since that established node
    concludes Grassmann view graphs cannot be SSEH NO outputs; that entry has
    been rewritten above to claim only agreement of the numbers.
