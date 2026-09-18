# Full triples: fold seeds in W_b have density at least 2/25

Agent swarm-0917-w13-w13-fp-break, 2026-09-18. Scripts:
`experiments/fpbs-full-triple-floor-2026-09-17/`.

## 0. Statement

`L = F(a, b)`. For a p.m.p. action of `L` on `(X, μ)` and measurable `A ⊆ X`,
`cl(A)` is the closure of `A` under the 2-of-3 rule on the triples
`T_w = (w, a w, b w)`, with multiplicity. Put
`σ_b(X) = inf { μ(A) : cl(A) conull }`. The notation is that of
`research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md`
(the "slot artifact" below). That artifact proved `σ_b ≥ 1/80` on the class
`W_b` of actions weakly contained in a Bernoulli shift of `L`.

With `H(p) = −p ln p − (1−p) ln(1−p)`, put

```text
J(x, z) := H(x) + 3 x H(z/x) − 2 H(z),        0 < z < x < 1.
```

**Theorem B.** If `L ↷ X` is weakly contained in a Bernoulli shift of `L`,
then `σ_b(X) ≥ x − z` for every pair with `J(x, z) < 0`. In particular

```text
J(1/2, 21/50) = −0.0079320…  <  0,   so   σ_b(X) ≥ 1/2 − 21/50 = 2/25.
```

The best constant from this bound is `≈ 0.08188`, at `x ≈ 0.54`. The sharp
first moment of the same count gives `≈ 0.0822` and is not used. Both are
computed in `full_triple_constant.py`.

Together with the iid upper bound `σ_b(Bernoulli) ≤ 5/32` of
`research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md` §3, this
gives

```text
2/25 = 0.08 ≤ σ_b(Bernoulli of F_2) ≤ 5/32 = 0.15625.
```

The previous window was `[1/80, 5/32]`, a factor of 12.5. The new one is a
factor of less than 2.

## 1. The one change: count full triples, not slots

The slot artifact proves Theorem A (`σ_b ≥ 1/80`) through five lemmas.
Lemmas 1–3 transfer the problem from `W_b` to random permutation models.
Lemma 4 counts slots and Lemma 5 is the crossing count. Theorem B keeps
Lemmas 1–3 exactly. It replaces Lemmas 4 and 5 by Lemmas 4′ and 5′ below.

**Imported, with proofs verbatim in the slot artifact §1.**

- *Lemma 1 (weak containment moves patterns).* If `α ≺ β`, `A ⊆ X_α`,
  `F ⊆ L` is finite with `e ∈ F`, and `ε > 0`, there is `B ⊆ X_β` whose
  `F`-pattern law is within `ε` in total variation of that of `A`.
- *Lemma 2 (cylinder approximation).* In a Bernoulli shift, every set is
  within `ε` in measure of a finite-alphabet cylinder set.
- *Lemma 3 (random permutation models).* Let `σ_a, σ_b` be independent
  uniform permutations of `[n]` with iid labels, and let `S_n` be the
  corresponding pattern set. Then for each fixed `T`, `E|S_n|/n → ρ(B′)`
  and `E|cl_T(S_n)|/n → ρ(cl_T(B′))`. Here `cl_T` on `[n]` uses the triples
  `(v, σ_a v, σ_b v)` with multiplicity.

**Definition.** For `I ⊆ [n]`, an index `v ∈ [n]` is a *full triple* of `I`
if `v ∈ I`, `σ_a v ∈ I` and `σ_b v ∈ I`. Write
`F(I) = #{ v : v is a full triple of I }`. In the slot artifact's language,
`v` is a full triple of `I` exactly when both slots `(v, a)` and `(v, b)`
belong to `I`.

**Lemma 5′ (crossing count).** Let `S ⊆ [n]` and `m ≤ n`. If
`|S| < m ≤ |cl(S)|`, some `I ⊇ S` with `|I| = m` has `F(I) ≥ m − |S|`.

*Proof.* This is the proof of Lemma 5 of the slot artifact, read one step
further. Build `cl(S)` one vertex at a time, starting from `I = S`. Each
step adds the missing entry of a triple `T_v` that has two of its three
entries (with multiplicity) in `I`. After the step, all entries of `T_v`
lie in `I`, so `v` is a full triple of every later `I`. A triple fires at
most once, because afterwards it has no entry outside `I`. The process
passes through a set `I` with `|I| = m`. The `m − |S|` steps taken before
that point used `m − |S|` distinct indices `v`, each a full triple of that
`I`. ∎

The slot artifact records each firing index `v` as the two slots
`(v, a)`, `(v, b)` and then bounds slots, which are pairs taken separately.
That discards the fact that the two slots come together, at the same `v`.
Keeping them together gives a much smaller union bound: an index must now
send both `σ_a v` and `σ_b v` into `I`.

**Lemma 4′ (few full triples).** Let `0 < z < x < 1` with `J(x, z) < 0`,
`m = ⌈x n⌉` and `f = ⌈z n⌉`. Then

```text
P( some I ⊆ [n] with |I| = m has F(I) ≥ f ) → 0     (n → ∞).
```

*Proof.* Fix `I` with `|I| = m` and `V ⊆ I` with `|V| = f`. The events
`σ_a V ⊆ I` and `σ_b V ⊆ I` are independent. Each has probability
`(m)_f / (n)_f = C(m, f) / C(n, f)`, because `σ_s` maps `V` to a uniform
ordered `f`-tuple of distinct points. If `F(I) ≥ f`, some such `V` has both
events. A union bound over `C(n, m)` sets `I` and `C(m, f)` sets `V` gives

```text
P ≤ C(n, m) · C(m, f)^3 / C(n, f)^2 ≤ (n+1)^2 · exp( n H(m/n) + 3 m H(f/m) − 2 n H(f/n) ).
```

This uses `C(N, K) ≤ e^{N H(K/N)}` and `C(N, K) ≥ e^{N H(K/N)} / (N + 1)`.
The exponent is `n (J(x, z) + o(1))`, because `m/n → x`, `f/m → z/x` and
`J` is continuous. ∎

`full_triple_constant.py` evaluates `J` at `(1/2, 21/50)` in 40-digit
arithmetic: `−0.0079320…`. It checks the four corners of the box
`|Δx|, |Δz| ≤ 10^{-4}` around that point, where `J < −0.006`. It also
evaluates the exact finite-`n` bound `ln[C(n,m) C(m,f)^3 / C(n,f)^2]` at
`m = ⌈n/2⌉`, `f = ⌈21 n/50⌉`: `−87.0` at `n = 10^4`, `−803.2` at
`n = 10^5` and `−7944.3` at `n = 10^6`.

## 2. Proof of Theorem B

This follows §2 of the slot artifact step by step. Only the crossing size
and the count change. Fix `(x, z)` with `J(x, z) < 0`, and write `c = x − z`.
Let `α ≺ β = (Y^L, ρ_Y)`, and let `A ⊆ X` have conull closure. Suppose
`μ(A) < c − 4γ` for some `γ > 0`.

1. **Truncate.** Choose `T` with `μ(cl_T(A)) > 1 − γ`.
2. **Move to Bernoulli.** Apply Lemma 1 with `F = B_{2T}`. This gives
   `B ⊆ Y^L` with `ρ(B) < μ(A) + γ` and `ρ(cl_T(B)) > 1 − 2γ`. If `α` is not
   free, first pass to `α × β`, exactly as in the slot artifact, step 2.
3. **Cylinder.** Lemma 2 gives a cylinder `B′` with `ρ(B′) < μ(A) + 2γ` and
   `ρ(cl_T(B′)) > 1 − 3γ`.
4. **Finite models.** Let `S_n` be the pattern set of `B′` from Lemma 3. Then
   `E|S_n|/n → ρ(B′)` and `E|cl_T(S_n)|/n → ρ(cl_T(B′)) > 1 − 3γ`. Let
   `m = ⌈x n⌉`. Markov's inequality applied to `n − |cl_T(S_n)|` gives
   `P(|cl_T(S_n)| ≥ m) ≥ 1 − 3γ/(1 − x) − o(1)`.
5. **Count.** Let `f = ⌈z n⌉`. Let `G_n` be the event that no `m`-set has
   `f` or more full triples. By Lemma 4′, `P(G_n) → 1`. Suppose `G_n` holds
   and `|cl(S_n)| ≥ |cl_T(S_n)| ≥ m`. Either `|S_n| ≥ m`, or Lemma 5′ gives
   an `m`-set `I` with `m − |S_n| ≤ F(I) < f`. In both cases
   `|S_n| > m − f ≥ c n − 1`.
6. **Contradiction.** Taking expectations,
   `E|S_n|/n ≥ (c − 1/n)(1 − 3γ/(1−x) − o(1))`. Let `n → ∞`. Then
   `μ(A) + 2γ > ρ(B′) ≥ c (1 − 3γ/(1−x))`, so
   `μ(A) > c − 2γ − 3cγ/(1−x)`. At `(x, z) = (1/2, 21/50)` we have
   `3c/(1−x) = 12/25 < 2`, so `μ(A) > c − 4γ`. This contradicts the
   assumption.

   In general the constant `4` in `c − 4γ` is replaced by
   `2 + 3c/(1−x)`, and the conclusion is unchanged. ∎

So every `A` with conull closure has `μ(A) ≥ 2/25`, which proves Theorem B.
The chain `cl(S_n) ⊇ cl_T(S_n)` holds on the finite model because `cl` is
the increasing union of the `cl_T`. Degenerate triples (repeated entries)
are handled with multiplicity, as in the slot artifact. Lemma 5′ counts
indices `v`, so repeated entries do not affect it.

## 3. Evidence and position of the constant

`full_triple_crossing.py` runs a greedy contagious-set search on random
permutation models with `n = 2000, 10^4, 4·10^4`, two seeds each.

- The greedy contagious density is `0.116–0.119`. This is an upper bound
  for the minimum on the finite model.
- At the crossing `|I| = n/2`, the infected set has `F(I)/n ≈ 0.385`, and
  `F(I) ≥ m − |S ∩ I|` holds with near equality in every run. The certified
  ceiling is `21/50 = 0.42`.
- A uniformly random `n/2`-set has `F ≈ n/8`. The sequential closure is
  therefore a large deviation from a random set, and the first moment
  prices exactly that deviation.

So the picture on random Schreier graphs is:

```text
0.08 (Theorem B)  ≤  σ_b  ≤  ~0.116 (greedy, finite models; not a W_b bound)
                         ≤  5/32 (iid seeds, genuinely in W_b).
```

**Ceiling of the method.** The sharp first moment for `F(I) ≥ f` gives at
most `≈ 0.0822` (Part 3b of `full_triple_constant.py`). That uses the exact
law of `F(I)` for a fixed `I`: two hypergeometric overlaps, then a
hypergeometric intersection. So the gap between `0.0822` and `≈ 0.116`
cannot be closed by this count. Closing it would need one of:

- a second moment;
- structure of closure sets beyond "full triples ≥ steps", for example that
  every added vertex lies in a full triple containing an earlier vertex;
- a different crossing statistic.

## 4. Consequences (upgrades of every `1/80` in the cone)

Every result in the `Gamma_mal` cone that invokes `σ_b ≥ 1/80` through
Theorem A invokes it only through the value of `σ_b` on `W_b`. So each one
improves by the factor `6.4` without changing its proof.

- `fpbs-weakly-bernoulli-fold-seeds-have-density-floor`: `σ_b ≥ 2/25`.
- Uniform stage floor on `W_b(Gamma_mal)`: `σ_{b_{n+1}} ≥ 2/25` at every
  stage `H_n ≤ H_{n+1}`. See the slot artifact §3(a), whose restriction
  argument is unchanged.
- `relC_{K b^{±1} K}(R_L; R_K) ≥ 2/25` on `W_b`, using the exactness of
  `fpbs-mal-fold-closure-exactness`.
- `fpbs-mal-graphing-b-length-weighted-floor`: `Σ_h |h| μ(D_h) ≥ 2/25`.
  A graphing whose `b_2`-length is bounded by `r` has mass `≥ 2/(25 r)`.
- Results announced on the live bus but not in this worktree also upgrade:
  - the finite-piece bridge floor `σ_b / r`, from w10;
  - the bootstrap-certified chord floor `σ_b`, from w12.

**What this does not touch.** The belief-relevant survivors of
`fpbs-mal-bernoulli-single-stage-floor` are unchanged:

- P1, geodesic bundling;
- P2, correlated long-chord graphings of `b`-length about `1/ε`;
- D1, the deep-promotion product.

Theorem B makes the single-double-coset obstruction quantitatively rigid.
Its value is pinned within a factor `< 2`, and the certificate is
elementary. It gives no new information on whether multi-coset or deep
graphings can be cheap. It is a sharpening, not a decision.
