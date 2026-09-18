# The Gamma_mal floor is a one-step deep-promotion floor on F_2

Worker swarm-0917-w9-w9-fp-follow (quantifier-shift), September 18, 2026.
Target: `fpbs-mal-bernoulli-single-stage-floor`.

## 0. Notation

- `beta` is the Bernoulli shift of `Gamma_mal` on `([0,1]^Gamma, Leb)`.
  - `E = E_beta` and `R_m = E_{beta|H_m}`, where `H_m = <a, b_m>`.
  - `theta` is the stage shift, and `T` implements it
    (`fpbs-shifted-stage-relative-cost-zero-or-infinite`, §1 item 4).
- A **graphing** is a countable family of partial measure-preserving maps
  inside `E`. `C(Psi)` is the sum of the measures of their domains.
- **Promotion cost.** For `2 <= m <= infinity`, with `H_infinity = Gamma_mal`
  and `R_infinity = E`, set

  ```text
  q_m = inf { C(Psi) : Psi a graphing inside R_m,  R_1 v Psi ⊇ R_2 }.
  ```

  - `q_m` is nonincreasing in `m`, since `R_m ⊆ R_{m+1}`.
  - `q_2 = relC(R_2; R_1) =: r`, the single-stage relative cost of the
    chord artifact.

## 1. Proposition Q (quantifier shift)

1. `q_infinity = inf_m q_m = lim_m q_m`.
2. `relC(E; R_1) = 0` iff `q_infinity = 0`.
3. Hence the target `relC(E; R_1) > 0` holds iff `lim_m q_m > 0`. By the
   0-or-infinity dichotomy, it then holds with value infinity.

### Proof

**(2), "only if".** `R_1 v Phi = E ⊇ R_2` for every `Phi` admissible for
`relC(E; R_1)`. So `q_infinity <= relC(E; R_1)`.

**(2), "if".** Suppose `q_infinity = 0` and fix `eps > 0`.
- For each `k >= 1` choose `Psi^(k)` inside `E` with
  `R_1 v Psi^(k) ⊇ R_2` and `C(Psi^(k)) < eps 2^{-k}`.
- Put `Psi_k = T^{k-1} Psi^(k) T^{1-k}`. Then `T^{k-1}` carries `R_1` to
  `R_k`, `R_2` to `R_{k+1}` and `E` to `E`. So `Psi_k` lies inside `E`,
  `R_k v Psi_k ⊇ R_{k+1}`, and `C(Psi_k) = C(Psi^(k))`, because `T`
  preserves `mu`.
- By induction on `k`, `R_1 v Psi_1 v ... v Psi_k ⊇ R_{k+1}`. The case
  `k = 1` is the choice of `Psi^(1)`. For the step, the join of the first
  `k-1` graphings with `R_1` contains `R_k`, so adding `Psi_k` gives a
  relation containing `R_k v Psi_k ⊇ R_{k+1}`.
- Since `E` is the union of the `R_k`, `Phi = U_k Psi_k` satisfies
  `R_1 v Phi = E` with `C(Phi) < eps`. So `relC(E; R_1) = 0`.

**(1).** Since `q_infinity <= q_m`, it suffices to show `inf_m q_m <= q_infinity`.
Let `Psi` be admissible for `q_infinity` and fix `delta > 0`.
- Freeness splits each map of `Psi` into label pieces `psi_{j,g}` on
  `D_{j,g}`, with `sum mu(D_{j,g}) = C(Psi)`. Let `Psi_m` be the pieces with
  `g in H_m`, which lie inside `R_m`.
- The relations `S_m = R_1 v Psi_m` increase with `m`. Every `R_1 v Psi`-path
  uses finitely many pieces, so `U_m S_m = R_1 v Psi ⊇ R_2`.
- Let `A_m = { x : (x, b_2 x) not in S_m }`. These sets decrease to a null
  set, so `mu(A_m) < delta` for some `m >= 2`.
- Put `Psi' = Psi_m ∪ b_2|_{A_m}`. It lies inside `R_m`. The relation
  `R_1 v Psi'` contains every pair `(x, b_2 x)` and every pair `(x, a x)`, so
  it contains `R_2 = E_{<a, b_2>}`.
- Hence `q_m <= C(Psi) + delta`. Now let `delta -> 0`, and use that `q_m` is
  nonincreasing.

**(3)** follows from (1), (2) and Theorem S. QED

## 2. Translation to one free group

Let `L = F(a, b)`, `phi(a) = a`, `phi(b) = b a b^{-2}`, and
`L_j = phi^j(L) = <a, phi^j(b)>`. So `L_1 = K = <a, c>`.

**Lemma 2.1.** The isomorphism `psi_m : H_m -> L`, with `a -> a` and
`b_m -> b`, carries `H_{m-j}` onto `L_j` for `0 <= j < m`.

*Proof.* By induction, `psi_m(b_{m-j}) = phi^j(b)`:
`psi_m(b_{m-j-1}) = psi_m(b_{m-j} a b_{m-j}^{-2}) = phi^j(b) a phi^j(b)^{-2} = phi^j(b a b^{-2}) = phi^{j+1}(b)`.
The step uses `phi^j(a) = a`. QED

**Lemma 2.2.** `beta|H_m` is isomorphic to the Bernoulli shift of `H_m`.

*Proof.* `H_m` acts freely on `Gamma` by left multiplication. Choosing one
representative in each right coset `H_m gamma` identifies `[0,1]^Gamma` with
`Y^{H_m}` equivariantly, where `Y = [0,1]^{H_m \ Gamma}`. `Y` is a standard
non-atomic probability space, so it is isomorphic to `[0,1]`. QED

**Corollary 2.3.** Let `rho` be the Bernoulli shift of `L` and put
`S_j = E_{rho|L_j}`, so `S_0 = E_rho`. Set

```text
Q_j = inf { C(Psi) : Psi a graphing inside E_rho,  S_{j+1} v Psi ⊇ S_j }.
```

Then `Q_j = q_{j+2}`, `Q_0 = r = relC(E_rho; S_1)`, and `Q_j` is
nonincreasing in `j`. Hence

```text
fpbs-mal-bernoulli-single-stage-floor   iff   inf_j Q_j > 0.
```

*Proof.* Take `m = j + 2`. Transport by `psi_m` and Lemma 2.2 sends
`H_1 -> L_{j+1}`, `H_2 -> L_j` and `H_m -> L`. So `q_m = Q_j`. Then apply
Proposition Q. QED

## 3. Reading

- **One-step form.** The target is about a group that is not finitely
  generated. It is equivalent to a uniform one-step statement about the
  Bernoulli shift of `F_2`. Promoting `E_{phi^{j+1}(L)}` to `E_{phi^j(L)}`
  must cost at least `c > 0` at every depth `j`, where graphings may use any
  labels in `L`.
- **Depth.** The pair `(L_j, L_{j+1})` is `(L, K)` transported by `phi^j`.
  So `Q_j` is the single-stage problem `r`, with extra labels from
  `L \ L_j` allowed. These are the "deep labels".
- **Both sides are sharp.**
  - *Target* iff `r > 0` and deep labels save at most a bounded factor in
    the limit, that is `lim_j Q_j > 0`.
  - *Refutation* iff some `F_2`-Bernoulli graphings of mass tending to 0
    promote `S_{j+1}` to `S_j`, with `j` allowed to grow. No infinite
    telescoping scheme has to be assembled. The telescoping is automatic,
    by Proposition Q (2).
- **Theorem B covers only depth 0.** `r = Q_0` is the term that Theorem B of
  the chord artifact bounds from below in `b`-length, over the label set
  `L_1 \ L / L_1`. For `j >= 1`, Theorem B bounds only graphings with labels
  in `L_j`. Labels outside `L_j` have no `L_{j+1}`-double-coset length. This
  is exactly the chord artifact's survivor P3, now stated as
  `inf_j Q_j >= c r`.
- **Upgrade of chord §3(c).** Chord §3(c) records only
  "target implies `r > 0`". Proposition Q gives the converse in the form
  above: `r` is replaced by `inf_j Q_j`, and nothing else is lost.

## 4. One level at a time

`phi` maps `(L, L_j, L_{j+1})` onto `(L_1, L_{j+1}, L_{j+2})`, and
`rho|L_1` is again a Bernoulli shift, by the argument of Lemma 2.2. So
`Q_j` equals the cost of promoting `S_{j+2}` to `S_{j+1}` with graphings
inside `S_1`. Allowing graphings in all of `E_rho` gives `Q_{j+1}`. Write

```text
Q_{j+1} = (1 - eps_j) Q_j.
```

Then `eps_j` is the saving from exactly one extra level of labels,
`L \ L_1`. The target holds iff `r > 0` and `prod_j (1 - eps_j) > 0`.
This is a decomposition in which each part can fail on its own:
- (D0) `r > 0`, the single-stage floor with labels in `L`;
- (D1) a one-level bound: enlarging the ambient group from `L_1` to `L`
  saves only a summable fraction of the promotion cost.

## 5. Attempts at (D1) and where they die

**Coset-hull projection.** The natural route to (D1) is to project a
graphing that uses deep labels onto one that uses shallow labels.
- Think of a deep edge `(x, h x)` as a path in the Cayley tree of `L`. Its
  shadow in `L_1`-cosets is the list of `L_1`-coset hulls that the path
  crosses. Replace the edge by one `L_1`-labelled chord per crossing.
- **Where it dies.** The replacement charges each deep edge once per coset it
  crosses. That is up to `|h|` times the number of vertices of the Stallings
  graph of the shallow subgroup. The vertices of the Stallings graph of `L_j`
  in `L` grow like `(1 + sqrt 2)^j`:
  1, 3, 8, 20, 49, 119, 288, 696 for `j = 0..7`.
  See `experiments/fpbs-deep-promotion-2026-09-17/core_size.py` and
  `core_size_out.txt`. `|phi^j(b)|` grows at the same rate. Chords that
  replace different deep edges on shared cosets are path-dependent, so the
  multiplicity cannot be divided out.
- The projected bound is `Q_j >= r / M_j`, where `M_j` is the sharing
  multiplicity. It is unbounded in `j` and gives nothing for `inf_j Q_j`.
- The projection loses only through sharing. A proof of (D1) along these
  lines needs the P1-type bundling inequality of the chord artifact (§5.5),
  now for crossings of deep edges.

**Compact or character structure (heuristic only).** An obstruction built
from an approximate `Z/N`-cocycle, or from an action of `L` co-induced from
a compact action of `K`, would have to appear as a factor of `rho`.
- The expected barrier is that the Koopman representation of such a factor
  contains `l^2(L/K)`-type pieces. For a factor of a Bernoulli shift of
  `L`, those pieces must be weakly contained in `lambda_L`.
- This is not proved here and is not recorded as a kill.

**Zero-cost splittings.** Rewriting `Gamma_mal` by roots or cyclic HNN
moves, which have cost 0 at each step, destroys the malnormality of
`L_{j+1} <= L_j`. The known floors (Theorem B and the measured absorption
cap) both use that malnormality, so these moves give no leverage.

## 6. Not claimed

- No bound on `Q_j` for any `j >= 1`, and no bound on `eps_j`.
- Nothing for free actions other than Bernoulli. Proposition Q uses the
  stage shift `T`, which exists for every theta-invariant action.
  Corollary 2.3 uses Lemma 2.2, which is specific to Bernoulli.
