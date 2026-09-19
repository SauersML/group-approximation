# Stationary-set recurrence and relative gaps along independent random sets

swarm-0917, worker w18c (second route toward `fpbs-benjamini-schramm-universal`),
2026-09-19.

## 1. Setting

`Gamma` is a finitely generated infinite group, `S` a finite symmetric
generating set, `G = Cay(Gamma,S)` with edges `{g, gs}`. `Gamma` acts on
configurations by `(h omega)(E) = omega(h^{-1} E)`. With this convention the
cluster of `e` in `g^{-1} omega` is `g^{-1} C_g(omega)`, so

```text
e in C_inf(g^{-1} omega)   iff   g in C_inf(omega).                  (1.1)
```

`P` is any `Gamma`-invariant bond percolation law. Write `U` for the
translation-invariant event that `omega` has exactly one infinite cluster, and
`C_inf` for that cluster on `U`.

**Independent stationary sets.** Two families, both independent of `omega`.

* **(W) walk ranges.** `mu` is any probability measure on `Gamma` (no
  symmetry, no generation assumption). `xi_1, xi_2, ...` are i.i.d. `mu`,
  independent of `omega`, and `X_n = xi_1 ... xi_n`, `X_0 = e`. The visit
  count is `V = #{n >= 0 : X_n in C_e(omega)}`.
* **(R) subrelation classes.** `Gamma` acts freely and preserving a
  probability measure on a standard space `(Y, nu)`, for instance the Bernoulli
  shift `[0,1]^Gamma`. `R'` is a Borel subrelation of the orbit relation of
  `Gamma` on `Y` whose classes are a.e. infinite. The random set is
  `A(y) = {g in Gamma : (g^{-1} y, y) in R'}`, with `y ~ nu` independent of
  `omega`. It contains `e`. The count is `V = |C_e(omega) ∩ A(y)|`.

Every infinite subgroup `I` is a case of (R): take `R'` the orbit relation of
`I` on the Bernoulli shift. Freeness gives `A(y) = I`, deterministically.

**Visit thresholds.** For Bernoulli percolation, with the standard monotone
coupling and `A` independent of it,

```text
p_vis(A;G) = sup{ p : V < infinity  a.s. under P_p }.
```

Since `C_e` increases with `p`, `V` does too, so `{p : V < infinity a.s.}` is
an interval containing `[0, p_vis)`. For a subgroup, `p_vis(I;G)` is at least
the Hutchcroft--Pan relative threshold `p_c(I;G)`: below `p_c(I;G)` no cluster
meets `I` infinitely often.

## 2. Theorem 1 (recurrence separation)

**Theorem 1.** Let `P` be any `Gamma`-invariant percolation law and `A` an
independent stationary set of type (W) or (R). Then, almost surely on the
event `U ∩ {e in C_inf}`,

```text
V = infinity.
```

In words, a unique infinite cluster meets every independent stationary set
through the origin infinitely often. No Bernoulli property of `P` is used.

### 2.1 Proof for (W)

Let `Z = Omega x Gamma^N` with `lambda = P ⊗ mu^{⊗N}`, and

```text
T(omega, (xi_1, xi_2, ...)) = (xi_1^{-1} omega, (xi_2, xi_3, ...)).
```

`T` preserves `lambda`. For bounded measurable `F`,

```text
∫ F∘T dlambda = sum_s mu(s) ∫∫ F(s^{-1} omega, xi') dP(omega) dmu^{⊗N}(xi')
              = ∫ F dlambda,
```

because `P` is invariant under `s^{-1}`. By induction,
`T^n(omega, xi) = (X_n^{-1} omega, theta^n xi)`, since
`xi_{n+1}^{-1} X_n^{-1} = X_{n+1}^{-1}`. Put
`B = {(omega, xi) : omega in U, e in C_inf(omega)}`. By (1.1) and the
invariance of `U`,

```text
T^n(omega, xi) in B   iff   omega in U and X_n in C_inf(omega).
```

By the Poincaré recurrence theorem for the measure-preserving map `T` of the
probability space `(Z, lambda)`, for `lambda`-a.e. `z in B` there are
infinitely many `n` with `T^n z in B`. On `B` we have `C_inf = C_e`, so
`X_n in C_e` for infinitely many `n`. ∎

### 2.2 A lemma on aperiodic relations

**Lemma 2.** Let `R` be a countable Borel equivalence relation on a standard
probability space `(Z, lambda)` that preserves `lambda`, meaning every Borel
partial injection with graph in `R` preserves `lambda`. Suppose a.e. class is
infinite. If `B ⊆ Z` is Borel, then a.e. `z in B` has `|[z]_R ∩ B| = infinity`.

*Proof.*

1. By Feldman--Moore, `R` is the orbit relation of a countable group
   `{gamma_0 = id, gamma_1, ...}` of Borel automorphisms. Discarding a null
   invariant set, we may assume every class is infinite.
2. Let `F = {z in B : |[z] ∩ B| < infinity}`. It is Borel, because
   `[z] ∩ B = {gamma_i z : gamma_i z in B}`. For `z in F` we have
   `[z] ∩ F = [z] ∩ B`.
3. Fix a Borel linear order on `Z`, and let
   `F_0 = {z in F : z = min([z] ∩ F)}`. This set is Borel and meets each
   class at most once.
4. For `n >= 1` and `z in F_0`, let `phi_n(z)` be the `n`-th distinct point
   in the list `gamma_0 z, gamma_1 z, ...`. It exists because classes are
   infinite.
   * Each `phi_n` is a Borel injection on `F_0`: two points of `F_0` lie in
     different classes, and so do their images.
   * Its graph lies in `R`, so `lambda(phi_n(F_0)) = lambda(F_0)`.
   * The images for different `n` are disjoint.
5. Hence `sum_n lambda(F_0) <= 1`, which forces `lambda(F_0) = 0`.
6. Every `z in F` has the form `gamma_i w` with `w = min([z] ∩ F) in F_0`.
   So `F ⊆ ∪_i gamma_i(F_0)` is null. ∎

### 2.3 Proof for (R)

1. **The space.** Let `Z = Omega x Y` with `lambda = P ⊗ nu`. `Gamma` acts
   diagonally, preserving `lambda`. The action is free because the action on
   `Y` is free.
2. **The lifted relation.** Let `(z, z') in R~` iff `z' = g^{-1} z` for some
   `g in Gamma` with `(g^{-1} y, y) in R'`, where `z = (omega, y)`.
   * By freeness, `y' in [y]_{R'}` determines `g`. So `z' -> y'` is a
     bijection from `[z]_{R~}` onto `[y]_{R'}`.
   * Hence `R~` is a countable Borel equivalence relation, contained in the
     orbit relation of a `lambda`-preserving action.
   * It therefore preserves `lambda`: a partial injection with graph in the
     orbit relation is a countable union of pieces on which it is a single
     group element.
   * Its classes are a.e. infinite.
3. **The target set.** With `B = {(omega, y) : omega in U, e in C_inf(omega)}`,
   (1.1) gives, for `z in B`,

   ```text
   [z]_{R~} ∩ B = { g^{-1} z : g in A(y) ∩ C_inf(omega) }.
   ```

4. **Conclusion.** Lemma 2 gives `|A(y) ∩ C_inf(omega)| = infinity` for a.e.
   `z in B`, and `C_inf = C_e` on `B`. ∎

## 3. Corollary (separation criterion)

**Corollary 3.** For Bernoulli percolation on `G` and every independent
stationary set `A` of type (W) or (R),

```text
p_c(G) <= p_vis(A;G) <= p_u(G).
```

If `V < infinity` a.s. at some `p > p_c(G)`, then `p_c(G) < p <= p_u(G)`.

*Proof.*

1. **Lower bound.** For `p < p_c`, `C_e` is finite. In case (R),
   `V <= |C_e| < infinity`. In case (W) with a transient walk, a finite set is
   visited finitely often, so `V < infinity`. (A recurrent walk has
   `V = infinity` at every `p`, so the lower bound is stated, and used, only for
   transient walks, such as simple random walk on a nonamenable `G`.)
2. **Upper bound.** Suppose `V < infinity` a.s. at `p`. By monotonicity the
   same holds at every `p' <= p`.
3. If some `p' <= p` had a unique infinite cluster, then `theta(p') > 0` and
   `P(U) = 1`, and Theorem 1 would give `V = infinity` with probability at
   least `theta(p') > 0`, a contradiction.
4. So `[0,p]` contains no uniqueness parameter, which gives `p_u >= p`. ∎

**Placement.**

* **Expectation form.** `fpbs-green-visit-criterion-implies-nonuniqueness` is
  the case (W), `mu` uniform on `S`, with `E V < infinity` in place of
  `V < infinity` a.s. Theorem 1 replaces the Harris--FKG bound
  `tau >= theta^2` by recurrence. So it needs only almost-sure finiteness,
  allows any step law, and holds for any invariant law with a unique infinite
  cluster.
* **Subgroups.** `fpbs-relative-gap-along-any-subgroup-separates` (the
  inequality `p_c(I;G) <= p_u`) is the case (R) with `R'` the orbit relation of
  an infinite subgroup, up to the difference between `p_c(I;G)` and
  `p_vis(I;G)`.
* **Invariant finite sets.** The proof of
  `fpbs-soft-collapse-kills-relative-gap-proofs` uses the same principle for
  subgroups ("an `I`-invariant random set cannot be finite and nonempty").
  Lemma 2 is the version for relations that need not come from a subgroup.

## 4. Theorem 4 (heavy walks turn uniform decay into finite Green visits)

**Theorem 4.** Let `Gamma` be any infinite finitely generated group with word
length `|.|`, and `f : Gamma -> [0,1]` with

```text
eps(r) = sup_{|y| > r} f(y) -> 0   as r -> infinity.
```

Then there is a symmetric probability measure `mu` on `Gamma` whose walk
satisfies `sum_{n>=0} E f(X_n) < infinity`. In particular, if some `p` has
`tau_p(e,y) -> 0` as `|y| -> infinity`, then some symmetric `mu` has

```text
A_mu(p) = sum_n P_p(e <-> X_n) = E V < infinity.
```

*Proof.*

1. **The measure.** Let `nu_k` be uniform on the ball `B_{R_k}`, with
   `R_1 < R_2 < ...` to be chosen, and `c_k = 1/k - 1/(k+1)`. Put
   `mu = sum_k c_k nu_k`, which is symmetric.
2. **Sampling.** Sample the walk by i.i.d. indices `K_i ~ (c_k)` and then
   `xi_i ~ nu_{K_i}`. Let `M_n = max(K_1, ..., K_n)`. Since
   `P(K >= m) = 1/m`,

   ```text
   P(M_n < m) = (1 - 1/m)^n <= e^{-n/m}.
   ```

3. **Sup-norm bound.** Given the indices, `X_n` has law
   `nu_{K_1} * ... * nu_{K_n}`. Young's inequality
   `||alpha * beta||_inf <= min(||alpha||_1 ||beta||_inf, ||alpha||_inf ||beta||_1)`
   bounds its sup norm by `||nu_{M_n}||_inf = 1/|B_{R_{M_n}}|`. Hence

   ```text
   P(X_n in B_r) <= P(M_n < m) + |B_r| / |B_{R_m}|.
   ```

4. **The radii.** Choose `r_n` nondecreasing with `eps(r_n) <= 2^{-n}`. Set
   `m_n = ceil(sqrt n)`, and choose `R_m` increasing with
   `|B_{R_m}| >= 2^{m^2} |B_{r_{m^2}}|`; this is possible because balls are
   finite and unbounded. Since `m_n^2 >= n`, we have `r_n <= r_{m_n^2}`, and so
   `|B_{r_n}| / |B_{R_{m_n}}| <= 2^{-n}`.
5. **Summing.** Then
   `E f(X_n) <= P(X_n in B_{r_n}) + eps(r_n) <= e^{-sqrt(n)/2} + 2^{1-n}`,
   using `ceil(sqrt n) <= 2 sqrt n`. This is summable.
6. **Percolation.** For `f = tau_p(e,.)`, Fubini gives
   `E V = sum_n E tau_p(e, X_n)`. ∎

**Consequence.** Let `p_dec(G) = sup{p : tau_p(e,y) -> 0 as |y| -> infinity}`,
and `p_A^mu = sup{p : A_mu(p) < infinity}`. Then

```text
p_dec(G) <= sup_mu p_A^mu(G) <= sup_mu p_vis^mu(G) <= p_u(G).
```

So the family of walk-visit criteria, taken over all step laws, reaches uniform
connectivity decay. The Green-visit kernel `fpbs-green-visit-criterion-universal`,
which fixes `mu` uniform on `S`, is one member of the family.

**Where this stops.** The reduction is lossless but circular for the goal.
`tau_p -> 0` at some `p > p_c` already gives nonuniqueness at `p` directly,
since uniqueness forces `tau_p >= theta(p)^2` by Harris--FKG. So Theorem 4
places the hole of Section 6 below uniform decay; it does not prove the hole.

## 5. Theorem 5 (soft collapse reaches every independent stationary set)

Terminology is that of `fpbs-soft-collapse-iff-invariant-sparse-spines`. A soft
collapse family `(omega_t)` is a `Gamma`-invariant coupled family with
(S1) monotonicity, (S2) the Bernoulli joint law for `t <= p_c`, (S3) ergodicity
and insertion tolerance, and (S4) "for every `t > p_c`, `omega_t` has exactly
one infinite cluster a.s.".

**Theorem 5.** Let `G` carry a soft collapse family, and let `A` be any
independent stationary set of type (W) or (R), independent of the whole family.
Then for every `t > p_c(G)`,

```text
P( V(omega_t) = infinity ) >= theta(t) = P(e in C_inf(omega_t)) > 0.
```

*Proof.* The law of `omega_t` is `Gamma`-invariant, and by (S4) `P(U) = 1`.
Then `theta(t) > 0`: an invariant percolation with an infinite cluster has
`P(x in C_inf) = P(e in C_inf)` for all `x`, and countable additivity forces
this to be positive. Apply Theorem 1. ∎

**Corollary 6 (obstruction).** On every Cayley graph with invariant sparse
spines, consider arguments whose inputs are (a) facts about Bernoulli
percolation at `p <= p_c` and (b) properties (S1)--(S4). No such argument
proves `V < infinity` a.s. at some `p > p_c` for any independent stationary
set, of any step law and any aperiodic subrelation. For each fixed `A`,
the soft visit threshold `sup{t : V(omega_t) < infinity a.s.}` equals `p_c`.

This extends `fpbs-soft-collapse-kills-relative-gap-proofs` from subgroups to
walk ranges and to classes of arbitrary aperiodic subrelations, including
hyperfinite ones. The invariant and the failing step are unchanged:
* the invariant is invariant sparse spines;
* the failing step is the passage from data at `p_c` to finiteness at
  `p_c + delta`.

So the hole of Section 6 needs a genuinely Bernoulli supercritical input (BK or
Russo above `p_c`, deletion tolerance, Harris--FKG, or the product structure).
The spine class contains `F_2 x Z`, `T_3 x Z` and `F_2 x F_2`
(`fpbs-soft-collapse-kills-relative-gap-proofs`, pairs covered).

## 6. The new route and its hole

**Hole (`fpbs-stationary-set-relative-gap-universal`, OPEN).** On every
nonamenable Cayley graph `G` there are `p > p_c(G)` and an independent
stationary set `A`, of type (W) for some step law `mu` or of type (R) for some
aperiodic subrelation of some free pmp action, with `V < infinity` a.s. under
`P_p`.

**Route (`fpbs-bs-via-stationary-set-relative-gap`).** The hole gives `p`
and `A`, and Corollary 3 gives `p_c < p <= p_u`. ∎

**The hole is implied by each of the following.** Each implication is
immediate from the definitions and Sections 3--4.

| source | family used | why |
|---|---|---|
| `fpbs-green-visit-criterion-universal` | (W), `mu` uniform on `S` | `E V < infinity` implies `V < infinity` a.s. |
| any relative gap `p_c(G) < p_c(I;G)`, e.g. `fpbs-percolation-kesten-normal-gap`, `fpbs-percolation-schreier-kesten-gap` | (R), orbit relation of `I` | below `p_c(I;G)` no cluster meets `I` infinitely often |
| uniform decay `tau_p -> 0` at some `p > p_c` | (W), the heavy `mu` of Theorem 4 | Theorem 4 |

Via green-visit, it is also implied by every kernel that implies that claim
(PB, NC, IS, `p_c < p_(2->2)`, `tau_p in l2`; see
`fpbs-green-visit-criterion-universal`).

So the hole is weaker than every relative-threshold kernel and every
green-visit kernel now on the graph.

**Conditional converse (not claimed).** Suppose that in the nonuniqueness phase
`tau_p(e,y) -> 0` as `|y| -> infinity`. This is a connectivity-decay statement,
open in general and not used anywhere here. Then the goal implies the hole, by
Theorem 4, so under that hypothesis the hole is equivalent to the goal.

**Why this route is not blocked where the subgroup routes are.** On the class
`fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness`, which includes
Kazhdan Tarski monsters, every subgroup is blind:
`fpbs-co-amenable-subgroup-relative-threshold-is-pc` gives `p_c(I;G) = p_c` for
all infinite `I`. So both Schreier--Kesten halves, and every subgroup member of
family (R), are empty there. The hole still offers two families on that class:
walk ranges, and classes of non-subgroup aperiodic subrelations, e.g.
hyperfinite ones.

The blindness proof counts trifurcations over a Følner sequence of the
Schreier graph `I\Gamma`, pulled back to `I`-orbits. It needs `I\Gamma` to be
amenable.

* A walk range has no quotient Schreier graph.
* For a hyperfinite subrelation of a free pmp action of a nonamenable group,
  the analogue of co-amenability (an invariant mean on the classes) would make
  the orbit relation amenable, by the relation version of "amenable and
  co-amenable implies amenable".

This is a remark about the proof, not a theorem. No blindness result for
these families is known, and none is claimed.
