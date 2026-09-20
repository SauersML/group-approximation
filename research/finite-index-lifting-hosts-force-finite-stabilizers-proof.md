---
rg: 2
id: finite-index-lifting-hosts-force-finite-stabilizers-proof
kind: route
title: Build the Mackey space of a lifting host, embed the host set as a stabilizer-transversal, and kill it with the finite fiber measure
target: finite-index-lifting-hosts-force-finite-stabilizers
requires:
  - manzoor-isotropy-has-no-positive-finite-type-corner
---

**Standard facts used.**
* (LN) Lusin–Novikov: a Borel set with countable sections is a countable union of Borel graphs. Consequently, images
  of Borel sets under countable-to-one Borel maps are Borel, and a Borel count of section points is Borel.
* (DIS) Disintegration. Let `p : (Y, m) -> X` be Borel with `m` finite, and `nu' = p_* m`. Then there are finite
  measures `m_x` on `p^(-1)(x)` with `m = ∫ m_x d nu'(x)`, unique up to `nu'`-null sets. If a countable group acts
  on `Y` and on `X`, preserving `m`, and `p` is equivariant, then uniqueness gives `g_* m_x = m_(g x)` for
  `nu'`-a.e. `x`, simultaneously for all `g`.
* (PT) Let `m_x` be a finite measure, `H` an infinite countable group preserving it, and `D` a measurable set with
  `h D ∩ D = ∅` for every `h ≠ 1` in `H`. Then `m_x(D) = 0`. Indeed the translates `h D` are pairwise disjoint and
  have equal measure, and infinitely many of them fit in finite total mass.

Fix a free host `(Lambda ↷ (Z, zeta), A, S, r)` of `R` that lifts through `Lambda ↷ (X, mu)`. Enumerate
`Lambda = {lambda_0 = 1, lambda_1, lambda_2, ...}`. Discarding null sets, assume the following hold everywhere:
freeness on `Lambda A`, class-bijectivity of `r` on `S`-classes, and the lifting identity `c(a, a') r(a) = r(a')`.
This is legitimate: all three fail on `S`-saturated or `Lambda`-saturated null sets, and saturations of null sets
are null because the relations are countable and measure-preserving.

**Step 0 (`R ⊆ R_Lambda(X)`).** `r` maps each `S`-class onto an `R`-class. By lifting, each point `r(a')` of that
class equals `c(a, a') r(a)`. So `R`-classes lie in `Lambda`-orbits.

## Step 1: the Mackey space

Let `Y` be the set of pairs `(z, i)` with `z ∈ Lambda A` and `i ∈ N`, such that:
* `lambda_i z ∈ A`;
* `lambda_j z ∉ [lambda_i z]_S` for every `j < i`.

So `(z, i)` records the `S`-class `[lambda_i z]_S ⊆ Lambda z ∩ A`, through its least-index representative. Each
`S`-class inside `Lambda z ∩ A` is recorded exactly once, so the fiber of `Y` over `z` has exactly `k(z)` points.
`Y` is Borel because `S` and the action are Borel. `k(z) = #{i : (z, i) ∈ Y}` is Borel by (LN). Put
`m = zeta ⊗ counting` on `Y`. Then `m(Y ∩ (W × N)) = ∫_W k d zeta` for Borel `W ⊆ Lambda A`, and in particular
`m(Y) = M`.

**Action.** For `g ∈ Lambda` and `(z, i) ∈ Y`, set `g · (z, i) = (g z, i')`. Here `i'` is the least index with
`lambda_(i') g z ∈ [lambda_i z]_S`. It exists because `lambda_i z = (lambda_i g^(-1)) (g z)`.
* This is a Borel bijection from the fiber over `z` onto the fiber over `g z`. Both fibers index the same set of
  `S`-classes, since `Lambda g z = Lambda z`.
* `h · (g · (z, i)) = (h g) · (z, i)`, since both sides record the class `[lambda_i z]_S` at the point `h g z`.
* `m` is invariant, because `zeta` is invariant and the fiber maps are bijections.

## Step 2: the equivariant map to X

Define `p(z, i) = lambda_i^(-1) r(lambda_i z)`.

*Equivariance.* Put `a = lambda_i z` and `a' = lambda_(i') g z`, so that `(a, a') ∈ S` and
`a' = (lambda_(i') g lambda_i^(-1)) a`. Lifting gives `r(a') = lambda_(i') g lambda_i^(-1) r(a)`. Hence

```text
p(g · (z, i)) = lambda_(i')^(-1) r(a') = g lambda_i^(-1) r(a) = g p(z, i).
```

*Absolute continuity.* Let `nu' = p_* m` on a `Lambda`-invariant piece of finite mass. For Borel `F ⊆ X`,

```text
m(p^(-1) F) <= sum_i zeta{ z : lambda_i z ∈ A, r(lambda_i z) ∈ lambda_i F }
            =  sum_i zeta(A ∩ r^(-1)(lambda_i F))
            =  sum_i zeta(A) mu(lambda_i F)
            =  sum_i zeta(A) mu(F).
```

This uses that `zeta` is `Lambda`-invariant, that `r_* zeta_A = mu`, and that `Lambda` preserves `mu`. So
`nu' ≪ mu`.

## Step 3: the host set is a stabilizer-transversal

Define `j : A -> Y` by `j(a) = (a, i(a))`, where `i(a)` is the least index with `lambda_(i(a)) a ∈ [a]_S`. Then:
* `j` is Borel and injective, since its first coordinate is `a`;
* `m(j(B)) = zeta(B)` for Borel `B ⊆ A`, since the fiber measure is counting;
* `p(j(a)) = r(a)`, by lifting applied to the pair `(a, lambda_(i(a)) a) ∈ S`.

**Key lemma.** Let `a ∈ A`, and let `h ∈ Stab_Lambda(r(a))` satisfy `h · j(a) ∈ j(A)`. Then `h = 1`.

*Proof.* `h · j(a)` is a point with first coordinate `h a`, recording the class `[a]_S`. If it equals `j(b)`, then
`b = h a`, and `j(b)` records `[b]_S`, so `[h a]_S = [a]_S`. Thus `(a, h a) ∈ S` with `c(a, h a) = h`. Lifting
gives `r(h a) = h r(a) = r(a)`. The class `[a]_S` maps bijectively onto `[r(a)]_R`, so `h a = a`, and freeness
gives `h = 1`. ∎

**Corollary.** For `x ∈ X`, put `D_x = j(A) ∩ p^(-1)(x)`. Then `h D_x ∩ D_x = ∅` for `h ∈ Stab_Lambda(x) \ {1}`.

*Proof.* A point `j(a) ∈ D_x` has `r(a) = x`, so `h ∈ Stab_Lambda(r(a))`. If `h · j(a) ∈ D_x`, the key lemma gives
`h = 1`. ∎

## Step 4: the death step

Let `E = {x ∈ X : Stab_Lambda(x) infinite}`, a `Lambda`-invariant Borel set. For `n ∈ N`, put
`W_n = {z ∈ Lambda A : k(z) <= n}` (in part 2, `W = Lambda A` instead) and `B = A ∩ W_n ∩ r^(-1)(E)`.

* `W_n` is `Lambda`-invariant, so `Y_n = Y ∩ (W_n × N)` is a `Lambda`-invariant subspace. It has
  `m(Y_n) <= n zeta(W_n) <= n zeta(Z) < infinity` in part 1, and `m(Y_n) <= M < infinity` in part 2.
* `j(B) ⊆ Y_n`, and `p(j(B)) ⊆ E`.
* Apply (DIS) to `p : (Y_n, m) -> X`. For `nu'`-a.e. `x`, every `h ∈ Stab_Lambda(x)` preserves `m_x`.
* For `nu'`-a.e. `x ∈ E`, the group `Stab_Lambda(x)` is infinite and preserves the finite measure `m_x`. By the
  corollary, `j(B) ∩ p^(-1)(x) ⊆ D_x` has disjoint translates. So (PT) gives `m_x(j(B) ∩ p^(-1)(x)) = 0`.
* For `x ∉ E` the section is empty. Hence

```text
zeta(B) = m(j(B)) = ∫ m_x(j(B) ∩ p^(-1)(x)) d nu'(x) = 0.
```

Here `nu' ≪ mu` (Step 2) is used only to know that the `nu'`-null exceptional set from (DIS) does not matter. It
is null for the measure against which we integrate.

## Step 5: conclusions

* **Part 1.** Taking the union over `n`, `zeta(A ∩ {k < infinity} ∩ r^(-1)(E)) = 0`. That is, for a.e. `a` with
  `Stab_Lambda(r(a))` infinite, `k(a) = infinity`.
  * If `k < infinity` a.e., then `zeta(A ∩ r^(-1) E) = 0`, so `mu(E) = zeta_A(r^(-1) E) = 0`.
  * The full restriction has `k ≡ 1`.
* **Part 2.** Use `W = Lambda A` and the finite mass `M` in Step 4. This gives `zeta(A ∩ r^(-1) E) = 0`, hence
  `mu(E) = 0`.
* **No invariant probability on the transversal space.** This is used in part 3. Suppose a `Gamma`-invariant
  probability on `{(x, T)}` gave positive mass to infinite-stabilizer points.
  * Disintegrating over `x` gives `Stab(x)`-invariant fiber laws. The unique point of `T ∩ Stab(x)` then has a law
    on `Stab(x)` that is invariant under right translation, which is impossible on an infinite discrete group.
  * The same conclusion is part 1 applied to the full-restriction host on `{1 ∈ T}`.

## Step 6: the examples of part 3

* **Torus.** The action `(m, n)(x, y) = (x + m alpha, y + n beta)` is free for rationally independent
  `alpha, beta, 1`. Its `S`-classes are the `Z × 0`-orbits, and `r(x, y) = x` maps each bijectively onto an
  `alpha`-rotation orbit. `c = (m, 0)` gives `c · r(z) = x + m alpha = r(z')`, which is lifting. Stabilizers on
  `X` are `0 × Z`. Each `Z^2`-orbit contains the countably many `S`-classes `{(x + m alpha, y + n beta) : m}`,
  one for each `n`. So `k ≡ infinity`, which is consistent with part 1.
* **Transversal space.** Freeness: if `g x = x` and `T g^(-1) = T`, then the point `tau` of `T ∩ Stab(x)` satisfies
  `tau g^(-1) ∈ T ∩ Stab(x)`, so `tau g^(-1) = tau` and `g = 1`. The orbit of `(x, T)` meets `{1 ∈ T}` exactly in
  `{(t x, T t^(-1)) : t ∈ T}`. This is the re-rooting class, so the host relation is the full restriction and
  `k ≡ 1`. Lifting holds with `c = t`. The deterministic transversal `T = Z × 0` of the torus example is
  re-rooting invariant.

## What the proof does not reach

* **Non-lifting hosts.** `Lambda` need not act on `X`. The Mackey space `Y` still exists, but `p` is defined only
  through a `Lambda`-action on `X`.
* **Infinite-index lifting hosts.** When `k = infinity`, `Y` has infinite mass on every piece, and (PT) is
  unavailable. The torus example shows such hosts exist for amenable relations with infinite isotropy.

For `R_mu` the open cases are therefore: a non-lifting host, or a lifting host with `k = infinity` through an action
with infinite isotropy.
