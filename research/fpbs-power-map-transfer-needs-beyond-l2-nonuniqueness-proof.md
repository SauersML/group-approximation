---
rg: 2
id: fpbs-power-map-transfer-needs-beyond-l2-nonuniqueness-proof
kind: route
title: The power map is dominated by p to the L, the l2 thresholds sit below sqrt(p_c), and the nonbacktracking bound sits below 1/sqrt(d-1)
target: fpbs-power-map-transfer-needs-beyond-l2-nonuniqueness
requires:
  - fpbs-generating-set-threshold-comparison
  - fpbs-lq-threshold-power-monotonicity
  - fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu
  - fpbs-amenable-wq-normal-pu-is-relative-pc
  - fpbs-nb-spectral-deficit-obstruction
  - fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu
  - fpbs-regular-tiling-edge-isoperimetric-constant
  - fpbs-expansion-thinning-threshold
---

Notation is as in the target. All maps below are continuous, strictly
increasing bijections of `[0,1]`.

## Step 0: the power map is below `p^L`

The comparison map is `phi(p) = (1-(1-p)^(1/M))^L` with `M >= 1`. For
`x in [0,1]` we have `x^(1/M) >= x`. Put `x = 1-p`: then
`1-(1-p)^(1/M) <= p`, so `phi(p) <= p^L`.

**Composition.** Suppose `f(p) <= p^a` and `g` is increasing with
`g(y) <= y^b`. Then `g(f(p)) <= f(p)^b <= p^(ab)`.

**The inverse.** If `psi(y) <= y^L'`, then `psi^(-1)(x) >= x^(1/L')`. To see
this, put `y = psi^(-1)(x)`: then `x = psi(y) <= y^L'`.

**Word length.** Let `L` be the longest word used for `S_G` over `S_T`.
Suppose `S_G ⊄ S_T`, and pick `s ∈ S_G \ S_T`.

- Since `S_T` is symmetric, `s^(-1) ∉ S_T` either.
- Since `s ≠ e`, the word chosen for `{s, s^(-1)}` has length at least 2.

So `L >= 2`. In the same way, `S_T ⊄ S_G` gives `L' >= 2`. When
`S_G ⊆ S_T` the bound is the nested monotone one, `phi = id`, so `L = 1`; the
case `S_T ⊆ S_G` gives `psi = id` and `L' = 1`. Since `S_T ≠ S_G`, at least
one of `L, L'` is at least 2.

## Step 1: the margin law (target item 1)

**One step.** The certificate asserts

```text
psi^(-1)(p_c(T))  <  phi(p_u(T)).
```

Apply the increasing map `psi`:

```text
p_c(T)  <  psi(phi(p_u(T)))  <=  p_u(T)^(L L').
```

Here `L L' >= 2`, and `p_u(T) <= 1`, so `p_c(T) < p_u(T)^2`.

**Chains.** Drop the steps with `S_(i+1) = S_i`; they are trivial. What
remains is

```text
psi_(m-1)^(-1) ∘ ... ∘ psi_0^(-1) (p_c(T))  <  phi_(m-1) ∘ ... ∘ phi_0 (p_u(T)).
```

Apply `psi_0 ∘ ... ∘ psi_(m-1)`:

```text
p_c(T)  <  Psi(p_u(T)),   with   Psi(p) <= p^N,   N = prod_i L_i L'_i >= 2.
```

**Relative variant.** For an amenable wq-normal `I`, the imported equality
`p_c(I;X) = p_u(X)` holds on every Cayley graph `X` of `Gamma`. The
comparison gives `p_c(I;G') >= phi(p_c(I;G))`, which is item 2 of
`fpbs-generating-set-threshold-comparison` rewritten. Nested monotonicity of
`p_c(I;.)` holds because a superset of edges is monotone. So the relative
bounds have exactly the form above, and the same conclusion follows.

**Conclusion.** `mu(T) > 0`. Now import `p_(2->2) <= p_2 <= sqrt(p_c)` from
item 3 of `fpbs-lq-threshold-power-monotonicity`. This gives
`p_u(T) > sqrt(p_c(T)) >= p_2(T) >= p_(2->2)(T)`.

## Step 2: void on the Hutchcroft--Pan class (target item 2)

If `p_u(T) <= p_2(T)`, then `p_u(T)^2 <= p_2(T)^2 <= p_c(T)` by the imported
`p_2 <= sqrt(p_c)`. So `mu(T) <= 0`, and by Step 1 no pure certificate starts
at `T`.

For `T = T_k □ H`, with `k >= 3` and `H` an infinite amenable Cayley graph,
Theorem 1.2 of Hutchcroft--Pan (imported in
`fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu`) gives
`p_u(T) = p_(2->2)(T)`. The imported chain gives `p_(2->2)(T) <= p_2(T)`, so
the hypothesis holds and `p_u(T) <= sqrt(p_c(T))`.

For the Cayley graphs listed in the target, identify them as follows:

- The free group `F_n` with a free basis has the `2n`-regular tree as its
  Cayley graph, and `2n >= 4`.
- `(Z/2)^(*k)` with its standard involutions has `T_k` as its Cayley graph.
- A disjoint union of generating sets of the two factors of a direct product
  has the Cartesian product of the two Cayley graphs as its Cayley graph.

## Step 3: spectral sources are impossible (target item 3)

Let `d = |S_T| >= 3` and `b = d-1`.

**Lower bound on `p_c`.** There are at most `d b^(n-1)` self-avoiding paths
of length `n` from `o`. If `o <-> x`, then some self-avoiding path from `o`
to `x` is open. A union bound over these paths gives

```text
E_p|K_o|  <=  1 + sum_(n>=1) d b^(n-1) p^n  <  infinity   for p < 1/b.
```

Therefore `p_c(T) >= 1/b`.

**Upper bound on the spectral certificate.**

- On `[2 sqrt b, infinity)` the function `sigma` is increasing, and
  `sigma(2 sqrt b) = sqrt b`.
- `Lambda_T >= 2 sqrt b`, by definition.

Hence `1/sigma(Lambda_T) <= 1/sqrt b`, and so
`(1/sigma(Lambda_T))^2 <= 1/b <= p_c(T)`.

**Comparison with `1/||A||`.** By Kesten, `||A_T|| >= 2 sqrt b` on every
infinite `d`-regular graph, so `Lambda_T = ||A_T||`. Also `sigma(x) <= x`. So
`1/||A_T|| <= 1/sigma(Lambda_T)`.

**Conclusion.** Replacing `p_u(T)` by either spectral lower bound, the
certified quantity `(lower bound)^2 - p_c(T)` is `<= 0`. So no spectral bound
can certify `mu(T) > 0`.

## Step 3a: the calibration sources

**Infinitely many ends.** A transitive graph with infinitely many ends has
`p_u = 1`. This is recalled and standard: see Lyons--Peres, *Probability on
Trees and Networks*, Chapter 7. A nonamenable such graph has
`p_c <= 1/(1+h) < 1`, by `fpbs-expansion-thinning-threshold`. So
`mu = 1 - p_c > 0`. This item is calibration only: no other claim depends on
it.

**Surface groups.** Take the `{4g,4g}` tiling, `g >= 2`. It is self-dual,
since the dual of `{p,q}` is `{q,p}`, so `G† ≅ G`.

- `fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu` gives
  `p_c(G†) = 1 - p_u(G)`, so `p_u = 1 - p_c`.
- `fpbs-regular-tiling-edge-isoperimetric-constant` gives
  `h = sqrt((4g-2)^2 - 4) >= sqrt 32`.
- `fpbs-expansion-thinning-threshold` then gives
  `p_c <= 1/(1 + sqrt 32) < 0.1503`.

Hence `mu = (1-p_c)^2 - p_c > 0.8497^2 - 0.1503 > 0.57`.

## Step 4: hybrid certificates (target item 4)

Assume `mu(T) <= 0`.

**`p_u` transferred with `S_G ⊄ S_T`.** Then `L >= 2`, and the certificate
needs

```text
p_c(G)  <  phi(p_u(T))  <=  p_u(T)^2  <=  p_c(T).
```

**`p_c` transferred with `S_T ⊄ S_G`.** Then `L' >= 2`, and the certificate
needs

```text
p_u(G)  >  psi^(-1)(p_c(T))  >=  p_c(T)^(1/2)  >=  p_u(T),
```

by Step 0. In both cases the intrinsically certified side must beat the
source's own opposite threshold. `QED`

## Conditional extension

Claim E of `fpbs-relative-threshold-is-quotient-l2-threshold` is OPEN. Its
consequence C2 would give `p_(2->2) = p_u` for every Cayley graph with an
infinite amenable normal subgroup. Step 2 would then apply verbatim. This
extension is not used in the established items.
