---
rg: 2
id: dickson-returns-force-compressions-in-canonical-full-groups
kind: claim
title: In CT_P(Z), nV and every group of canonical box maps, an invariant probability that charges the set of points whose forward degree walk is bounded below forces a compression or an open periodic box (Dickson's lemma); so minimal elements have almost every orbit expanding without bound in some prime, forward and backward
distinct_from:
  ct-p-z-order-is-decided-by-elliptic-reduction: that reduces order to elliptic primes and shows minimal elements of CT_{3}(Z) are non-elliptic in both primes; this constrains the degree walk of every invariant measure of a minimal (or compression-free) element, through a well-quasi-order argument.
  hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z: that closes hyperbolic orbits (all exponents nonzero); this needs no exponents and covers the zero-exponent (parabolic) regime left open there.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - ct-p-z-order-is-decided-by-elliptic-reduction
  - hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z
```

**ESTABLISHED** (lane proof, elementary: Poincaré recurrence and Dickson's lemma; not independently
reviewed; no priority claimed). **OPEN:** does `CT_{3}(Z)` have a minimal element? Items 2–3
constrain one heavily but neither build nor exclude it. Kourovka 17.58 stays OPEN.

## Setting

- `g ∈ 𝒞_S` is a canonical box map on a clopen `X ⊆ Ẑ_S × Ω`, as in
  `ct-p-z-order-is-decided-by-elliptic-reduction`. This covers `CT_P(Z)`, `S = P′`.
- The same proof works for Brin's `nV`, with product dyadic boxes and Brin's level cocycle.
- The one property used: **a canonical map of a box onto itself is the identity**. Composites and
  restrictions of canonical maps are canonical.
- `d = (d_q)_{q∈S}` is the degree cocycle, with `S_j d(x) = d(g^j)(x) ∈ Z^S`, and
  `R_q = q^{−v_q(M*)}`.
- For `N ≥ 0` put `F_N = {x : S_j d(x) ≥ −N·𝟙 for all j ≥ 0}` (componentwise). This is the set of
  points whose forward walk never expands any coordinate by more than `q^N`.

## Statement

1. **Dickson returns.** Suppose some `g`-invariant probability `ν` and some box `B` with `q`-radii
   `R_q q^{−N}` satisfy `ν(F_N ∩ B) > 0`. Then there is `k ≥ 1` with either `g^k(B) ⊊ B` (a
   compression) or `g^k|_B = id`.
2. **Compression-free elements.** If `g` has no compression, then for every invariant probability
   `ν`, `ν`-almost every point of `∪_N F_N` lies in the interior of the periodic set. So every
   ergodic measure not carried by `int Per(g)` has, at almost every point, a prime `q` with
   `inf_{j≥0} S_j d_q(x) = −∞`. The same holds backward, for `g^{−1}`.
3. **Minimal elements.** If `g` is minimal on an infinite clopen `U`, then `ν(F_N) = 0` for all `N`
   and all invariant `ν`, and the same for `g^{−1}`.
   - So almost every orbit expands some prime without bound in forward time, and some prime
     without bound in backward time.
   - For `CT_{3}(Z)` and an ergodic `ν` of such `g`: by the closing lemma `λ_2 λ_3 = 0`.
     - If `λ_q ≥ 0` for both primes, then some zero-exponent prime has forward sums unbounded
       below `ν`-a.e.
     - Symmetrically, if `λ_q ≤ 0` for both, some zero-exponent prime has backward sums unbounded.
   - A measurable coboundary `d_q = u∘g − u` whose transfer `u` is bounded below cannot play that
     role.

## Proof of item 1

- **The box never splits.** Let `A = F_N ∩ B`. For `y ∈ A`, the image `g^j(B)` has `q`-radius
  `R_q q^{−N−S_j d_q(y)} ≤ R_q` for every `j ≥ 0`. By induction each image lies in one piece, so
  `g^j` is canonical on `B` for all `j ≥ 0`.
- **The key step.** Let `y ∈ A` and `k ≥ 1`, with `g^k y ∈ B` and `S_k d(y) ≥ 0` componentwise.
  Then `g^k(B)` is a box containing a point of `B`, with radii at most those of `B`, so
  `g^k(B) ⊆ B` in every coordinate by the ultrametric inequality.
  - If all radii are equal, `g^k(B) = B`, and `g^k|_B` is a canonical self-map of a box, hence the
    identity.
  - Otherwise `g^k(B) ⊊ B`.
- **Returns.** By Poincaré recurrence, `ν`-a.e. `x ∈ A` returns to `A` at times
  `0 = r_0 < r_1 < r_2 < …`. Put `W_n = S_{r_n} d(x) ∈ Z^S`.
  - Since `x ∈ F_N`, every `W_n ≥ −N·𝟙`.
  - For `n < n′`, apply the key step to `y = g^{r_n} x ∈ A` and `k = r_{n′} − r_n`, so that
    `S_k d(y) = W_{n′} − W_n`.
  - So if the conclusion of item 1 fails, then `W_{n′} − W_n` is never `≥ 0` componentwise.
- **Dickson's lemma.** `(N^S, ≤)` is a well-quasi-order, so the infinite sequence `W_n + N·𝟙 ∈ N^S`
  has `n < n′` with `W_n ≤ W_{n′}`. Contradiction. `∎`

## Proofs of items 2 and 3

- **Item 2.** With no compression, item 1 makes every such `B` a periodic box. `F_N` is covered, up
  to a `ν`-null set, by the boxes `B` of radii `R_q q^{−N}` with `ν(F_N ∩ B) > 0`.
  - The complement of `∪_N F_N` is exactly the set where `min_q inf_j S_j d_q = −∞`.
  - For `g^{−1}`, use `d(g^{−1})(x) = −d(g)(g^{−1} x)`.
- **Item 3.** A minimal `g` on infinite `U` has no compression, because `ν(g^k B) = ν(B)` and `ν`
  has full support. It also has no open periodic set. So item 2 applies with `int Per = ∅`.
  - The closing lemma excludes `λ_2, λ_3 ≠ 0`.
  - If both `λ_q ≥ 0`, a prime with `λ_q > 0` has forward sums tending to `+∞`, hence bounded below.
    So the prime supplied by item 2 has zero exponent.
  - A coboundary `u∘g^j − u ≥ inf u − u(x)` is bounded below along the orbit, so it cannot supply
    `−∞`.

## What this says about a SMART analogue in CT_{3}(Z)

- **Two separate one-prime conditions do not suffice.** Along almost every orbit the joint degree
  walk in `Z^2` must keep escaping the translated positive quadrant, in both time directions. Two
  separately non-elliptic primes are not enough: the escape has to happen jointly.
- **Consistency with SMART.** Inside `2V`, SMART satisfies this, because its level walk `(k, −k)` is
  the head position, which is unbounded (`smart-trace-full-group-embeds-in-brin-thompson-2v`). So
  this obstruction alone does not separate `CT_{3}(Z)` from `2V`.
- **The remaining separator.** SMART preserves Haar measure on `C^2` (level change `(k,−k)`, zero
  total). In `CT_{3}(Z)` the Haar Radon–Nikodym cocycle is `d_2 log 2 + d_3 log 3`. That map is
  injective on `Z^2`, so no infinite-order element preserves Haar measure.
  - Any minimal element of `CT_{3}(Z)` is therefore Haar-singular, with zero-mean but nonzero
    `log(slope)`.
  - Exploiting that, together with the rational points (denominators prime to 6 are invariant, and
    bounded real height is finite), is the next step on the exclusion side.

**Lesson for general BH.**
- **A well-quasi-order bound.** In any full group whose canonical self-maps are identities
  (arithmetic `CT_P(Z)`, product `nV`, k-graph groupoids), the degree lattice `Z^k` with the
  product order is a well-quasi-order. So a recurrent orbit whose forward walk is bounded below must
  eventually return dominated. That return is a compression or an identity.
- **Consequence.** Minimal, compression-free and undecidable dynamics in these hosts must expand
  without bound, in some coordinate and in both time directions, along almost every orbit.
- **Scope.** The criterion is uniform across hosts and cheap to check. It is the right filter for
  candidate writers, minimal elements and exotic subgroups.
