---
rg: 2
id: thompson-t-unitary-gap-implies-orthogonal-and-symplectic-gaps
kind: claim
title: The projective-unitary level-T gap implies the orthogonal and symplectic ones, because a dense Z/4 * Z/3 pair in SO(k) or Sp(m) can be perturbed inside its SU conjugacy classes to a dense SU pair
distinct_from:
  thompson-t-gap-on-dense-orthogonal-adjoint-images: that is the orthogonal gap as an open hole; this derives it from the unitary gap with constant eps_SU/2 and proves nothing unconditional.
  thompson-t-gap-on-dense-symplectic-adjoint-images: that is the symplectic gap as an open hole; this derives it from the unitary gap with constant eps_SU.
  thompson-t-gap-on-dense-projective-unitary-images: that is the unitary gap itself, still open; this is the implication from it to the other two families.
  thompson-v-gap-on-dense-orthogonal-adjoint-images: that is the V-level orthogonal gap over S4 *_Z2 S3; the transverse count here uses the free product Z/4 * Z/3 and has not been done for the amalgam.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that is the reduction of T not MF to a gap over all unitary pairs; this compares gaps between two classes of dense adjoint images.
artifacts:
  - research/thompson-t-unitary-gap-implies-classical-gaps-proof.md
  - experiments/thompson-t-classical-gap-collapse-2026-09-17/h1_census.py
---

**ESTABLISHED** by `thompson-t-unitary-gap-implies-classical-gaps-proof`
(written proof, not yet refereed).

## Setting

The notation is that of `thompson-t-witnesses-are-dense-in-simple-adjoint-groups` and
`thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`:

```text
Gamma0 = Z/4 * Z/3 = < a, b | a^4, b^3 >,
r_1 = [bab, a^2 bab a^2],   r_2 = [bab, a^2 b^2 a^2 bab a^2 b a^2],   r_P = (ba)^5.
```

For a compact simple Lie algebra `h` with an invariant inner product, and a homomorphism
`tau : Gamma0 -> Inn(h)`, put

```text
D_h(tau) = max( ||tau(r_1) - 1||, ||tau(r_2) - 1||, ||tau(r_P) - 1|| ),
```

where `||.||` is the operator norm on `h`. The norm does not depend on which invariant inner product
is chosen, because `h` is simple.

`Gap_T(X)` says: there is `eps > 0` such that `D_h(tau) >= eps` for every `k` with `h = X(k)` simple
and every `tau` with dense image in `Inn(h)`. Here `X` is one of `SU`, `SO`, `Sp`.

## Statement

1. **(Orthogonal.)** Suppose `Gap_T(SU)` holds with constant `eps_SU`. Then `Gap_T(SO)` holds with
   constant `eps_SU / 2`.
2. **(Symplectic.)** Suppose `Gap_T(SU)` holds with constant `eps_SU`. Then `Gap_T(Sp)` holds with
   constant `eps_SU`.
3. **(Perturbation lemma, unconditional.)** Take `n = k` with `k >= 3` and `k != 4`, or `n = 2m`
   with `m >= 2`. Let `K0` be
   `SO(k)` inside `SU(k)`, or `Sp(m)` inside `SU(2m)`. Let `A, B` in `K0` have central fourth and
   third powers, and suppose they generate a dense subgroup of `K0`. Then there are pairs `(A', B')`,
   arbitrarily close to `(A, B)`, such that:
   - `A'` is `SU(n)`-conjugate to `A`, and `B'` is `SU(n)`-conjugate to `B`;
   - `<A', B'>` is dense in `SU(n)`.

   The pairs with this property are dense near `(A, B)` in `C_A x C_B`, the product of the two
   conjugacy classes.
4. **(Transverse count.)** Write `su(n) = h (+) p`, where `p` is the orthogonal complement of `h`.
   Then `p = i Sym^2_0(R^k)` for `SO`, and `p` is the traceless part of `Lambda^2` for `Sp`. Under the
   hypotheses of item 3,

   ```text
   dim H^1(Gamma0; p) = dim p - dim p^A - dim p^B >= 1 .
   ```

   This number is the codimension, in `C_A x C_B`, of the non-dense pairs near `(A, B)`.
5. **(Norm comparison.)** For `g` in `SO(k)` with `k >= 3`,
   `||Ad_su(g) - 1|| <= 2 ||Ad_so(g) - 1||`. For `g` in `Sp(m)`,
   `||Ad_su(g) - 1|| <= ||Ad_sp(g) - 1||`.

## Consequence

By item 1 of `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`, `T` is not MF if and only if
all three of `Gap_T(SU)`, `Gap_T(SO)` and `Gap_T(Sp)` hold. By items 1 and 2 above, this becomes:

```text
T is not MF   <=>   Gap_T(SU).
```

So the route `thompson-t-not-mf-via-classical-adjoint-trichotomy` has one open hole instead of three.
That hole is `thompson-t-gap-on-dense-projective-unitary-images`. The route is recorded as
`thompson-t-not-mf-via-projective-unitary-gap`.

## What the proof uses

- Jordan's theorem on finite linear groups.
- Richardson's rigidity of semisimple subalgebras.
- Sard's theorem.
- An exact eigenvalue-multiplicity count. The count uses only two consequences of density: `K0` has
  no common eigenvector on `C^n`, and `p` has no nonzero `Gamma0`-fixed vector.

No property of `T` is used beyond the definition of the three relators. The census artifact checks
item 4 over every multiplicity pattern for `k <= 200` and `m <= 100`. It finds no violation. This is
exact integer arithmetic and is not needed for the proof.

## Scope

- The argument is specific to a free product of two finite cyclic groups. For those groups,
  `H^1(Gamma0; p)` has the closed form above, with no third fixed-space term.
- For the triangle-level gaps, `Delta(4,3,5)`-homomorphisms, the pentagon class `(ba)` is also fixed.
  The count then acquires a term `- dim p^(ba)`. Whether it stays positive is not settled here.
- For the V-level amalgam `S4 *_Z2 S3`, the count is
  `dim p - dim p^(S4) - dim p^(S3) + dim p^(Z2)`. It is not settled here.

## Attempts

- (swarm-0917-w21-w21-ptl-last1) Generic perturbation inside `SU` conjugacy classes, with the exact
  transverse `H^1` count. The count is proved for all ranks, and the census over `k <= 200`,
  `m <= 100` found no counterexample.
