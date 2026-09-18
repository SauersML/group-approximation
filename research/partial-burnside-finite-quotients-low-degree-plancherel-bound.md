---
rg: 2
id: partial-burnside-finite-quotients-low-degree-plancherel-bound
kind: claim
title: Finite quotients of a partial Burnside group at the degree-c radius carry Plancherel mass at most C/|Q| on irreducibles of dimension at most c, so abelian-by-bounded quotients die at a radius uniform over all modules
distinct_from:
  bounded-degree-partial-burnside-reps-factor-through-burnside: that is the fixed-degree statement for single representations, and its clause 3 uses the regular representation of degree |Q|; this counts Plancherel mass across all irreducibles of dimension at most c at the fixed radius R_c, and yields finiteness for groups whose faithful degree is unbounded but whose irreducibles are small.
  lef-burnside-approximants-are-nonlinear-and-nonsolvable: clause 3 there kills each solvable family at some radius depending on the family, and clause 4 bounds faithful linear degree; this gives one radius R_c for all groups with an abelian subgroup of index at most c, over every module, and needs no restricted Burnside theorem.
  partial-burnside-radius-four-virtually-abelian-quotient: that exhibits an infinite quotient of Π_4(2,5) with an abelian subgroup of index <= 125; this shows every such quotient, for every module, has order bounded by C(2,5,125) once the radius reaches R_125(2,5).
  approximate-burnside-models-low-degree-trace-mass-vanishes: that is the approximate Hilbert--Schmidt statement for models of an exponent-N group with the full law; this is the exact finite statement at a finite radius.
---

**ESTABLISHED** through `partial-burnside-low-degree-plancherel-proof`.

**Setting.** Fix `m, N >= 2`, `F = F_m`, and `R_0(m,N,d)` as in
`bounded-degree-partial-burnside-reps-factor-through-burnside`. For `c >= 1` put

```text
R_c = max_(d <= c) R_0(m,N,d),
```

and let `K_c <= F` and `C(m,N,c) = [F : K_c] < infinity` be as in
`approximate-burnside-models-low-degree-trace-mass-vanishes` (the intersection
of the kernels of all representations of `B(m,N)` of degree `<= c`). Let `Q` be
a finite group with a surjection `p : F -> Q` such that `p(h)^N = 1` whenever
`1 <= |h| <= R_c`, that is a finite quotient of `Π_(R_c)(m,N)`.

**Statement.**
1. **Plancherel bound.** Every irreducible representation of `Q` of dimension
   `<= c` is trivial on `p(K_c)`, and

   ```text
   sum over irreducible pi of Q with dim pi <= c of (dim pi)^2 / |Q|
       <= C(m,N,c) / |Q|.
   ```

2. **Small irreducibles force the law.** If every irreducible representation of
   `Q` has dimension `<= c` (for instance if `Q` has an abelian subgroup of index
   `<= c`), then `p(K_c) = 1`, `|Q| <= C(m,N,c)`, and `Q` has exponent dividing
   `N`.
3. **Infinite virtually abelian quotients.** Let `Q` be any `m`-generated group,
   finite or infinite, with an abelian subgroup of index `<= c`, satisfying
   `h^N = 1` on the ball of radius `R_c`. Then `|Q| <= C(m,N,c)` and `Q` has
   exponent dividing `N`.

## Consequences

- **The Wave 4 uniformity gap, for bounded tops.** Attempt 8 of
  `hyperlinear-fg-bounded-exponent-groups-are-finite` recorded that
  abelian-by-5-group quotients of `Π_R(2,5)` die at radius 5 in every computed
  case, and that nothing bounds the death radius over all modules and all tops.
  Clause 3 bounds it over all modules and all abelian kernels for tops of order
  `<= c`: the radius `R_c(2,5)` works for every such family at once. For the
  quotient `Q ⊂ Z[ζ_5]^5 ⋊ H5` of
  `partial-burnside-radius-four-virtually-abelian-quotient`, all analogues with
  an abelian subgroup of index `<= 125`, over any module, are finite of exponent
  5 at radius `R_125(2,5)`. The open part is tops of unbounded order, and there
  the irreducible dimensions must be unbounded.
- **Invariant and death step.** The invariant is Plancherel mass on irreducibles
  of bounded dimension. A family of finite quotients of `Π_R(m,N)` that are not of
  exponent `N`, or that have unbounded order, at every radius `R`, must have
  Plancherel mass escaping to irreducibles of dimension `> c` at radius `R_c`,
  for every `c`. Every member dies at Step 1 of the route, where each small
  irreducible satisfies the law on the `R_c`-ball and so kills `K_c`.
- **LEF approximants.** If `G` is an infinite LEF group of exponent `N` with
  approximants `Q_k`, then `|Q_k| -> infinity` and each `Q_k` satisfies the law on
  larger and larger balls, so by clause 1 the Plancherel mass of `Q_k` on
  irreducibles of dimension `<= c` tends to 0 for every `c`. This is clause 1 of
  `approximate-burnside-models-low-degree-trace-mass-vanishes` for the regular
  representations of the approximants, in exact form.

## Trust surface

- **Clauses 1 and 2 of `bounded-degree-partial-burnside-reps-factor-through-burnside`**
  (ESTABLISHED): the stabilization radius `R_0(m,N,d)` and the bounded finite image.
- **Standard facts, not re-read:** character theory of finite groups (the sum of
  `(dim pi)^2` over the irreducibles of a finite group is its order; the regular
  representation is faithful); Frobenius reciprocity; finitely generated
  abelian groups; subgroups of finite index in finitely generated groups are
  finitely generated.

No restricted Burnside theorem is used, and no bound on `R_c` or `C(m,N,c)` is
claimed; both come from Noetherianity and Jordan's theorem.
