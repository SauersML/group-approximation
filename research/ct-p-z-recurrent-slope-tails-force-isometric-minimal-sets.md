---
rg: 2
id: ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets
kind: claim
title: "For g in CT_P(Z) acting on the profinite integers, periodic points are rational numbers or lie in classes fixed pointwise by a power of g; and if some orbit in a clopen g-invariant set U has a slope potential that is recurrent from below at bounded scale, then g has an equicontinuous (affine-isometric) minimal set in U, so (U, g) has no infinite minimal subshift factor"
distinct_from:
  ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits: that is the group statement on a mixed ray (finite iff frozen everywhere, periodic infinite needs a sweeping orbit), with the hyperbolic-return lemma under the hypothesis that every coordinate is hyperbolic; this is the single-element statement for every slope lattice, allows isometric coordinates, and turns a return into an equicontinuous minimal set instead of a fixed point.
  aperiodic-full-groups-lift-along-factor-maps: that lifts a full group from a factor to an extension; this says which elements of CT_P(Z) can have an infinite minimal subshift as a factor at all.
  conway-amusical-permutation-is-the-full-three-shift: that records the open gate (a T in CT_P(Z) with a clopen invariant set whose minimal subsets are not equicontinuous) and settles it for V; this gives the dynamical signature any T passing the gate must have, and shows that aperiodicity alone is not the obstruction.
  ct-z-north-south-element-has-no-finite-cycles: that proves the north-south element has no finite cycles on Z; this uses it on the profinite integers of CT_{3}(Z), where it becomes aperiodic.
---

**ESTABLISHED** (lane proof by bh-1946; not independently reviewed). Elementary. No
priority claimed; the ingredients (hyperbolic fixed points of contractions, closing
returns) are standard, and only the bookkeeping for canonical class maps is new here.
Kourovka 19.46 and 17.58 (S. Kohl) stay **OPEN**; this node constrains one route to them
(`ct-z-periodic-groups-via-subshift-factors-of-elements`).

## Setting

- `P` is a finite set of odd primes, `P' = P ∪ {2}`, `Ẑ = ∏_{p ∈ P'} Z_p`, `k = |P'|`.
- A class `r(m)` has degree `d(m) = (v_p(m))_{p ∈ P'} ∈ N^k`. Its closure in `Ẑ` is the
  ball product `∏_p (r + m Z_p)`, by the Chinese remainder theorem.
- By `ct-p-z-is-a-one-vertex-k-graph-full-group` item 3, every `g ∈ CT_P(Z)` is given by a
  partition into classes `r_i(m_i)` and canonical maps `r_i + m_i t ↦ s_i + n_i t`. It extends
  to a homeomorphism `ĝ` of `Ẑ`, with the same formulas for `t ∈ Ẑ`.
- **Coordinates.** On the ball of class `i`, `ĝ` acts in each coordinate `p` by
  `x_p ↦ s_i + (n_i/m_i)(x_p − r_i)`. This is one rational affine formula, the same in every
  coordinate.
- **Degree cocycle.** `c(g, x) = d(n_i) − d(m_i) ∈ Z^k` for `x` in class `i`. It is intrinsic:
  its entries are the valuations of the slope of the germ.
- **Potential.** `t_x(n) = Σ_{0 ≤ j < n} c(g, ĝ^j x)` for `n ≥ 0`, extended to `n < 0` by the
  cocycle identity. It is the degree of the slope of `g^n` at `x`.
- **Reading depth.** Fix `D ∈ N^k` such that every class of one defining partition of `g`
  has degree `≤ D` componentwise. Refining, `g` is canonical on every class of degree `≥ D`.

## Statement

1. **Reading lemma.** Let `y ∈ Ẑ`, `L ≥ 1` and `E ≥ D` with `E + t_y(j) ≥ D` for
   `0 ≤ j < L`. Then `g^L` maps the degree-`E` class containing `y` canonically onto the
   degree-`(E + t_y(L))` class containing `ĝ^L y`.
2. **Returns.** Suppose `g^L` maps a class `C = r(m)` canonically onto `C' = s(n)`, with
   `C̄ ∩ C̄' ≠ ∅`. Put `δ = d(n) − d(m)`, `H = {p : δ_p ≠ 0}` and `I = {p : δ_p = 0}`.
   - (a) If `H = ∅`, then `C = C'` and `ĝ^L` is the identity on `C̄`.
   - (b) If `H ≠ ∅`, put `q = (sm − rn)/(m − n) ∈ Q`. Then `q ∈ Z_p ∩ (r + mZ_p)` for
     `p ∈ H`, and `F = {x ∈ C̄ : x_p = q for all p ∈ H}` is nonempty and `ĝ^L`-invariant. On
     `F`, `ĝ^L` acts as a product of affine isometries of the balls `r + mZ_p`, `p ∈ I`.
3. **Periodic points are arithmetic.** Every periodic point of `ĝ` either
   - is a rational number `q` whose denominator is prime to `P'`, or
   - lies in the closure of a class on which some `g^L`, `L ≥ 1`, is the identity. That class
     contains integers, all in finite cycles of `g`.

   Hence, for a clopen `ĝ`-invariant `U`, `ĝ|_U` is aperiodic iff `g` has no finite cycle on
   `U ∩ Z_(P')`, where `Z_(P')` is the set of rationals with denominator prime to `P'`.
4. **Recurrent tails force isometric minimal sets.** Let `U ⊆ Ẑ` be clopen with `ĝ(U) = U`.
   For `x ∈ U` and `B ∈ N`, let `N_B(x)` be the set of `n ≥ 0` with
   `t_x(j) − t_x(n) ≥ −B·1` for all `j ≥ n`. If `N_B(x)` is infinite for some `x ∈ U` and
   some `B`, then `U` contains a nonempty closed `ĝ`-invariant set on which `{ĝ^n}` is
   equicontinuous. In particular `ĝ|_U` has an equicontinuous minimal subset. The same holds
   for `g^{-1}`, i.e. with `n ≤ 0` and `j ≤ n`.
   - **Record lows (added 09-19).** The same conclusion holds if, instead, infinitely many
     `n ≥ 0` are *`B`-record lows*: `t_x(j) ≥ t_x(n) − B·1` for all `0 ≤ j ≤ n`. The
     backward version also holds.
   - **Positive rays never pass.** If every slope of `g` lies in `γ^Z`, `γ ≥ 2` an integer,
     then every nonempty clopen `ĝ`-invariant `U` contains an equicontinuous minimal set.
5. **Consequence for subshift factors.** If `(U, ĝ)` factors onto a minimal system that is not
   equicontinuous (for instance an infinite minimal subshift), then `N_B(x)` and the set of
   `B`-record lows are finite for every `x ∈ U` and every `B`, for `g` and for `g^{-1}`. In
   particular:
   - no forward or backward orbit in `U` has bounded potential;
   - if every slope of `g` lies in `γ^Z` with `d(γ) = v` of mixed sign (a mixed ray, e.g.
     `γ = 3/2`), the condition says exactly that every forward and every backward potential in
     `U` is unbounded;
   - if `v ≥ 0` (a positive ray, `γ` an integer), it never holds, by item 4.
6. **Aperiodicity is cheap.** The north-south element `ψ ∈ CT_∅(Z)` of
   `ct-z-north-south-element-has-no-finite-cycles` acts on the profinite integers
   `Z_2 × Z_3` of `CT_{3}(Z)` with no periodic points. It is not equicontinuous there. Its
   minimal sets are the two fibers over `a = −2/3` and `r = −1/3`, both affine-isometric
   (odometer) systems on `Z_3`. Every finitely generated periodic subgroup of its topological
   full group is finite.

## Proof

**1.** Induction on `L`. For `L = 1`, `E ≥ D` and `g` is canonical on classes of degree
`≥ D`.
- **The composite is canonical.** Let `r(m)`, with `M | m`, lie in a defining class `ρ(M)`,
  mapped by `ρ + Mt ↦ σ + Nt`. Then `x = ρ + Mt ∈ r(m)` iff `t ∈ (r − ρ)/M + (m/M)Z`. So the
  image is a class of modulus `Nm/M`, reached by a canonical map, of degree
  `d(m) + d(N) − d(M) = E + c(g, y)`.
- **Induction step.** The hypothesis `E + t_y(j) ≥ D` says that the image class after `j`
  steps still has degree `≥ D`. So the next step is again canonical on it, and composites of
  canonical maps are canonical. ∎

**2.** In coordinate `p`, write `B_p = r + mZ_p` and `B'_p = s + nZ_p`, of radii `|m|_p` and
`|n|_p`, and `φ_p(x) = s + (n/m)(x − r)`, which maps `B_p` onto `B'_p`.
- **(a).** If `δ = 0`, then `m = n`, since both are positive and `P'`-smooth.
  Classes of equal modulus with intersecting closures are equal, so `r = s` and
  `t ↦ t` is the identity.
- **`δ_p > 0`.** Here `|n/m|_p < 1`. `B'_p` is a smaller ball meeting `B_p`, so
  `B'_p ⊆ B_p`, and `φ_p` is a contraction of `B_p` into itself. Its unique fixed point
  solves `x = s + (n/m)(x − r)`, i.e. `x = q`. So `q ∈ B_p`.
- **`δ_p < 0`.** Here `B_p ⊆ B'_p`, and `φ_p^{-1}` contracts `B'_p` into `B_p ⊆ B'_p`. Its
  fixed point is again `q`, and `q ∈ B_p`.
- **`δ_p = 0`.** The balls have equal radius and meet, so `B_p = B'_p`, and `φ_p` is an affine
  isometry of `B_p` onto itself.
- **Conclusion.** `F = ∏_{p ∈ H} {q} × ∏_{p ∈ I} B_p ⊆ C̄`, and `ĝ^L = ∏ φ_p` preserves it
  and acts on it as stated. ∎

**3.** Let `ĝ^L x = x` with `L ≥ 1`.
- **A return.** Take `E ≥ D + max(0, −min_{j<L} t_x(j))·1`. By 1, `g^L` maps the degree-`E`
  class `C ∋ x` canonically onto a class `C' ∋ x`. When `x` lies in a clopen invariant `U`,
  also take `E` so large that `C̄ ⊆ U`; this is possible since `U` is a finite union of class
  closures.
- **Case (a) of 2.** `g^L = id` on `C̄`. Every class contains integers, and they all lie in
  cycles of length dividing `L`. With `C̄ ⊆ U`, these integers lie in `U`.
- **Case (b) of 2.** For `p ∈ H`, `x_p` is the unique fixed point `q`. For `p ∈ I`, `x_p` is
  fixed by `φ_p(y) = s + (n/m)(y − r)`. Since `n ≠ m`, `n/m ≠ 1` in `Q_p`, and the only fixed
  point of `φ_p` in `Q_p` is again `q`. So `x = q` diagonally, and `q ∈ Ẑ` forces its
  denominator to be prime to `P'`.
- **The criterion.** Integers and elements of `Z_(P')` lie in `Ẑ`, and a finite cycle of `g`
  on them is a periodic orbit of `ĝ`. Conversely every periodic point is of one of the two
  kinds above. ∎

**4.**
- **Setup.** Enlarge `D` so that every class of degree `D` lies in `U` or in its complement,
  and put `E_0 = D + B·1`. There are finitely many classes of degree `E_0`.
- **Pigeonhole.** Choose `n_1 < n_2` in `N_B(x)` with `ĝ^{n_1}x` and `ĝ^{n_2}x` in the same
  degree-`E_0` class `C_0`. Put `y = ĝ^{n_1}x` and `L = n_2 − n_1`.
- **A return.** `t_y(j) = t_x(n_1 + j) − t_x(n_1) ≥ −B·1`, so `E_0 + t_y(j) ≥ D` for all
  `j`. By 1, `g^L` maps `C_0` canonically onto a class `C' ∋ ĝ^L y`. Since also
  `ĝ^L y ∈ C_0`, we get `C̄_0 ∩ C̄' ≠ ∅`.
- **Case (a) of 2.** `ĝ^L = id` on `C̄_0`, so `⋃_{i<L} ĝ^i C̄_0 ⊆ U` is closed, invariant,
  and every point on it is periodic. The family `{ĝ^n}` restricted to it is
  `{ĝ^i : 0 ≤ i < L}`, a finite family, hence equicontinuous.
- **Case (b) of 2.** `F ⊆ C̄_0 ⊆ U`, and `ĝ^L|_F` is an isometry for the max of the `p`-adic
  metrics. Put `F̃ = ⋃_{0 ≤ i < L} ĝ^i F`, which is closed and invariant.
  - For `n = qL + i` with `0 ≤ i < L`, `ĝ^n|_F = ĝ^i ∘ (ĝ^L|_F)^q`.
  - The same holds on each `ĝ^i F`, and for negative `n`.
  - So `{ĝ^n|_{F̃}}` is equicontinuous: finitely many uniformly continuous maps composed with
    isometries.
- **Minimal subsets.** A minimal subset of an equicontinuous system is equicontinuous.
- **For `g^{-1}`.** Apply the argument to `g^{-1} ∈ CT_P(Z)`, whose potential at `x` is
  `n ↦ t_x(−n)`.
- **Record lows.** Take `D` to serve for both `g` and `g^{-1}`.
  - Choose `B`-record lows `n_1 < n_2` with `ĝ^{n_1}x`, `ĝ^{n_2}x` in one degree-`E_0` class
    `C_0`, and put `y' = ĝ^{n_2}x`.
  - The potential of `g^{-1}` from `y'` is `j ↦ t_x(n_2 − j) − t_x(n_2) ≥ −B·1` for
    `0 ≤ j ≤ n_2`.
  - So by 1, applied to `g^{-1}`, `g^{-(n_2 − n_1)}` maps `C_0` canonically onto a class
    containing `ĝ^{n_1}x ∈ C_0`. This is a return for `g^{-1}`, and the rest is as above.
- **Positive rays.** Here `t = τ v` with `v ≥ 0`. Take any `x ∈ U`.
  - If `liminf_{n→∞} τ_x(n) = −∞`, the times of new minima of `τ` are infinitely many `0`-record
    lows.
  - Otherwise `N_B(x)` is infinite for some `B`, by the argument in 5.
  - Either way, 4 applies. ∎

**5.**
- **The factor argument.** Let `π : U → X` be a factor map onto a minimal `X`, and let
  `M ⊆ U` be the equicontinuous minimal set from 4. Then `π(M)` is closed, invariant and
  nonempty, so `π(M) = X`.
  - A factor of an equicontinuous compact system is equicontinuous, since `π` is uniformly
    continuous.
  - An infinite subshift is expansive, hence not equicontinuous.
- **Bounded potential.** If the forward potential of `x` is bounded by `B/2` in every
  coordinate, then every `n ≥ 0` lies in `N_B(x)`.
- **Mixed ray.** Here `t = τ v` with `v_p > 0 > v_{p'}` for some `p, p'`. So `n ∈ N_B(x)`
  forces `τ` to stay within `B` of `τ(n)` on `[n, ∞)`, from both sides, and conversely.
  - If some forward potential is bounded, every `n` lies in `N_B(x)` for large `B`.
  - If every forward potential is unbounded, no `n` does.
  - Likewise a `B`-record low `n` forces `|τ(j) − τ(n)| ≤ B'` for `0 ≤ j ≤ n`, so `|τ| ≤ 2B'`
    on `[0, n]`. Infinitely many of them force `τ` to be bounded on `[0, ∞)`.
- **Positive ray.** Here `n ∈ N_B(x)` iff `τ(j) ≥ τ(n) − B'` for `j ≥ n`, with `B'`
  depending only on `B` and `v`.
  - If `liminf τ = −∞`, this never holds.
  - If `liminf τ = ℓ` is finite, then infinitely many `n` have `τ(n) ≤ ℓ + 1`, and for large
    `n` every `j ≥ n` has `τ(j) ≥ ℓ − 1`. So infinitely many `n` lie in `N_2`.
  - If `τ → +∞`, the last visits to each level lie in `N_0`. ∎

**6.**
- **North-south dynamics on `Z_2`.** `ψ(n) = 4n + 2` for `n ≢ 1 (4)`, `n − 3` on `9(16)`,
  and `(n − 1)/4` on `1(16)`, `5(16)` and `13(16)`.
  - On `2 + 4Z_2`, `ψ(x) − a = 4(x − a)`, and this ball is invariant.
  - On `5 + 16Z_2`, `ψ(x) − r = (x − r)/4`. So `x ≠ r` leaves `5 + 16Z_2` after finitely
    many steps.
  - `0(4)` and `3(4)` go into `2(4)` in one step, `1(16)` via `0(4)` in two, `13(16)` via
    `3(4)` in two, and `9(16)` lands in `6(16) ⊆ 2(4)`.
  - So every `x ≠ r` has `ψ^n x → a`. A periodic point other than `r` is therefore `a`.
    Both `a` and `r` are fixed.
  - **Backward convergence.** `ψ^{-1}(y) = 4y + 1` off `2 + 4Z_2`, `y + 3` on `6 + 16Z_2`,
    and `(y − 2)/4` on `2`, `10` and `14 + 16Z_2`.
    - On `1 + 4Z_2`, which is invariant, `ψ^{-1}(y) − r = 4(y − r)`.
    - On `10 + 16Z_2`, `ψ^{-1}(y) − a = (y − a)/4`, so `y ≠ a` leaves it.
    - `2(16)` and `14(16)` reach `1(4)` via `0(4)` and `3(4)`, and `6(16)` lands in
      `9(16) ⊆ 1(4)`.
    - So every `y ≠ a` has `ψ^{-n} y → r`.
  - This re-checks the dynamical part of item 2 of `ct-z-north-south-element-has-no-finite-cycles`,
    which was not reviewed there.
- **No periodic points on `Z_2 × Z_3`.** The pieces have 2-power moduli, so the projection to
  `Z_2` is equivariant, and a periodic point lies over `a` or `r`. By 3 it would equal `−2/3`
  or `−1/3`, whose denominators are divisible by 3. Neither lies in `Z_3`.
  - Directly: over `a` the map is `x_3 ↦ 4x_3 + 2`, and over `r` it is
    `x_3 ↦ (x_3 − 1)/4`. Their fixed points `−2/3` and `−1/3` are not in `Z_3`.
- **Not equicontinuous.** Near `r`, distances in `Z_2` grow by the factor 4.
- **The fiber maps are minimal.** Let `φ(x) = ux + c` on `Z_3`, with `u ≡ 1 (3)` and `c` a unit.
  - Put `S(n) = Σ_{i<n} u^i`. Lifting the exponent gives `|S(n)|_3 = |n|_3`.
  - Then `S(n) − S(m) = u^m S(n − m)`, so `S` extends to an isometry of `Z_3` onto `Z_3`.
  - So the orbit `φ^n(0) = c S(n)` is dense, and `φ` is minimal.
  - Both fiber maps qualify: `4 = 1 + 3` with `c = 2`, and `1/4 ≡ 1 (3)` with `c = −1/4`.
  - Every orbit accumulates only on the two fibers, so these are the only minimal sets.
- **Periodic subgroups of the full group are finite.** Let `P` be a finitely generated
  periodic subgroup of `[[ψ̂]]`.
  - **Restriction to the fibers.** Each `f ∈ [[ψ̂]]` preserves the fibers `F_a` and `F_r`.
    Restricted to `F_a`, the elements permute the classes mod `3^N` for some `N` and act on
    each class by powers of `φ`. So `[[F_a, φ]]` is locally virtually abelian, and the image
    of `P` there is finite. The same holds on `F_r`.
  - **A kernel supported away from the fibers.** The kernel `P_0` has finite index and is
    finitely generated. `ψ̂` is aperiodic, so cocycles are unique, and `f ∈ P_0` has cocycle
    `0` on `F_a ∪ F_r`. Hence `f` is the identity on a clopen neighbourhood of `F_a ∪ F_r`.
  - **Bounded orbits.** The union `K` of the supports of generators of `P_0` is compact,
    avoids the fibers, and is `P_0`-invariant.
    - By uniform north-south convergence there is `N_0` such that every `ψ̂`-orbit meets `K`
      in at most `2N_0 + 1` points.
    - `P_0` preserves each `ψ̂`-orbit, so all `P_0`-orbits on `K` are that small.
  - **Finiteness.** A finitely generated group has finitely many subgroups of index
    `≤ 2N_0 + 1`. Their intersection fixes `K` pointwise, hence is trivial. So `P_0` and `P`
    are finite. ∎

## Why it matters

**What forbids a single element from carrying a periodic group.**
- **Periodic points are not the obstruction.** They are rational (item 3), and one more
  prime can remove them all, as `ψ` on `Z_2 × Z_3` shows.
- **Recurrence is the obstruction.** A potential that comes back within a bounded window,
  from below, at infinitely many times, gives a return. The return gives a closed invariant
  set on which the element is an affine isometry, i.e. an odometer.
- **Consequence for Hypothesis F.** Odometers have only equicontinuous factors, and their
  full groups are locally virtually abelian. So an element of `CT_P(Z)` satisfying
  Hypothesis F of `ct-z-periodic-groups-via-subshift-factors-of-elements` must make every
  orbit in `U` dip below every level it reaches, by every amount, in both time directions.

**The signature to aim for.** Every orbit's slope potential must have excursions at all
scales, as partial sums of a Toeplitz or paperfolding sign sequence do. So the slope cocycle
must itself be hierarchical. The natural candidates are *renormalizable* elements: elements
`g` such that a class conjugate `κ g^2 κ^{-1}` (`κ(x) = j + mx`, as in
`ct-z-north-south-element-has-no-finite-cycles` item 3) reproduces `g` on a subclass.

## Lesson for general BH

**Burnside-type hosts need hierarchy in the slope cocycle, not just freedom from periodic
points.**
- **What arithmetic can buy.** A second prime turns fixed points into isometric fibers.
  Periodic points are arithmetic and cheap to remove.
- **What it cannot buy.** Recurrence of the cocycle at a bounded scale always closes up into
  an odometer, and every finitely generated periodic subgroup of an odometer full group is finite.
- **The general principle.** In any Thompson-like host whose germs are affine (`nV`,
  `CT_P(Z)`, Röver–Nekrashevych-type hosts), the only way to realize Grigorchuk or
  Nekrashevych periodic groups is a cocycle that is recurrent at no bounded scale, i.e. a
  renormalization.
