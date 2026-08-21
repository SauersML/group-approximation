---
rg: 2
id: far-sector-is-solenoid-measure-rigidity
kind: claim
title: The far sector is an approximate measure-rigidity statement for the times-four automorphism of the two-adic solenoid, which needs the ambient non-amenability
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  parabolic-spectrum-is-doubling-invariant: that is the single-element spectral constraint; this identifies the exact dynamical system (the 2-solenoid automorphism) and records why single-system measure rigidity is FALSE, so the ambient group is essential.
  approximate-doubling-invariant-joint-measure-is-atomic: that is the target rigidity statement; this explains the dynamical obstruction to proving it from the abelian data alone.
---

The dyadic parabolics `[[1, a/2^k],[0,1]]` (`a in Z`, `k >= 0`) form a
subgroup `P ~= Z[1/2]` of `SL_2(Z[1/2])`, on which `h = diag(2, 1/2)` acts
by multiplication by `4`, an automorphism of `Z[1/2]`.  A unitary
representation restricted to `<P, h> = Z[1/2] rtimes_4 Z` (a metabelian,
amenable group) is, by SNAG, a projection-valued measure on the Pontryagin
dual `hat(Z[1/2]) = ` the **2-adic solenoid** `Sigma_2`, and `h` acts by the
dual automorphism `alpha` of `Sigma_2` (the natural extension of `z -> z^4`
on the circle).  The spectral measure of the parabolic `U` is the pushforward
of this solenoid measure to the circle factor.

**Consequence.**  In an exact representation the solenoid spectral measure is
`alpha`-invariant, and the arithmetic (finite-order) representations
correspond to measures supported on the `alpha`-periodic points = torsion of
`Sigma_2` = odd roots of unity.  In an approximate representation the measure
is approximately `alpha`-invariant.  So the far sector asks: is an
approximately-`alpha`-invariant solenoid spectral measure of a
finite-dimensional near-representation close to a convex combination of
periodic (atomic) measures?

**Why the abelian data is not enough.**  `alpha` is a single hyperbolic
solenoid automorphism.  Its invariant measures are NOT only Haar and the
periodic ones: like `z -> z^4` on the circle it carries a
family of Gibbs/Cantor invariant measures; HOWEVER (correction 2026-08-21)
those Gibbs measures are themselves weak-* limits of periodic-orbit
(atomic) measures -- Sigmund's specification theorem for the full shift --
which is exactly WHY BS(1,4) is HS-stable (dense periodic measures,
Levit--Vigdorovich).  So the single-parabolic measure IS approximable by
atomic ones; the earlier claim that Gibbs measures refute single-map
rigidity was wrong.  What the single map does NOT give is Furstenberg-style rigidity (which would
force Haar-or-atomic) requires TWO multiplicatively independent maps
(`x2` and `x3`), whereas `SL_2(Z[1/2])` inverts only `2` and supplies only
the `x4` (equivalently `x2` via half-parabolics) direction.  Hence the far
sector CANNOT be closed inside the amenable subgroup `<P, h>`: the diffuse
non-Haar invariant measures must be excluded by the FULL non-amenable
`SL_2(Z[1/2])`, through the involution `S` coupling `U` to `L = S U S^(-1)`
and property (T;FD).  This is the precise reason Dogon--Vigdorovich's
question is a theorem about the S-arithmetic lattice and not about a
Baumslag--Solitar subgroup, and it locates the missing ingredient: a
rigidity for approximate `alpha`-invariant measures that uses the extra
non-commuting symmetry, an approximate-representation analogue of the
Bekka--Kalantar / character-rigidity input.

## Attempts

- **The abelian direction is UNCONDITIONALLY fine (Levit--Vigdorovich,
  arXiv:2206.02268).**  Correction to the pessimistic reading above: their
  theorem is that a system has *dense periodic measures* -- periodic-orbit
  (atomic) measures are weak-* dense among ALL invariant measures -- exactly
  when the associated metabelian group is HS-stable, and a SINGLE ergodic
  toral/solenoid automorphism always has dense periodic measures (via
  Marcus 1980).  Since `Z[1/2]` inverts only the prime `2`, the relevant
  dynamics is the single automorphism `x2` (equivalently `x4`) of the
  2-solenoid, which is ergodic, so it HAS dense periodic measures and
  `BS(1,2) = Z rtimes Z[1/2]` is HS-stable.  The Gibbs measures do exist but
  are approximable by periodic (atomic) ones -- that is the content of dense
  periodic measures -- so they are NOT an obstruction.  The Furstenberg
  `x2 x3` / higher-rank measure-rigidity difficulty (their Question 4,
  `Z^2 rtimes Z[1/6]`) arises only when two independent primes are inverted,
  which does NOT happen for `Z[1/2]`.  Conclusion: the abelian/solenoid part
  of the far sector is unconditionally rigid, and the entire remaining
  obstruction is the non-amenable coupling through the involution and
  (T;FD).
- **The trace side is also done.**  By Peterson--Thom character rigidity,
  every character of `SL_2(Z[1/2])` is a limit of finite-dimensional traces
  (congruence traces `1_(Gamma(n)) -> delta_e`), i.e. the Hadwin--Shulman
  criterion holds; this is hyperfinite HS-stability.  For the AMENABLE
  `BS(1,2)` this criterion equals stability, but for the non-amenable
  `SL_2(Z[1/2])` it is weaker, and the gap is exactly the non-hyperfinite
  asymptotic representations -- the same object as `(RCC)`.
- **Single-map rigidity is not the issue after all; the coupling is.**  Any
  far-sector proof must use the involution or (T;FD) to control the
  non-amenable direction, not the abelian dynamics, which is settled.  Known
  non-amenable HS-stability results to mine for the technique: Atkinson,
  Hadwin--Shulman, Ioana--Spaas--Wiersma (ISW20), Gao--Shen (GS21),
  Ioana (Ioa21).
- **Two-map upgrade.**  `L = S U S^(-1)` has its own `alpha`-invariant
  measure equal (via `S`) to that of `U`, but `S` does not give a second
  COMMUTING multiplication on the same solenoid; it is an outer symmetry.
  The right framework is likely stationary measure rigidity for the
  `SL_2`-action, i.e. a quantitative Benoist--Quint / Bourgain--Furman--
  Lindenstrauss--Mozes statement for approximate representations, which is
  not available off the shelf.
- **(T;FD) route.**  Property (T;FD) forces exact characters to be limits
  of finite-dimensional traces; the far sector is exactly the failure of
  this to be quantitative/stable, so this is a restatement, not a tool,
  unless combined with the solenoid structure above.
