# One compression-rigidity theorem across metrics, part 2 (2026-09-12)

Lane `ex-free-unified-theory`. Part 1: `research/artifacts/unified-compression-rigidity-2026-09-12.md`.
This part records two consequences of the finitary theorem and one refinement of the
Hilbert--Schmidt median route.

## 1. At a simple configuration the criterion is exact

**Theorem 1 (`leavitt-unit-group-outside-class-iff-compression-stability`).** Let `R = L_(F_2)(1,2)`,
and let `Gamma = EL_alpha(R) <= G_L = EL_D(R) = R^x` be the nine-leaf pair with compressors `u, v`.
For `C` sofic, hyperlinear, `k`-linear sofic or weak MF:

```text
R^x not in C   <=>   NORM_C at the pair   <=>   UCS_C(F, {u, v}).
```

*Proof.* The second equivalence is Theorem 1 of part 1.
- *Normalization excludes membership.* A faithful `rho : R^x -> U` has
  `rho(j) in C(rho(Gamma))` for `j in J = V_(1000)`. Normalization puts `rho(u j u^-1)` there too.
  So `rho` kills `[u j u^-1, gamma]`, which is nontrivial
  (`leavitt-unit-group-carries-nontrivial-rigid-defect`).
- *A wall gives membership.* A homomorphism with a wall is nontrivial, and `R^x` is simple. So it is
  faithful, and property (U) puts `R^x` in `C`. ∎

**General form.** The same argument gives: if `H` is simple and contains a rigid pair with a
nontrivial defect, then for every class with (U), `H not in C` iff `NORM_C` holds at that pair.

**Readoff for one group.**

| metric | the inequality `UCS_C(F, {u,v})` | status |
| --- | --- | --- |
| Hamming | holds | established: Kun--Thom 4.1 via `sofic-groups-kill-rigid-compression-defects`; recovers the OpenAI theorem |
| Hilbert--Schmidt | iff `R^x` not hyperlinear | OPEN; its failure is `binary-leavitt-unit-group-hyperlinear`, a hyperlinear nonsofic group |
| rank over `F_2` | iff `R^x` not `F_2`-linear sofic | OPEN; the gate `binary-leavitt-unit-group-is-f2-linear-sofic` of the Gottschalk campaign |
| rank over `C` | iff `R^x` not `C`-linear sofic | OPEN |
| operator norm | iff `R^x` not weak MF | holds: every homomorphism from `R^x` to an MF group is trivial (`binary-leavitt-all-ranks-full-mf-radical`) |

So the four approximation questions about the first nonsofic group are one inequality, read in four
metrics. The Hamming and operator-norm readings are known. In the operator norm the same inequality
fails at the Kun--Thom Theorem E pair, through the MF amalgams `H_K`.

**Contrast with the Kun--Thom pair.** At the Theorem E pair the actor `G` is residually finite, so it
is in every class, and a wall produces a *different* group `<sigma(G), z>`. That is why the crux
`hs-uniform-compression-stability-at-the-theorem-e-pair` is a win--win between two different
landmarks, while at the Leavitt pair the inequality decides one group.

**Coincidence of handles.** `leavitt-pair-vertex-rounding-is-nonhyperlinearity` shows (H1) at the
Leavitt pair is also equivalent to nonhyperlinearity of `R^x`. So at this pair, vertex rounding,
normalization for every model, the uniform inequality and nonhyperlinearity are one statement. The
vertex `Gamma ~= R^x` has no nontrivial finite-dimensional unitary representation, so (H1) carries no
spectral content there: any proof of any of the four must be algebraic or global, not a rounding
argument.

## 2. The median route consumes a masa, not a gap

**Theorem 2 (`hs-vertex-rounding-and-liftable-masa-force-normalization`).** For a trace-preserving
`sigma` of an infranormal Kazhdan pair, (H1) together with a liftable masa of `sigma(G)' cap M`
forces normalization.

What is new relative to `hs-rounding-and-actor-gap-force-ccr` is one step. The block median
observable

```text
f = sum_A q_A F_(m_A)(zeta_A) q_A,     1/2 a median of q_A F_(m_A)(zeta_A) q_A on each block,
```

lies in `sigma(G)' cap M` by Section 4 of `research/artifacts/hs-s4-assembly-2026-09-12.md`, and it
commutes with every block. So it lies in the masa `C = prod_U C_n`: `f = sum_A c_A q_A` along `U`.
- A median bound gives `(c_A - 1/2)^2 <= 2 delta_A^2`, where `delta_A` is the block-normalized
  distance from `f` to `c_A`.
- Summing, `||f - 1/2||_2^2 <= 6 ||f - sum_A c_A q_A||_2^2 -> 0`.

That is the concentration which Section 5 there obtained from a per-block Poincare gap. The rest of
the assembly is unchanged.

**Where this puts the Hilbert--Schmidt row.** Both open inputs are halves of the Hilbert--Schmidt form
of Kun's decomposition:
- (R): `hs-stable-vertex-rounding-for-every-model`, internal coordinates for the vertex.
- (L): `actor-commutant-has-liftable-masa-in-every-model`, internal atoms for the actor. This is the
  Hilbert--Schmidt form of Kun--Thom Lemma 2.3 for `G`.

In the Hamming row one theorem, Kun's decomposition, supplies both halves at once.

## 3. Why (L) is not free from property (T) of `G` at the ultraproduct level

This records an attempt, to save a future lane the time.

- **The idea.** A cascade (Hilbert hotel) under (H1) shifts internal log aspect ratios
  `D = log zeta_A` upward on most of the mass. The increments `J(t) = Ad sigma_n(t)(D) - D` form a
  1-cocycle of the free group on `F cup T`. If they descended to an `L^2(M)`-valued cocycle of `G`,
  property (T) (vanishing of `H^1`) would make them a coboundary `theta_t(xi) - xi` with
  `xi in L^2`. Positivity and trace invariance would then force `J = 0`.
- **Where it dies.**
  - `D` has internal norm of order `log n`. Relators act on `M_n` by unitaries that are only
    2-norm close to `1`, so the relator increments `Ad w_n(D) - D` are of order `eps_n log n` and
    need not vanish.
  - The cocycle therefore does not descend to `G` unless `eps_n log n -> 0`. In that regime
    `ccr-under-vertex-rounding-from-few-aspect-scales` already gives (CCR) with no actor input.
  - If `J(t)` were uniformly bounded and nonnegative up to `o(1)` in `L^1`, the exact internal
    identity `tau_n(J_n(t)) = tau_n(D) - tau_n(D) = 0` would give `J -> 0` in `L^1` with no
    property (T) at all. So a cascade whose jumps are nonnegative on most of the mass must pay on
    the unbounded negative tail of the increments: mass carried to internal infinity. This is the
    rank-spiky compensation of Alekseev--Thom 6.2(a) in `notes/NOTEPAD.md`, seen as log-scale
    holonomy around relators.
- **Verdict.** Property (T) of `G` enters the Hilbert--Schmidt row only through finite-stage
  structure (atoms, rounding rates, quantitative stability), consistent with Section 4 of
  `research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md`.
