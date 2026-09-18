---
rg: 2
id: hyperlinear-fg-bounded-exponent-groups-are-finite
kind: claim
title: Every finitely generated hyperlinear group of finite exponent is finite
distinct_from:
  infinite-fg-bounded-exponent-groups-are-non-mf: that is the operator-norm MF form of the same finiteness principle, reduced to the corona restricted Burnside statement; this is the normalized Hilbert--Schmidt form, and neither implies the other on its face.
  hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness: that is the established equivalence with a statement about limit traces of approximate exponent-N models; this is the finiteness statement itself.
---

**OPEN.** Let `G` be a finitely generated group of finite exponent. If `G` is
hyperlinear, then `G` is finite.

This is a Hilbert--Schmidt "Burnside problem". A proof would give a
non-hyperlinear group. The large odd exponent free Burnside groups are
infinite (`free-burnside-large-odd-exponent-is-nonamenable`), so they would be
non-hyperlinear, a negative answer to Weiss's Open question 9.4 in Pestov's
guide. Route: `non-hyperlinear-group-via-hyperlinear-burnside-finiteness`.
Through the Delzant--Gromov stages of `B(m,N)` it would also give a
non-hyperlinear, hence nonsofic, hyperbolic group
(`nonsofic-hyperbolic-group-via-hyperlinear-burnside-finiteness`).

By `hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness`, this
statement for `m`-generated groups of exponent dividing `N` is equivalent to
the following. Every limit trace of approximate exponent-N unitary models
factors through a finite quotient of `F_m`.

## Attempts

1. **Hilbert--Schmidt stability of exponent laws** (approach A5 of
   `research/artifacts/ideas-2026-09-13/nh/nh-small-cancellation.md`,
   2026-09-13).
   - Its trace-level conclusion is statement 2 of the equivalence node, so
     the route is this claim, not something weaker.
   - Rounding a single generator is free: move its eigenvalues to `N`-th roots
     of unity. Rounding does not pass to products, though, and at the trace
     level there is nothing left for stability to add.
2. **Kill test: an infinite f.g. hyperlinear group of finite exponent.** None
   found. The search below is not exhaustive.
   - Pestov, arXiv:0804.3968v8, §9, Open question 9.4 (text checked): "Is
     the free Burnside group of a finite exponent n sofic?" It is recorded
     there as open. A web search found no later answer.
   - Residually finite candidates die. A f.g. residually finite group of
     finite exponent embeds in a product of finite quotients of `R(m,N)`,
     hence is a quotient of `R(m,N)` and finite (`restricted-burnside-finiteness`).
   - Bounded-dimension approximations force finiteness, not just LEF:
     `bounded-dimension-microstates-bounded-exponent-group-is-finite` passes to
     a faithful representation in `U(d)` and applies Schur's theorem. So a
     counterexample needs microstate dimensions tending to infinity. (The
     earlier inference from `bounded-dimension-microstates-force-lef` alone was
     incomplete, since LEF does not force finiteness.) An infinite
     bounded-exponent LEF group would still be a counterexample, through
     unbounded dimensions. The MF analogue of that firewall is
     `bounded-exponent-lef-group-defeats-burnside-mf-program`.
   - Amenable groups are hyperlinear, so this claim forbids infinite f.g.
     amenable groups of finite exponent. A search summary called that
     existence question open; the source was not pinned against text.
3. **Calibration through stability.** By
   `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, a flexibly
   HS-stable hyperlinear f.g. group of finite exponent is residually finite,
   hence finite. So flexible HS-stability of the bounded-exponent groups would
   prove this claim. Conversely, one infinite hyperlinear bounded-exponent
   group refutes every such stability principle for that group.
4. **Counterexample hunt and small exponents** (lane solve-nh-bounded-exponent,
   2026-09-13). Not solved; no counterexample.
   - **Verbal products give nothing.** Brude--Sasyk (arXiv:1909.07800v5,
     Theorem 1.5 and Corollary 1.6, read from the PDF, p. 3) preserve soficity
     and hyperlinearity under k-Burnside products only for `k = 2, 3, 4, 6`.
     Those are exactly the exponents where free Burnside groups are finite, so
     their constructions stay finite on finitely generated finite-exponent
     inputs. For larger `k` the `k`-Burnside product of two cyclic groups of
     order `k` is `B(2,k)` itself, since the verbal subgroup lies in `[A,B]`
     (their Corollary 2.9); soficity there is Pestov's Question 9.4 again.
   - **Small exponents are trivial.** For `N` dividing `2`, `3`, `4` or `6`,
     every f.g. group of exponent dividing `N` is finite (Burnside, Sanov,
     M. Hall; statement pinned from the "Burnside problem" survey page), so
     the claim holds there vacuously. It is open exactly where `B(m,N)` is not
     known to be finite, including `N = 5`; `B(m,N)` is infinite for odd
     `N > 665` (Adian) and large even `N` (Ivanov, Lysenok).
   - **Stability adds no leverage.** For infinite `B(m,N)`, flexible
     HS-stability plus hyperlinearity would already force residual finiteness,
     hence finiteness, so stability for these groups is at least as strong as
     their non-hyperlinearity. No mechanism for it was found. Rounding
     almost-order-`N` unitaries one at a time does not control products.
   - **Literature scan.** arXiv full-text searches for bounded exponent with
     amenable, Burnside with sofic, and finite exponent with LEF (2026-09-13)
     returned no construction of an infinite f.g. amenable, sofic, LEF or
     hyperlinear group of bounded exponent, and no finiteness theorem. The
     session's web search budget was exhausted, so MathOverflow, zbMATH and
     MathSciNet were not checked. Not exhaustive.
5. **Numerics, exact-law models, and the collapse gap** (lane
   solve-burnside-sofic, 2026-09-13). Not solved; no counterexample.
   - **An obstruction window is at least as long as the gap between `B(m,N)`
     and `R(m,N)`.**
     - Let `l_0` be the word length of a shortest nontrivial element of
       `ker(B(m,N) -> R(m,N))`. It is finite exactly when `B(m,N)` is
       infinite.
     - If `2R < l_0`, words of length `<= R` satisfy the same equalities in
       `R(m,N)` as in `B(m,N)`.
     - `R(m,N)` is finite (`restricted-burnside-finiteness`), so it is sofic
       and hyperlinear.
     - So for a nonsofic or non-hyperlinear `B(m,N)`, the radius `R` given by
       clause 3 of `local-approximation-properties-are-marked-closed`
       satisfies `2R >= l_0`.
     - Numerics on approximate permutation or unitary models with windows
       shorter than `l_0/2` are passed with zero defect by the regular
       representation of `R(m,N)`. They cannot suggest either verdict.
     - This lane has no estimate of `l_0`, so no MSI runs were made.
   - **Exact-law models see only `R(m,N)`.**
     - Suppose permutations `σ_1, ..., σ_m` generate a group of exponent
       dividing `N`. That finite `m`-generated group is a quotient of
       `R(m,N)`, so every element of `ker(B(m,N) -> R(m,N))` acts as the
       identity.
     - So models built from finite groups of exponent `N`, including their
       products, never separate that kernel.
     - A sofic approximation of an infinite `B(m,N)` must therefore break the
       law `w^N = 1` somewhere in all but finitely many of its models. This is
       the model-level form of the residually finite kill in Attempt 2.
   - **Iterated small cancellation stages carry a negative answer into
     hyperbolic groups.**
     - For odd `N >= n_1(F_m)`, `B(m,N)` is the direct limit of the
       non-elementary hyperbolic stages `G_k` of
       `free-burnside-is-a-limit-of-hyperbolic-groups`.
     - By `nonsofic-free-burnside-gives-nonsofic-hyperbolic-group`, a nonsofic
       or non-hyperlinear `B(m,N)` makes `G_k` nonsofic or non-hyperlinear for
       all large `k`.
     - So this claim now also routes into `nonsofic-hyperbolic-group`, through
       `nonsofic-hyperbolic-group-via-hyperlinear-burnside-finiteness`.
     - Conversely, soficity of every hyperbolic group would make these
       `B(m,N)` sofic.
     - Only Coulon's account of the Delzant--Gromov construction was pinned.
       Ol'shanskii's graded diagrams were not read.
   - **The collapse gap, exactly.**
     - For odd `N >= n_1(F_m)`, a non-hyperlinearity proof for `B(m,N)` is
       equivalent to finding a radius `R >= l_0/2` and an `ε > 0` such that
       no unitary matrices, in any dimension, match the equalities and
       inequalities of the `R`-ball of `B(m,N)` within `ε`.
     - On that ball the stages `G_k` with `k >= k(R)` look exactly like
       `B(m,N)`, although they have elements of infinite order.
     - So whatever the method (the global exponent law, Zelmanov's theorem,
       Schur's theorem), its conclusion reaches a hyperbolic group through
       finitely many relations `w^N = 1`.
     - No mechanism working at radius `l_0/2` was found.
   - **Calibration: a local restricted Burnside principle.**
     - Let `LRB(m,N)` be the statement: there are `R_0` and `C` such that
       every finite `m`-generated group with `h^N = 1` for all `h` of word
       length `<= R_0` has order `<= C`.
     - For odd `N >= n_1(F_m)`, `LRB(m,N)` makes some stage `G_k` not
       residually finite. Proof:
       - Pick `R` so that the `R`-ball of `B(m,N)` has more than `C` elements.
       - Pick `k` with `S_L ∩ N_k = S_L ∩ F_m^N` for `L = max(2R, N·R_0)`,
         as in step 2 of `nonsofic-free-burnside-gives-nonsofic-hyperbolic-group-proof`.
       - Then `h^N = 1` in `G_k` whenever `|h| <= R_0`.
       - A finite quotient of `G_k` injective on the `R`-ball would contradict
         `LRB(m,N)`.
     - So `LRB(m,N)` implies `non-residually-finite-hyperbolic-group`.
     - A Hilbert--Schmidt analogue with approximate laws is the natural
       collapse input. Its exact form was not settled, and neither form was
       proved or refuted.
6. **Local restricted Burnside, partly settled** (lane
   solve-local-restricted-burnside, 2026-09-13). Not solved.
   - `LRB(m,N)` of Attempt 5 is now the established node
     `local-restricted-burnside-iff-partial-burnside-finite-quotients`.
     - It holds iff some partial Burnside group
       `Π_R(m,N) = F_m/⟨⟨h^N : |h| <= R⟩⟩` has only exponent-`N` finite quotients.
     - For odd `N >= n_1(F_m)` it makes every large stage `G_k` not residually
       finite.
     - Residual finiteness of infinitely many stages refutes it.
   - **Small radii fail.** `partial-burnside-presentations-are-golod-shafarevich`
     gives unbounded finite `p`-groups satisfying the law on words of length
     `<= R` whenever a prime power `q | N` has `q >= 4R + 5`.
   - **Nilpotent groups satisfy it.**
     `finite-nilpotent-groups-satisfy-local-restricted-burnside`. So large stages
     `G_k` have finite pro-p completions, and a refutation at large radii needs
     non-nilpotent finite groups.
   - **Open instance.** `large-odd-exponent-local-restricted-burnside`, routed into
     `non-residually-finite-hyperbolic-group`.
7. **Entropy-measure transplant: free entropy dimension, killed** (swarm-0917,
   heretic lane, 2026-09-17). DEAD as a route to this claim, and to every
   non-hyperlinearity hole.
   - **The idea.** An exact-order-`N` element has an atomic spectral measure,
     with mass `1/N` on each root of unity. Exponent laws should therefore
     make microstate spaces small. The plan was to force `δ_0 < 1` against
     Jung's floor `δ_0 >= 1` for diffuse embeddable algebras.
   - **Where it dies.** `free-entropy-dimension-cannot-certify-non-hyperlinearity`.
     (That node is OPEN: a referee refuted its universal Consequence on 2026-09-17. What
     survived review is only that the Theorem-3 floor and the `δ*` ceiling never cross.)
     - For every infinite f.g. group, the published floor is the dimension
       of the algebraic cocycles (Shlyakhtenko, arXiv:0710.4111, Theorem 3).
     - The published ceiling is `δ_0 <= δ* = β_1^(2) + 1` (Mineyev--Shlyakhtenko).
     - The floor never exceeds the ceiling, because
       `Z^1(Γ; CΓ) ⊂ Z^1(Γ; UΓ)` and Lück dimension is monotone. No
       hyperlinearity is used.
     - The exponent law contributes only `c(g) ∈ (1 - E_g) UΓ` for each
       generator. That bounds the ceiling by `m(1 - 1/N)`, which is still
       `>= 1`.
     - So a `δ_0` proof needs a floor larger than `δ*`. That floor is false
       on every hyperlinear group, and proving it already proves the
       microstate spaces empty.
   - **1-bounded entropy (not re-read at source).** Hayes's `h` is `>= 0` on
     every embeddable algebra, because a nonempty orbit covering has log count
     `>= 0`. The strong 1-boundedness criteria (Cartan, property (T), sofic
     with `β_1^(2) = 0`) give only `h <= 0`, so the same range argument
     applies.
   - **Heretic audit: three unstated shared assumptions** of the HOT families
     (linear-characteristic, host-geometry, logic-computability,
     cohomology-index, stability-approximation), each denied in turn.
     - **(A1) The obstruction is certified at a finite radius.** Denial: use a
       genuinely global law such as the full exponent law. It breaks at
       Attempt 5: each finite ball of `B(m,N)` is a ball of a hyperbolic stage
       `G_k`, so any certificate reaches `G_k`.
     - **(A2) The obstruction is computed from the algebra of `Γ`, not from
       the volume of the model space.** Denial: this is the entropy-measure
       family. It breaks at the cocycle inclusion above, because the volume
       invariant is itself sandwiched between two algebraic cocycle
       dimensions.
     - **(A3) The trace to be approximated is the regular trace.** Denial:
       aim at a non-regular character. It breaks at
       `hyperlinear-radical-is-finitely-witnessed`: if every element survives
       some approximable character, tensor powers recover the regular trace.
     - No denial gave a new route.
8. **Inverter: partial Burnside census at exponent 5** (swarm-0917 w4,
   2026-09-17). Not solved. If `LRB(2,5)` fails, an infinite LEF, hence
   hyperlinear, group of exponent 5 exists and refutes this claim at `N = 5`. So
   the minimal counterexample's biography starts from finite quotients of
   `Π_R(2,5)` that are not 5-groups, at every radius. Data in
   `experiments/partial-burnside-census-2026-09-17/results.txt`.
   - **Radius 2 is rich.** A low-index census finds `A_6`, `A_10`, `A_11`, `A_12`
     and groups of orders 55, 80, 360, 660, 11520 among images of `Π_2(2,5)` in
     degree `<= 12`.
   - **Radius 3 looks empty but is not.** In degree `<= 20`, `Π_3(2,5)` has only
     5-group images. Yet `partial-burnside-radius-four-virtually-abelian-quotient`
     (ESTABLISHED, exact certificate over `Z[ζ_5]`) gives an infinite virtually
     abelian quotient `Q ⊂ Z[ζ_5]^5 ⋊ H5` of `Π_4(2,5)`, with finite quotients
     containing elements of every prime order `q != 5`. So `R*(2,5) >= 5`, and
     low-index censuses at a fixed radius are not evidence for `LRB`.
   - **Two-dimensional models die at once.** Irreducible `SL_2(C)` pairs fail at
     radius 1. Over `F_p` (`p <= 59`) irreducible pairs reach radius 2 only for
     `p = 3, 11`, never radius 3.
   - **Where the abelian-by-5-group obstruction dies.** The law is linear in the
     cocycle. For `H5` and all 2-generated subgroups of
     `{sum-zero diagonals} ⋊ C5` on 5-dimensional monomial modules, no
     non-coboundary solution survives radius 5 (`q = 11, 31, 41, 101`). By
     clause 3 of `lef-burnside-approximants-are-nonlinear-and-nonsolvable`, every
     solvable family dies at some radius. The step that fails is uniformity:
     nothing here bounds the death radius over all modules and all 5-group tops.
   - **Next.** Radius 5 with larger modules (degree 25 monomial over
     `C5^2`-tops, or modules of quotients of `R(2,5)` of class `>= 3`), then
     non-solvable tops.
9. **Inverter: low-degree trace mass must escape** (swarm-0917 w5, 2026-09-17).
   Not solved. This picks up the uniformity step where Attempt 8 stopped. Two
   ESTABLISHED class kills; neither uses a restricted Burnside theorem.
   - **Approximate side.** `approximate-burnside-models-low-degree-trace-mass-vanishes`.
     The microstates of an infinite exponent-`N` group put trace mass tending
     to 0 on irreducible pieces of dimension `<= c`, for every `c`. The same
     holds for models Hilbert--Schmidt close to block-diagonal with blocks of
     dimension `<= c`. Invariant: low-degree trace mass. Death step: the weak-*
     limit of the small pieces lies on `Hom(B(m,N), U(<= c))`, which kills a
     finite-index `K_c <= F_m` (Jordan and Schur, through clause 2 of
     `bounded-degree-partial-burnside-reps-factor-through-burnside`).
     Positive-definiteness on a sum of `s` distinct elements of `K_c` then caps
     the mass by `1/s`. This strictly contains the bounded-dimension case
     `bounded-dimension-microstates-bounded-exponent-group-is-finite`.
   - **Exact side.** `partial-burnside-finite-quotients-low-degree-plancherel-bound`.
     At the radius `R_c = max_(d <= c) R_0(m,N,d)`, a finite quotient `Q` of
     `Π_(R_c)(m,N)` has Plancherel mass `<= C(m,N,c)/|Q|` on irreducibles of
     dimension `<= c`. Every `m`-generated group with an abelian subgroup of index
     `<= c` that satisfies the law on the `R_c`-ball is finite of exponent `N`.
     So Attempt 8's missing uniformity over modules holds for tops of bounded
     order, including every analogue of the `Z[ζ_5]^5 ⋊ H5` quotient at radius
     `R_125(2,5)`.
   - **What is left.** A counterexample, or an LEF refutation of `LRB`, needs
     approximants whose trace or Plancherel mass escapes to irreducibles of
     unbounded dimension that are not HS-almost reducible into bounded blocks.
     For census work this means non-solvable tops or 5-group tops of unbounded
     order with high-dimensional irreducibles. Nothing here bounds `R_c` or
     `C(m,N,c)`.
10. **Calibration: split into a finite-group principle and exact trace
    rounding** (swarm-0917, d-nhg-p4; numbered 10 because Attempts 8 and 9 were
    posted on the live bus from other worktrees).
    - **Established decomposition**
      (`hs-burnside-iff-lrb-and-partial-law-trace-rounding`). For fixed `m, N`:

      ```text
      HB(m,N)  <=>  LRB(m,N) and S(m,N,R) for all R
               <=>  there are R, C with LRB(R, C) and S(m,N,R).
      ```

      `S(m,N,R)` says that every limit trace of an approximate exponent-N model
      is a limit of traces of genuine finite-dimensional unitary
      representations of the finitely presented partial Burnside group
      `Π_R(m,N)`.
    - **Necessity of `LRB`.** Regular representations of the LEF witnesses of
      `local-restricted-burnside-iff-lef-burnside-groups-are-finite` form an
      eventually exact model whose trace is the indicator of the kernel of an
      infinite group.
    - **Necessity of `S`.** A limit trace factoring through a finite group is a
      convex combination of normalized characters of irreducibles that kill
      every `N`-th power.
    - **Sufficiency.** Linear images of `Π_R(m,N)` are residually finite by
      Malcev. At an `LRB` radius their finite quotients are bounded, so the
      images are uniformly bounded and the trace factors through `R(m,N)`.
    - **Calibration kill.** At an `LRB` radius, with `B(m,N)` infinite, strict
      or flexible HS-stability of `Π_R(m,N)` makes `Π_R(m,N)` a finitely
      presented non-hyperlinear group. So operator-level rounding proofs of `S`
      at the needed radius are at least as strong as the root.
    - **New open nodes.** `approximate-exponent-traces-round-to-partial-burnside-reps`
      (true at radius `1` by spectral rounding; the needed radius exceeds
      `(q - 5)/4` by Golod--Shafarevich), and the route
      `non-hyperlinear-group-via-lrb-and-partial-law-rounding`.
    - **Status.** The target stays OPEN. What was gained: the finite-group
      content and the analytic content are now separate prerequisites, and a
      failure of `LRB` does not refute `S`.
