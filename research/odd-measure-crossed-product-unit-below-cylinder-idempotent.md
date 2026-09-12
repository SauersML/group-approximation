---
rg: 2
id: odd-measure-crossed-product-unit-below-cylinder-idempotent
kind: claim
title: In the signed Thompson crossed product over odd measures the unit is Murray-von Neumann below the cylinder idempotent
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the corner equation in the whole anti-central summand S_-; this asks for the equivalent subequivalence inside the explicit subalgebra F_3[H] eps_- of the signed Thompson group, a dynamical crossed product, which is sufficient but not necessary.
  ternary-twisted-algebra-has-swap-separated-one-sided-pair: that is an idempotent-free equivalent of the corner equation in all of S_-; this restricts to the signed Thompson crossed product and to the cylinder idempotent q_[0].
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

**OPEN.** Let `B = F_3[H] eps_- ~= C(M_-, F_3) ⋊_alg V`, the signed Thompson crossed product over
odd `F_2`-measures (`signed-thompson-algebra-is-odd-measure-crossed-product`). Let `q_[0]` be the
indicator of `{mu([0]) = 1}`. Exhibit `b', c' in B` with

    c' q_[0] b' = eps_- .

By `hadamard-unit-conjugates-swap-idempotent-to-cylinder`, a solution solves
`ternary-anti-invariant-swap-corner-is-full` and refutes Gottschalk on `L_(F_3)(1,2)^x`. The route is
`odd-measure-compression-gives-anti-invariant-corner`.

## Attempts

- **Honest compression, dead.** Lifting the Dirac Hilbert hotel by clopen pieces and `V`-translates
  is excluded by the invariant Haar measure (`odd-measure-space-has-no-honest-thompson-compression`).
  The route `ternary-lift-by-honest-odd-measure-compression` is invalidated.
- **Mod-3 trace, no obstruction.** `Tr(eps_-) = 1` and `Tr(q_[0]) = -1` leave room for an
  equivalent subidempotent of trace `1` (`odd-measure-crossed-product-carries-mod-three-trace`).
- **Intertwiner, dead.** No nonzero finitely supported `v` intertwines the corner endomorphism
  `iota(g) = s0 g t0 + s1 t1`, so a lift of `s0` cannot be an exact intertwiner. The general form,
  covering every injective non-surjective endomorphism, both sides, every prime and every field, is
  `self-similar-leavitt-intertwiners-have-no-exact-lift` (gk-l3-corner). Section 7(b) of the artifact
  gives the `iota` case directly.
- **Finite-dimensional support no-gos do not bind.** Every finite-dimensional representation of
  `H = E ⋊ V` is trivial (`signed-thompson-group-has-no-finite-dimensional-representations`). No
  obstruction needing a representation with `z -> -1` can exclude witnesses in `B`.
- **Nonamenable Thompson support (established).** The supports of any witness project onto a
  nonamenable subgroup of `V`.
  * *Why.* Otherwise the support subgroup is locally-finite-by-amenable, hence sofic, and its group
    algebra over `F_3` is directly finite
    (`odd-measure-corner-witnesses-need-nonamenable-thompson-support`).
  * *Scope.* The reflection group `E` is invisible to this. A witness projecting into `F` would prove
    `F` nonamenable.
- **Kernel mass sits at finite depth.** Half of all Haar mass is already kernel at depth two, and
  the Dirac spectrum of `R` is null (`odd-measure-kernel-carries-almost-all-haar-mass`).
  * So "a witness must capture mass at infinite depth" is not a valid diagnostic.
  * Group-algebra elements are finitely supported, so no support no-go can require infinite support
    short of refuting the target.
- **More roots of unity give no room against honest compression.**
  * Over `F_q`, the phase units `sum zeta_i P_(C_i)` with `zeta_i in mu_(q-1)`, together with `V`, give
    `C(M_chi, F_q) ⋊ V` on each scalar character factor `A_chi`.
  * Here `M_chi` is the coset of finitely additive `Z/(q-1)`-valued measures fixed by `chi`.
  * Haar measure on that compact group is again `V`-invariant, so Proposition 4 persists for every `q`
    and every `chi`.
  * `#M_chi^P = (q-1)^(|P|-1)` is prime to `p`, so the mod-`p` average of Proposition 5 exists too.
  * Section 10 of the artifact.
- **Gate.** If the signed Thompson group `E ⋊ V` is `F_3`-linear sofic, this claim is false
  (`linear-sofic-group-algebra-is-stably-finite`). Soficity of `V` is open.
- **Where it dies.** A witness needs a cover of `M_-` compressible only modulo 3: multiplicities
  `1 mod 3`, with cross terms cancelling mod 3, or equivalently non-function idempotents equivalent
  to `eps_-`. No such cover has been constructed, and no obstruction to one is known. Section 8 of
  the artifact.
- **Star designs, a sufficient self-adjoint case (w3-corner-crossed).** `x* x = eps_-` with
  `q_[0] x = x` solves this claim with `b' = x` and `c' = x*`. The route is
  `star-compression-design-solves-odd-measure-target`, and existence is the open claim
  `odd-measure-crossed-product-has-star-compression-design`.
  * **Freeness.** `V` acts essentially freely on `(M_-, lambda)`
    (`thompson-action-on-odd-measures-is-essentially-free`).
  * **Weight theorem** (`star-compression-designs-need-weight-four-colliding-columns`). In every star
    design, colliding weight-four columns carry at least half the Haar mass, and colliding columns
    share at least two points with cancelling signs.
  * **Dead designs.** Cancellation-free, two-term and difference-free designs are dead.
  * **Scope.** General solutions with `c' != b'*` escape this counting.
- **Rank obstruction (w3-corner-module, w3-corner-crossed).** Any Sylvester rank function on `B`
  refutes this claim.
  * **Why.**
    - A swap `g` in `V` with `g[0] = [1]` conjugates `q_[0]` to `q_[1] = eps_- - q_[0]`.
    - Rank functions add over orthogonal idempotents, so every rank function has
      `rk(q_[0]) = rk(eps_-)/2`, exactly.
    - `eps_- = c' q_[0] b'` gives `rk(eps_-) <= rk(q_[0])`, which forces `rk(eps_-) = 0`, while
      `rk(eps_-) = 1` for the unit of `B`.
    - Equivalently, the claim makes `eps_-` properly infinite: `eps_- ⊕ eps_- ≲ q_[0] ⊕ q_[1] ~ eps_-`.
    - The exact value is w3-corner-module's sharpening.
  * **This also forbids** `eps_- ~ 1_(W_1)` in the mixed-depth entry below, since that equivalence would
    solve this claim.
  * **Sources.** Densities matter only for building a rank function. The mechanisms below are stated
    self-contained, and no literature theorem is cited.
    - **Sofic action.** A sofic model of `V ↷ (M_-, lambda)`: asymptotic permutation representations of
      `V`, with clopens modelled by asymptotically Boolean, equivariant subsets whose densities tend to
      `lambda`. The ultralimit of normalized ranks of `f[g] -> diag(f) perm(g)` is a rank function with
      `rk(1_U) = lambda(U)`.
    - **Linear soficity.** An `F_3`-linear sofic approximation `pi_n` of `E ⋊ V` (over a field of
      characteristic 3), extended linearly to `F_3[H]`, has an ultralimit rank function with
      `rk(eps_-) = lim rk(1 - pi_n(z)) > 0`, because the approximation separates `z` from `1`.
      Compressing to the corner `B = F_3[H] eps_-` gives one on `B`. So the linear-soficity gate above
      is an instance of this obstruction.
  * **Status.** No rank function on `B` is known. A sofic essentially free action makes `V` sofic, which
    is open.
- **Mixed-depth defect, equivalent to a clopen indicator (w3-corner-cohn-a).** For every choice of
  extending units, the natural lift of `(s_0, t_0)` has a corrected left inverse with
  `tau'' sigma = eps_- - e'`. Here `e' = 2(F - D)`, and `D` is a partial symmetry on
  `F = 1_(W_1) + 1_(W_2)` (`natural-leavitt-pair-lifts-have-partial-symmetry-defect`).
  * **Matrix units.** `(1_(W_1), 1_(W_2), [h]1_(W_1), [h^-1]1_(W_2))` form `2 x 2` matrix units, and `e'` is
    their rank-one idempotent. So `e' ~ 1_(W_1) ~ 1_(W_2)`. Since `W_2 ⊆ {mu([0]) = 1}`, we get
    `e' ≲ q_[0]` for every choice of units. This is Remark 2.3 of
    `research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md`.
  * **Comparison.** `e' ~ eps_-` iff `eps_- ~ 1_(W_1)`, and that would solve this claim: from `x y = 1_(W_2)`
    and `y x = eps_-`, take `c' = y`, `b' = x`. Up to equivalence the defect is a clopen indicator of
    Haar mass `1/4`, not a new non-function idempotent.
  * **Status.** `Tr(1_(W_1)) = 1/4 = 1 = Tr(eps_-)` in `F_3`, so the mod-3 trace allows it. No equivalence
    `eps_- ~ 1_(W_1)` is known. Monomial ones are dead by `odd-measure-space-has-no-honest-thompson-compression`.
