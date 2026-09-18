---
rg: 2
id: kazhdan-profinite-untwisting-is-virtual-splitting
kind: claim
title: For a Kazhdan group, a scalar multiplier is a measurable coboundary on an ergodic profinite action only if it is virtually a coboundary along that action
distinct_from:
  ioana-profinite-cocycle-superrigidity: Ioana untwists 1-cocycles of free profinite actions into countable groups; this untwists a 2-cocycle, a constant circle-valued multiplier, over a possibly non-free profinite action, with the uncountable target T, and the conclusion is exact finite-dimensional projective realizability rather than virtual cohomology to a homomorphism.
  central-bernoulli-lifts-force-splitting: that is the Bernoulli (Popa) side with finite coefficients; this is the profinite side with circle coefficients, where Popa does not apply and the proof is a Kazhdan projection plus a Peter--Weyl descent.
  sp4-maslov-circle-survives-in-bernoulli-l0-cohomology: that computes the image of H^2(Gamma,T) in Bernoulli L^0 cohomology via Jiang; this computes it for every ergodic profinite action of any property (T) group.
  deligne-monomial-twisted-modules-have-no-folner-truncations: that excludes exact monomial truncations of fixed twisted modules; this excludes a coherent measurable phase field over the whole profinite tower, which is a strictly larger class of monomial candidates.
---

**ESTABLISHED** by `kazhdan-profinite-untwisting-is-virtual-splitting-proof`.

**Setting.** `Gamma` is a countable group with property (T), and `alpha in Z^2(Gamma, T)` is a normalized scalar
2-cocycle. `pi : Gamma -> K` is a homomorphism with dense image in a second-countable profinite group `K`, and
`Gamma` acts on `(K, Haar)` by `g . x = pi(g) x`. An ergodic profinite action of `Gamma` (inverse limit of a
countable tower of finite transitive actions) is `K/L` with its Haar measure, for such `K` and a closed subgroup
`L`, so this is the general case up to passing to a factor `K -> K/L`. The map `pi` need not be injective, so the
action need not be free.

Say `alpha` is a **measurable coboundary on** a p.m.p. action `Gamma ~> X` if there is a measurable
`c : Gamma x X -> T` with

```text
c(g, h x) c(h, x) = alpha(g, h) c(gh, x)      for all g, h in Gamma and a.e. x.        (U)
```

Equivalently, `[alpha]` dies under `H^2(Gamma, T) -> H^2(Gamma, L^0(X, T))`. A solution of (U) gives an
isomorphism `L^infty(X) x|_alpha Gamma = L^infty(X) x| Gamma` that is the identity on `L^infty(X)` and sends
`u_g` to `conj(c(g, g^{-1} .)) u_g`.

**Theorem.**
1. If `alpha` is a measurable coboundary on `Gamma ~> K`, then there is an open subgroup `U <= K` such that
   `alpha` restricted to `Lambda = pi^{-1}(U)` is a coboundary in `Z^2(Lambda, T)`. Equivalently, `Gamma` has an
   exact `alpha`-projective unitary representation on `l^2(K/U)`, of dimension `[Gamma : Lambda]`, of monomial form.
2. Conversely, if `alpha|pi^{-1}(U)` is a coboundary for an open subgroup `U`, then `alpha` is a measurable coboundary
   on `K` (Shapiro on the finite quotient `K/U`, pulled back).
3. For an arbitrary ergodic profinite action `X = K/L`: if `alpha` is a measurable coboundary on `X`, the same
   conclusion as in 1 holds, since `c` pulls back along the factor map `K -> K/L`.

So, for Kazhdan groups, the kernel of `H^2(Gamma, T) -> H^2(Gamma, L^0(K, T))` is exactly the union over open
`U <= K` of the kernels of restriction to `pi^{-1}(U)`.

**Corollary (invisible multipliers).** If `Gamma` has property (T) and `alpha` has no nonzero finite-dimensional
exact projective representation, then `alpha` is not a measurable coboundary on any ergodic profinite action of
`Gamma`. The Deligne instance is `deligne-multiplier-survives-on-bernoulli-times-profinite-actions`.

**Mechanism in one line.** Double the phase field: `c(g,x) conj(c(g,y))` has no multiplier, so it twists a genuine
representation `rho` of `Gamma` on `L^2(K x K)`. The normalized indicators of the level-`n` coset relation are almost
`rho`-invariant by martingale convergence. Property (T) turns them into an invariant vector, and the invariant
vector says `c` is cohomologous to its right translate `c(., . k)` for a positive-measure, hence open, set of `k`.
The translation symmetries then form a compact central `T`-extension of an open subgroup of `K`. Peter--Weyl splits it
over a smaller open subgroup `U`, and the split symmetries push `c` down to the finite set `K/U`.

**Where the argument needs coherence.** Almost-invariance uses that `c(g, .)` is `L^2`-approximated by its conditional
expectations on coarser levels. A sequence of phase fields on the finite Schreier graphs `Gamma/Gamma_n` with
frustration tending to zero, not arising from one measurable field on the limit, has no such coarser approximation.
At a fixed finite level the doubling trick returns only the diagonal, which is exactly invariant and carries no
information. The theorem therefore excludes coherent towers and says nothing about incoherent finite-level voltage
models, which stay governed by `deligne-class-finite-action-norms-vanish` and
`deligne-class-congruence-cosystole-bounded-below`.

**Model test.**
- **Hypothesis side.** Property (T) is used once, in Step 3 of the route: almost-invariant vectors are close to
  invariant ones. Nothing is claimed without (T). For `Gamma = Z^2` and the Heisenberg multiplier `alpha_theta`,
  `theta` irrational, the conclusion would say `alpha_theta` dies on no profinite action, because its restriction to
  `m Z^2` is `alpha_{m^2 theta}`, which is still nontrivial. Whether that holds is not addressed here.
- **Conclusion side.** A virtually split multiplier (`alpha|Lambda` trivial) is untwisted on `Gamma/Lambda`, and so
  on every profinite action factoring onto it. This is item 2, so the dichotomy is sharp.
