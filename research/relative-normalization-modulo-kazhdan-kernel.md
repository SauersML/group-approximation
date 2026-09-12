---
rg: 2
id: relative-normalization-modulo-kazhdan-kernel
kind: claim
title: Sofic representations of a rigid pair normalize the relative centralizer modulo a normal Kazhdan subgroup
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is the Kun--Thom theorem that sigma(G) normalizes the exact centralizer C(sigma(Gamma)), the case M = 1; this asks the same for the group of permutations normalizing sigma(M) whose commutators with sigma(Gamma) lie in sigma(M).
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the group-level relative criterion; this is its ultraproduct form, equivalent to it by relative-defect-normalization-dichotomy, which is where the Kun--Thom finite-stage machinery would have to run.
  relative-element-splits-into-m-times-centralizer: that proposed the stronger splitting sigma(z) in sigma(M).C(sigma(Gamma)), refuted by outer automorphisms trivial modulo M; this makes no splitting claim and is not affected by that obstruction.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**OPEN.** Let `Gamma <= G` be a rigid pair and `M <= Gamma` a Kazhdan
subgroup normal in `G`. For every homomorphism `sigma : G -> S_U`, `sigma(G)`
normalizes

```text
N_rel(sigma) = { x in S_U : x sigma(M) x^-1 = sigma(M), [x, sigma(Gamma)] <= sigma(M) } .
```

By `relative-defect-normalization-dichotomy` this is equivalent to
`sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`. The case `M = 1`
follows from Kun--Thom Theorem 4.1, which covers trace-zero sofic
representations, together with `rigid-compression-defect-normalization-dichotomy`
for arbitrary homomorphisms. Conjugation by `sigma(Gamma)` preserves `N_rel(sigma)`
automatically, so only strict compressors matter.

## Attempts

- **Splitting into `sigma(M) . C(sigma(Gamma))`: dead.** A splitting
  `sigma(z) = sigma(m_0) c` forces `z` to act on `Gamma` as the inner
  automorphism by `m_0`. Take `H = SL_3(Z) semidirect <alpha>` with `alpha` the
  transpose-inverse, and `M = Gamma = G = SL_3(Z)`, `z = alpha`. Then
  `[z, Gamma] <= M`, but `alpha` sends the companion matrix of `x^3 - 2x^2 - 1`
  (trace 2) to a matrix of trace 0, so it is not inner. Found by lane
  `hyperbolic-sofic`. This claim holds trivially in that example, since
  `Gamma = G`.
- **Invariant factor: vacuous exactly where it is needed.** Each `x` in
  `N_rel(sigma)` normalizes `sigma(M)`, so it preserves the diagonal algebra
  `D^{sigma(M)}` of `sigma(M)`-invariant functions. On that algebra
  `[x, sigma(gamma)]` acts trivially, so `x` commutes with `sigma(Gamma)`, and
  `sigma(G)` acts through `G/M`. Kun--Thom Theorem 4.1 at this level would need
  a sofic (trace-zero) representation of `G/M` on the factor. For the Leavitt
  cover, the block lemma `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`
  makes `sigma(G)` act trivially there, so the factor carries no information.
  All the content lies inside the `sigma(M)`-blocks. There
  `[sigma(g) x sigma(g)^-1, sigma(gamma)]` fixes `D^{sigma(M)}` pointwise and
  must be shown to be a single element of `sigma(M)`. That is a uniform
  condition, not a blockwise one, and no rounding theorem gives it. **This is
  where it stops.**
- **2-norm criterion (from `hyperbolic-sofic`).** An injective trace-zero
  `sigma` of `H` extends to a trace-preserving embedding of `L(H)` into the
  tracial ultraproduct, and `E_{sigma(L(M))} sigma(u_d) = sigma(E_{L(M)} u_d)`,
  which is `u_d` or `0` according as `d in M`. So for a defect element
  `d = [g z g^-1, gamma]`, any lower bound `||E_{sigma(L(M))} sigma(u_d)||_2 > 0`
  gives `d in M`. Caveat: `sigma(L(M))` is not the block algebra of the finite
  groups `sigma(M)|_B`. A lower bound for the conditional expectation onto the
  larger block algebra does not suffice.
- **Relativizing the Kun--Thom cluster counting: dead as a direct transfer
  (lane `rnorm-kazhdan-kernel`).**
  - **What powers Theorem 4.1:** the cluster groupoid of the `Gamma`-expander
    components is finite. The compressor functor is faithful, and orbit sizes
    `o_n` and isotropy sizes `k_n` are one-sided monotone under it. The median
    argument with (T) of `G` makes them almost invariant, so the index of the
    induced isotropy inclusion is an integer below 2, hence 1, and the functor
    is bijective on Hom-sets.
  - **Relative arrows** are approximate bijections between components that
    intertwine the `Gamma`-actions up to a twist `phi in Aut(Gamma)` trivial
    modulo `M`. For a fixed twist they form a torsor over the `Gamma`-isotropy,
    and the distance gap still holds.
  - **Twists are unbounded.** For distinct `m, m'` in the infinite group `M`,
    `sigma(m)|_B` and `sigma(m')|_B` are relative arrows with twists `Ad m` and
    `Ad m'`, and trace zero puts them at relative distance `1 - o(1)` on most
    components. So relative Hom-sets are unbounded along `U`, and there is no
    integer index to compare.
  - **Modulo inner twists,** the realized outer twist classes on a component
    contain the image of `Q = Z/(M . C_H(Gamma))`. Compressors act on `Q` by
    injective endomorphisms, which are strict exactly when the defect is
    nontrivial (`relative-defect-iff-surjective-compressor-endomorphisms`).
    For the Leavitt cover `Q = C_(R^x)(EL_alpha(R))`, which contains a copy of
    Thompson's `V` and is not co-Hopfian.
  - **So a proof must supply a new size.** It needs a size on realized outer
    twists that is one-sided monotone under compressors, like `o_n` and `k_n`,
    and that no strict self-embedding can preserve. Cardinality cannot do this
    for infinite `Q`. A measure-type size, such as the support proportion
    that corner embeddings of `V` halve, is the natural candidate; none is
    constructed. **This is where it stops.**
- **Measure-type twist sizes: the support-proportion candidate is dead
  (lane `rnorm-twist-measure`).**
  - **Twists are global.** `realized-relative-twists-embed-in-outer-twist-group`:
    - `N_rel(sigma)/(sigma(M) . C(sigma(Gamma)))` embeds in the outer twist
      group `Out_M(Gamma)`, which does not depend on `sigma`;
    - compressors act by an algebraic endomorphism `eps_t`, injective on the
      realized part;
    - the realized part is the stabilizer of the `S_U`-conjugacy class of
      `sigma|_Gamma`.
    So twist data is not point dependent, and the Kun--Thom pigeonhole has no
    twist-valued point function to run on.
  - **Conjugation-invariant sizes are exactly invariant.**
    `conjugation-invariant-sizes-miss-relative-defect`: `eps_t` moves realizer
    sets by conjugation, so every size read from conjugacy invariants of
    realizers never changes. That includes support proportions, which are `1`
    on nontrivial host elements in trace-zero models. The candidate
    `support-proportion-size-separates-compressor-images` is refuted and the
    route `rnorm-via-support-proportion-size` is invalidated.
  - **Red-flag check.** Neither result uses property (T) beyond the absolute
    normalization, and both hold in amenable hosts. So they correctly prove no
    nonsoficity, in particular nothing about Thompson's `V`.
  - **Surviving shape.** A size has to be a relative invariant of
    (realizer set, `sigma(Gamma)`). By the stabilizer form, that is an
    invariant of the conjugacy class of `sigma|_Gamma`: Kun--Thom cluster data
    of `Gamma`-components with their masses, on which `Out_M(Gamma)` acts by
    precomposition.
    - A contradiction needs a monotone quantity comparing the stabilizer of
      that data with its `eps_t`-image.
    - For infinite stabilizers such as `V`, orbit counting fails, so the
      quantity must be a relative index bounded by the (T)-rigidity of
      components.
    - None is constructed. **This is where it stops.**
