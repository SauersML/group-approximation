---
rg: 2
id: f2-linear-sofic-groups-kill-rigid-compression-defects
kind: claim
title: An F_2-linear sofic group containing an infranormal Kazhdan pair has trivial rigid compression defect
distinct_from:
  hyperlinear-groups-kill-rigid-compression-defects: that is the normalized Hilbert--Schmidt row, where property (T) supplies a spectral gap and only a size is missing; this is the normalized-rank row over F_2, where neither a (T) rounding nor a size is known.
  sofic-groups-kill-rigid-compression-defects: that is the established normalized-Hamming row; this is the row one class up, since sofic groups are F_2-linear sofic and F_2-linear sofic groups are weakly sofic.
  weakly-sofic-groups-can-carry-rigid-defects: that is the established failure one class further up; this is the open intermediate row, which that failure does not decide.
  rigid-compression-defect-normalization-dichotomy: that is the class-independent equivalence between killing defects and normalizing Kazhdan centralizers, with the witness construction; this is the F_2-linear sofic instance stated as a standalone target with its two payoffs.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**OPEN, and a win--win.** The claim: for every countable `F_2`-linear sofic
group `H` and every `Gamma <= G <= H` with `Gamma` and `G` Kazhdan and `Gamma`
infranormal in `G`,

```text
[g z g^-1, gamma] = 1     for all g in G, z in C_H(Gamma), gamma in Gamma.
```

By [[rigid-compression-defect-normalization-dichotomy]] this is equivalent to
normalization in the rank ultraproduct. For every infranormal Kazhdan pair
`Gamma <= G` and every homomorphism
`sigma : G -> U = prod_omega GL_n(F_2) / d_rank`, the group `sigma(G)`
normalizes `C_U(sigma(Gamma))`.

## The two payoffs

- **If this holds:**
  - The binary Leavitt unit group is not `F_2`-linear sofic, since it carries
    a nontrivial defect
    ([[leavitt-unit-group-carries-nontrivial-rigid-defect]]). That gives
    [[non-linear-sofic-group]] through
    [[non-linear-sofic-via-f2-rank-row-defect]].
  - The Kun--Thom wreath is not `F_2`-linear sofic
    ([[kun-thom-wreath-carries-rigid-defect]]), so `F_2`-linear sofic is
    strictly smaller than weakly sofic.
  - It does not settle Kaplansky direct finiteness over `L^x`
    ([[leavitt-packet-linear-sofic-kills-kaplansky-target]]).
- **If this fails:** some `F_2`-linear sofic group carries a nontrivial rigid
  defect. By [[sofic-groups-kill-rigid-compression-defects]] it is nonsofic,
  so sofic is strictly smaller than `F_2`-linear sofic. This is the
  characteristic-two form of Arzhantseva--Paunescu Question 8.5, which
  [[linear-sofic-nonsofic-group]] asks over `C`.

## Attempts

- **Transferring (T) rounding: dead as a direct transfer.**
  - Both proved rows round the Kazhdan group's approximate objects into exact
    ones: the Hamming row by Kun's expander decomposition, the Hilbert--Schmidt
    shadow by the spectral gap on `L^2`.
  - The normalized rank metric has no Hilbert structure. Two matrices at rank
    distance `r` agree only on a subspace containing a `2^(-r)` fraction of
    the vectors of `F_2^n`. So neither the permutation action on `F_2^n` nor
    its `L^2` space carries approximate relations.
  - Bachner, arXiv:2408.15614v2, read at abstract level: "lattices in
    semisimple Lie groups of higher rank are not strictly C-stable" in the
    rank metric, and "free groups are not uniformly flexibly F-stable over any
    field". So Kazhdan lattices do not round in the rank metric even in the
    strict uniform sense over `C`.
  - A proof must use finite-stage structure of the compression, not stability
    of `Gamma`.
- **A faithful size, condition (A3) of the ladder artifact's Theorem 10:
  absent.**
  - Rank ultraproducts carry a faithful rank function on elements and
    idempotents.
  - Commutant algebras `sigma(Gamma)'` have infinite codimension. On them no
    conjugation-invariant monotone size is known that separates proper
    inclusions, so strict conjugation-compressions of the commutant are not
    excluded (artifact Section 10, "Rank ultraproduct").
- **Rounding on finite subgroups: a partial input only.** Observation of lane
  `kdf-leavitt-certificate`:
  - For a finite `K <= H` and a rank almost-representation `f_n` of `K`, the
    image of `F_2[K] (x) V_good -> F_2^n`, `a (x) w -> f_n(a) w`, is an honest
    `K`-submodule of codimension at most `|K|^2 eps n`.
  - This is flexible rank stability of finite-dimensional algebras
    (Bauer--Blachar--Greenfeld arXiv:2401.04676, Theorem 5.1, audited in
    `atlas-rank-stability-literature-fence`).
  - So rounding exists on finite and locally finite subgroups, including the
    level-preserving units of `L^x`. It does not reach the Kazhdan pair.
- **Monotonicity: brackets the row without deciding it.** Since sofic is
  contained in `F_2`-linear sofic, which is contained in weakly sofic, the
  established sofic row holds below and the weakly sofic failure sits above.
- **Stable finiteness: necessary, not sufficient.**
  - `F_2`-linear soficity of `L^x` needs `F_2[L^x]` directly finite, which is
    open.
  - Greenfeld, arXiv:2210.11650, abstract: "there exist finitely generated,
    stably finite algebras which are non linear sofic". So for algebras,
    direct finiteness cannot certify the positive side.
- **The natural Cantor truncation model of `L^x`: dead.**
  - `R` acts on locally constant `F_2`-valued functions on `2^N`. Truncate to
    `LC_M = F_2^(2^M)`.
  - A prefix replacement `a -> b` with `|b| > |a|` moves `2^(M-|a|)`
    dimensions of functions on `[a]` into room for `2^(M-|b|)` on `[b]`. The
    truncated matrix loses normalized rank at least `2^(-|a|) - 2^(-|b|)`,
    independent of `M`.
  - By Kraft's equality, every length-changing element of Thompson `V` has
    such a branch, because `V` preserves no measure on `2^N`.
  - A positive model needs rank-preserving transport, which this action does
    not supply. This rules out only the natural truncation, not other bases.
- **The linear-scale layer: complete with no (T), and insufficient
  (2026-09-12, lane `gk-kdf-structure`).**
  - [[rank-ultraproduct-compressors-conserve-fixed-right-ideals]]: fixed right
    ideals of a compressed finitely generated subgroup round for free,
    `rk((1-e)x) <= sum_s rk((s-1)x)`. Compressors conserve them in every tensor
    degree, and the normal closure fixes them pointwise. Degree `(1,1)` is the
    linear-scale part of the commutant.
  - So (A1)-(A3) of Theorem 10 hold on this layer with size `rk`, and rounding there
    needs no property (T). The rounding and size gaps recorded above live below
    linear scale.
  - (A4) fails on this layer, and
    [[linear-scale-rank-conservation-does-not-kill-defects]] shows it cannot kill
    defects without property (T) of the compressor group: the sofic literal group
    `E` satisfies every conclusion while its defect survives.
  - Consequence for the payoff group: every rank model of `L^x` has the nine-leaf
    Kazhdan subgroup fixing exactly what `L^x` fixes, in every degree
    ([[leavitt-rank-models-kazhdan-fixed-ideals-are-global]]).
- **Which step of the Hamming proof is permutation-specific**
  (`research/artifacts/rank-row-compression-audit-2026-09-12.md`, Section 3).
  - *Transfer.* No room to drift: for an invertible `s` carrying pieces into single
    pieces, `sum_l |d_l - sum_(tau(j)=l) d_j| <= 2 sum_j leak_j`. Also the
    more-than-half collision, since independent subspaces add dimensions.
  - *Fail.* Rounding into expanding pieces: almost invariant subspaces do not round,
    as in the cyclic `F_2^(2^m)` example, and property (T) does not repair this (next
    item).
  - *Fail.* One-piece transport, which consumes monomiality. A compressor
    `rho(t) (x) B` with non-monomial `B` sends `W (x) e_1` to the graph
    `{ w (x) e_1 + w (x) e_2 }`, which lies inside no single piece. The
    Hilbert--Schmidt row fails at the same step
    ([[nonmonomial-multiplicity-obstructs-hs-compressor-transport]]).
  - So a proof along these lines would need finite-stage multiplicity coordinates on
    which compressors act monomially up to rank `o(n)`, plus a rank-expansion input for
    Kazhdan groups. Neither is known, and the second cannot come from property (T).
- **Rank rounding from property (T): refuted (2026-09-12, lane `gk-kdf-structure`).**
  - [[kazhdan-group-rank-models-admit-no-expander-decomposition]]: `EL_3(F_2[t])` is
    Kazhdan, yet its representations over `F_(2^k)`, viewed over `F_2`, are irreducible
    and still carry almost-invariant subspaces.
    - Multiplication by a field generator is a companion-matrix shift, and the degree
      truncations have boundary at most `6` in every dimension.
    - So there is no rounding modulus, and no uniform dimension expansion.
    - Every decomposition into internally `kappa`-expanding pieces leaks linearly:
      `lambda > kappa/21`.
    - Linear-size pieces stay non-expanding under `o(n)` rank perturbations of the models.
  - [[kazhdan-rank-ultraproducts-can-have-diffuse-commutants]]: in the rank ultraproduct
    the relative commutant carries a continuous chain of idempotents, and invariant
    right ideals have no atoms. In Hamming and Hilbert--Schmidt the uniform spectral gap
    forbids both.
  - Over `C` the conclusion is the opposite: the unitary argument gives
    `sum_s e_s(W) >= kappa^2 dim W/4` for irreducible representations. The obstruction
    is specific to finite coefficient fields and holds over every `F_p`.
  - The same models exist for the Theorem E subgroup `EL_r(F_2[x_1..x_d])`.
  - Consequence: step (K) of the Hamming normalization proof has no rank-metric form
    available from property (T) of `Gamma`. A proof of this claim must use a different
    input: property (T) of the compressor group jointly with the compression, or a size
    that does not come from atoms.
  - Not covered: pieces of sublinear dimension in perturbed models, and whether some
    other size on the (possibly commutative) relative commutant forbids strict
    compression. This claim stays OPEN in both directions.
