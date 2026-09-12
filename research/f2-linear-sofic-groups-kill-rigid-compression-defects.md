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
