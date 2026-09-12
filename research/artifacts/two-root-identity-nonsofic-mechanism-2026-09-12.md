# The two-root identity and the nonsoficity mechanism

Lane `gk-gate-nonsofic`, 2026-09-12. Supports the Cairn claim
`two-root-identity-is-corner-local-for-leavitt-rank-models` and the Attempts entry on
`rank-models-of-el3-satisfy-the-two-root-identities`.

## Summary

* **Section 1.** Every subgroup containing the nine-leaf configuration is `R^x` itself, so the
  mechanism cannot be localized to a proper nonsofic subgroup through the configuration.
* **Section 2 (established).** The two-root identity is corner-local. For a characteristic-two
  rank model `sigma` of `R^x` and any cylinder corner `P`, these are equivalent: `sigma` is
  trivial; `N_23 N_12 = 0` for the unit pair; `N_23 N_12 = 0` for the corner pair
  `iota_P(unit pair)`. So the root pair may be placed inside the centralizer of the Kazhdan
  subgroup of the configuration.
* **Section 3.** Aim the Hamming mechanism at this one identity with the pair in `C_G(Gamma)`.
  * Conservation (M), the more-than-half collision (C) and fixed-ideal globality all transfer.
  * The defect piece `Q = im(N_23' N_12')` is almost invariant under `sigma(Gamma)`, not fixed.
  * Globality rounds only fixed ideals. Turning an invariant subspace into a fixed object costs
    a factor `n` of normalized scale, and almost invariant subspaces of Kazhdan groups do not
    round over finite fields. So the mechanism dies at rounding (K), now for the single piece `Q`.
* **Section 4.** What a proof along this line must supply.

Notation: `R = L_(F_2)(1,2)`; `S[p]`, `T[p]` the prefix isometries; the 3-leaf code
`zeta = (0, 10, 11)` identifies `R^x = GL_3(R) = EL_3(R)`
(`leavitt-gl-equals-el-and-perfect-unit-group`), with unit pair
`x_12(1) = 1 + S[0]T[10]`, `x_23(1) = 1 + S[10]T[11]`. A rank model is a homomorphism
`sigma : R^x -> M^x`, where `M` is a rank ultraproduct over a field of characteristic two, and
`N_ab = sigma(x_ab(1)) - 1`.

## 1. The configuration generates everything

The nine-leaf configuration (`openai-nine-leaf-leavitt-configuration`) has
`Gamma = EL_alpha(R)`, the units supported on `[0]`, and compressors `u, v` with
`G = <Gamma, u, v> = EL_D(R)`. `EL_D(R) = R^x` by `leavitt-gl-equals-el-and-perfect-unit-group`.
So every subgroup of `R^x` containing the configuration is `R^x`.

Proper nonsofic subgroups containing the unit pair would need a coefficient subring with no rank
model (`rank-modelled-coefficients-violate-two-root-identities`). The smallest subring containing
a unital binary Leavitt family is `R`. No smaller host is available along this line.

## 2. Corner locality (established)

For a prefix `P`, put `S = S[P]`, `T = T[P]` and

```text
iota_P(g) = S g T + (1 - S T).
```

**Lemma 2.1.** `iota_P` is an injective group endomorphism of `R^x`.

*Proof.* `T S = 1` and `T (1 - S T) = 0 = (1 - S T) S`. So

```text
iota_P(g) iota_P(h) = S g T S h T + S g T (1-ST) + (1-ST) S h T + (1-ST)^2 = S gh T + (1 - ST),
```

`iota_P(1) = 1`, and `T iota_P(g) S = g` gives injectivity. QED

**Theorem 2.2.** Let `sigma` be a characteristic-two rank model of `R^x` and `P` any prefix. The
following are equivalent:

1. `sigma` is trivial;
2. `N_23 N_12 = 0` for the unit pair;
3. `sigma(iota_P(x_23(1)) - 1) sigma(iota_P(x_12(1)) - 1) = 0`.

*Proof.* (1) implies (2) and (3) trivially.

**Per-model chain.** Let `tau` be any characteristic-two rank model of `R^x = EL_3(R)` with
`N_23 N_12 = 0` for its unit pair.

* In characteristic two, `x_12(1)^2 = 1` gives `N_12^2 = 0`. So both two-root identities hold, and
  `el3-unit-root-matrix-units-iff-two-root-identities` makes the six unit root elements act by
  matrix units on orthogonal idempotents `p_1, p_2, p_3`.
* `matrix-unit-rank-models-extract-ring-rank-models` gives a unital ring homomorphism from `R` into
  the corner `p_1 M p_1`, which is a rank ultraproduct, unless `p_1 = 0`, in which case `tau` is
  trivial.
* `leavitt-algebra-has-no-unital-rank-model` excludes the first case.

So `tau` is trivial.

* **(2) implies (1).** Take `tau = sigma`.
* **(3) implies (1).** Take `tau = sigma o iota_P`, a rank model of `R^x` by Lemma 2.1. Its unit
  pair values are exactly the values in (3). So `sigma o iota_P` is trivial, and `sigma` kills the
  nontrivial subgroup `iota_P(R^x)`. The kernel of `sigma` is normal, and `R^x` is simple
  (`binary-leavitt-unit-group-is-simple`), so `sigma` is trivial. QED

**Consequence.** For every nontrivial characteristic-two rank model, the product `N_23 N_12`
is nonzero on the unit pair and on the root pair of every cylinder corner at once. A proof of the
gate may test the identity on a pair supported on any single cylinder.

**Corollary 2.3.** `iota_0(x_ab(1)) = x_ab(e_0)`, with `e_0 = S[0]T[0]`. By
`shifted-root-pair-conjugates-to-idempotent-root-pair`, the pair `(x_12(e_0), x_23(e_0))` is
conjugate in `GL_3(R)` to the shifted pair `(x_12(t_0), x_23(s_0))`. So `sigma` is trivial exactly
when `rk(n_23(s_0) n_12(t_0)) = 0`, where `n_ab(r) = sigma(x_ab(r)) - 1`. The shifted pair is not
conjugate to the unit pair, so this is a genuinely different test on the same model. This form
was pointed out by gk-rk-unipotent.

**Remarks.**

* **Alternative proof.** gk-rk-unipotent gives a proof that avoids simplicity of `R^x`. It kills
  `x_12(e_P)` and then uses `R e_P R = R` in normal closures of root elements.
* **Corner models and isometry relations.** `iota_P(x_ij(a)) = x_ij(s_P a t_P)`, so the relations of
  `leavitt-isometry-commutators-constrain-el3-rank-models` apply to `sigma o iota_P` with
  `A_i = n_12(s_P t_i t_P)` and `B_j = n_23(s_P s_j t_P)`. This observation is gk-ri-nofd's.

## 3. The mechanism aimed at the identity

**Placement.** Take `P = 1000`, and let `x' = iota_P(x_12(1))`, `y' = iota_P(x_23(1))`, both supported
on `[1000]`.

* They commute with `Gamma`, the units on `[0]`, since the supports are disjoint.
* The compressor `u` of the configuration maps `[1000]` onto `[0001]` and `[0]` onto
  `u[0] = [0000] u [0010] u [010]`. So `u x' u^-1` and `u y' u^-1` lie in `Gamma` and commute with
  `u Gamma u^-1`.
* By Theorem 2.2, `sigma` is nontrivial exactly when `delta := rk(N_23' N_12') > 0`, where
  `N_12' = sigma(x') - 1` and `N_23' = sigma(y') - 1`.

**What transfers.**

* **(M) conservation.** For exact subspaces moved by invertible `sigma_i(g)`, dimension is conserved
  (`rank-row-compression-audit-2026-09-12`, Section 3).
* **(C) collision.** A subspace cannot contain two independent subspaces each of more than half its
  dimension.
* **(Fix) globality.** `Fix^(a,b)(sigma(Gamma)) = Fix^(a,b)(sigma(R^x))` in every tensor degree
  (`leavitt-rank-models-kazhdan-fixed-ideals-are-global`).

**The defect piece.** At finite stages put `Q_i = im(N_23,i' N_12,i')`, of dimension
`delta n_i + o(n_i)`.

* **Almost invariance.** For `gamma` in `Gamma`, `[x', gamma] = [y', gamma] = 1`. So
  `N_23' N_12' sigma(gamma) - sigma(gamma) N_23' N_12'` has rank `o(n_i)`, and `sigma_i(gamma) Q_i`
  and `Q_i` agree up to `o(n_i)` dimensions.
* **Transport.** `sigma_i(u) Q_i` is the defect piece of the pair `u x' u^-1, u y' u^-1` inside
  `Gamma`, almost invariant under `u Gamma u^-1`, and of the same dimension.

**Where it stops.**

1. **Invariant, not fixed.** Globality comes from Lemma 1 of the audit artifact, which rounds
   pointwise-fixed subspaces. `Q` is invariant under `sigma(Gamma)` but not pointwise fixed. The
   natural fixed objects attached to `Q` are its projection, a fixed vector in degree `(1,1)`, and a
   line in an exterior power. Each has normalized rank `O(1/n)` at its own scale, so globality sees
   rank `0`.
2. **No rounding of invariant pieces, even one piece.** To run (T1) and (C) on `Q` and
   `sigma(u) Q`, the Hamming proof decomposes the space into expanding `Gamma`-components (K).
   Aiming at the single piece `Q` does not help.
   * **The counterexample.** In `kazhdan-group-rank-models-admit-no-expander-decomposition`, the
     models `EL_3(F_2[t]) -> SL_3(F_(2^k))` have the half-degree truncation `W_(k/2)`. It has
     boundary at most `6` and sits at normalized distance about `1/2` from every invariant subspace.
   * **Consequence.** "`Q` almost invariant under `sigma(Gamma)`, hence near an invariant piece" cannot
     follow from property (T) of `Gamma` alone. This was pointed out by gk-l-gate-neg.
   * **What a rescue must use.** Only data that counterexample lacks:
     * the compression relation together with property (T) of the compressor group;
     * the absence of nontrivial finite-dimensional representations of `R^x`, while the counterexample's
       models are honest representations;
     * the global fixed-ideal condition `leavitt-rank-models-kazhdan-fixed-ideals-are-global`.

   Without components there is no target subspace in which `Q` and `sigma(u) Q` could collide.
3. **Nothing finite or sofic suffices.** Every relation among exact pieces of finitely many root
   elements inside a finite subgroup holds in the free profile on finite subgroups, where
   `rk(N_23 N_12) = 3/8` (`finite-subgroup-rank-data-cannot-force-two-root-identity`). Sofic subgroups
   containing the pair carry violating models (`sofic-subgroups-carry-rank-models-violating-two-root-identity`).
   The subgroup used here, `<Gamma, x', y', u>`, contains `Gamma`, the units on `[0]`. That is a copy
   of `R^x`, hence nonsofic, so these calibrations do not kill the argument before (K). The counting
   must involve `sigma(Gamma)` on `Q`, which is step 2.

This is the same failure the audit records for the full rank row, localized to one piece. Aiming
at a single product removes the need to decompose the whole space, but not the need to decompose
the one invariant piece `Q`.

## 4. What a proof along this line needs

Any one of the following would let (M) and (C) act on `Q`:

* **Fixedness.** Show that `sigma(Gamma)` acts on `Q` with a linear-size fixed part. Then
  globality puts that part in `Fix(sigma(R^x))`. On it `N_12'` acts as zero, so the part lies in
  `ker N_12'`. Combined with `Q` inside `im N_23'` this must be turned into `delta = 0`, and no such
  step is known.
* **A conserved size on invariant subspaces.** Find a function on `sigma(Gamma)`-almost-invariant
  subspaces that is additive on independent pieces, conserved by `sigma(u)`, and positive on `Q`.
  This is axiom (A4) of `invariant-size-collapse`, which the audit shows fails for normalized
  dimension of fixed ideals.
* **Commutant rounding.** Show that `N_23' N_12'` lies within rank `o(n)` of the linear-scale commutant
  of `sigma(Gamma)`. Globality then makes it commute with `sigma(R^x)`, hence with `sigma(x_12(1))`
  and `sigma(x_23(1))` of the unit pair. Whether that forces `delta = 0` is open. In any case the
  commutant layer is vacuous whenever `sigma(Gamma)` has no bounded-dimension types, and `R^x` has
  none.
