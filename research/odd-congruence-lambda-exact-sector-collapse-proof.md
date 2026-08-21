---
rg: 2
id: odd-congruence-lambda-exact-sector-collapse-proof
kind: route
title: Property T lifts everything into the congruence commutant, where the three-term Weyl relation evaluates the corrector to one
target: odd-congruence-lambda-exact-sector-collapses
requires:
  - odd-congruence-exact-sector-is-one-inner-action
---

Fix the sector data: `sigma_m : Lambda -> U(d_m)` genuine
representations factoring through `G_m = SL_3(Z/n_m)`, `n_m` coprime
to `2p`, with `pi|_Lambda = [sigma_m]` in `M = prod_U M_(d_m)`, and
`V = pi(h)`.

**Step 0 (the congruence commutant tower).**  Write
`R_m = sigma_m(G_m)' subseteq M_(d_m)` and `R_U = prod_U R_m
subseteq M`.  Since `Lambda -> G_m` is onto, `sigma_m(Lambda)` and
`sigma_m(Lambda_-)` (`Lambda_- = Lambda cap h^(-1) Lambda h`, which
contains the principal congruence subgroup `Lambda(4)` and hence
still surjects onto `G_m` by strong approximation and coprimality)
generate the same algebra, with common commutant `R_m`.

**Step 1 (property (T) lifting).**  `Lambda` and its finite-index
subgroup `Lambda_-` have property (T) with fixed Kazhdan pairs.  For
a genuine representation the conjugation action `Ad sigma_m` is a
genuine unitary representation of `Lambda` on Hilbert--Schmidt space
whose invariant vectors are exactly `sigma_m(Lambda)' = R_m`; the
Kazhdan constant bounds the distance to invariant vectors, so any
`x in M` commuting with `pi(Lambda)` (resp. `pi(Lambda_-)`) has
representatives `x_m` with `dist_2(x_m, R_m) <= (1/epsilon) max_F
||[x_m, sigma_m(lambda)]||_2 -> 0`.  Hence

```text
pi(Lambda)' cap M = pi(Lambda_-)' cap M = R_U.                  (OSP1)
```

(This step is where `Lambda`-exactness is essential: for approximate
`sigma_m` the conjugation action is not a representation and row 2 of
`rc3-standard-tools-all-fail-audit` applies.  It is also why no
regularity or multiplicity hypothesis is needed.)

**Step 2 (the exact slot and the corrector).**  Choose `lambda_(h,m)
in Lambda` with `lambda_(h,m) = h mod n_m` and set `V' =
[sigma_m(lambda_(h,m))]`, well defined because `sigma_m` factors
through `G_m`.  As in `odd-congruence-exact-sector-is-one-inner-action`:
`V'` is a limit of image elements, so it commutes with `R_U`; both
`V` and `V'` implement `lambda -> h lambda h^(-1)` on `pi(Lambda_-)`,
so `W := V'^* V` commutes with `pi(Lambda_-)`, hence by `(OSP1)`

```text
W in R_U,  and so  [W, pi(lambda)] = 0 (lambda in Lambda),
[W, V'] = [W, V'_x] = 0                                          (OSP2)
```

for every image element `V'_x = [sigma_m(mu_m)]`, `mu_m in Lambda`.

**Step 3 (the Weyl relations evaluate `W`).**  Let `w_13, w_12,
w_23 in Lambda` be signed permutation matrices; in `Gamma`:

```text
w_13 h w_13^(-1) = h^(-1),    h' := w_12 h w_12^(-1),
h'' := w_23 h w_23^(-1),      h h''^(-1) = h'                    (OSP3)
```

(diagonal conjugation permutes the entries: `diag(2,1,1/2) *
diag(1/2,2,1) = diag(1,2,1/2)` at `p = 2`, and identically for
general `p`).  Since `pi` is a genuine homomorphism these hold
exactly in `M`.  Now substitute `V = V' W` and push `W` through
everything it commutes with (`(OSP2)`):

- `pi(w_12) V pi(w_12)^(-1) = [pi(w_12) V' pi(w_12)^(-1)] W =
  V'_(h') W` where `V'_(h')` is the image slot of `h' mod n_m`
  (conjugating an image element by an image element stays an image
  element); likewise `pi(h'') = V'_(h'') W`.
- The three-term relation gives
  `pi(h) pi(h'')^(-1) = V' W W^(-1) V'_(h'')^(-1) = V' V'_(h'')^(-1)
  = V'_(h')` (image elements multiply by their congruence values,
  and `h h''^(-1) = h' mod n_m`), while `pi(h') = V'_(h') W`.
  Equating: `V'_(h') = V'_(h') W`, so

  ```text
  W = 1  exactly.                                               (OSP4)
  ```

  (The first relation of `(OSP3)` gives `W^2 = 1` by the same
  computation; it is subsumed by `(OSP4)` and recorded because it is
  ALL that survives at `SL_2`, where the diagonal has one Weyl
  direction and no three-term relation — the involution seed.)

**Step 4 (collapse).**  `W = 1` gives `V = V'`, which commutes with
`R_U supseteq pi(Lambda)' cap M` by Step 2.  So every
`k in pi(Lambda)' cap M` commutes with `pi(h)` and with `pi(Lambda)`,
hence with `pi(Gamma)` (`Gamma = <Lambda, h>`):
`pi(Lambda)' cap M subseteq pi(Gamma)' cap M`, and the reverse
inclusion is automatic.  This is `(OS1)`.

**Scope.**  Everything used: exactness of the `Lambda`-restriction
(Step 1), oddness/coprimality (existence of the `h`-image, Step 2),
and rank two (the three-term relation, Step 3).  No trace condition
entered, so the theorem covers every trace profile over this sector,
in particular the regular one consumed by the goal routes.
