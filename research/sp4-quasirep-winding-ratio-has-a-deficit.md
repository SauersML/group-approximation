---
rg: 2
id: sp4-quasirep-winding-ratio-has-a-deficit
kind: claim
title: On some finite window, Sp4(Z) quasi-representations fall short of the rephasing-dual winding ratio
distinct_from:
  sp4-quasirep-windings-are-sublinear: that asks for the winding-to-defect ratio to tend to zero; this asks only that its limsup on one window stay strictly below the explicit positive constant |k|/(2 pi beta*_W). It is implied by that claim and strictly weaker as a statement.
  sp4-winding-ratio-sharp-constant-is-gromov-dual: that proves the ceiling nu/(2 pi) and that P_op = R/Z forces the ratio to at least |k|/(2 pi beta*_W) on every window; this is the open inequality in the other direction on a single window.
  deligne-sep8-first-order-tensor-threshold: that is phrased with projective models at a moving parameter; this concerns only plain quasi-representations of Sp_4(Z).
---

**OPEN.** Notation as in `sp4-winding-ratio-sharp-constant-is-gromov-dual`. The claim is that for some relator `r`
with `k != 0` and some finite window `W` containing `W_r`,

```text
Theta(W) = limsup_{eps -> 0+} S_W(eps)/eps  <  |k| / (2 pi beta*_W).
```

A sufficient form, independent of the window: `Theta_inf < nu/(2 pi)`. In words, quasi-representations of
`Sp_4(Z)` do not attain the l1-dual ceiling on the winding-to-defect ratio.

**Why it matters.**
- By item 7 of `sp4-winding-ratio-sharp-constant-is-gromov-dual`, it gives `P_op = (1/m)Z/Z` with `m` even.
- With `deligne-finite-parameter-group-has-period-prime-to-three`, this gives the flagship, via route
  `deligne-triple-cover-via-winding-deficit`.
- It is implied by `sp4-quasirep-windings-are-sublinear`, where `Theta(W) = 0`, but asks much less. Near-extremal
  quasi-representations are allowed to wind linearly, only at a strictly smaller rate than the all-MF branch
  forces.

**How it can fail.**
- `P_op = R/Z` refutes it on every window (item 5 of the theorem node).
- More generally, it fails if, on every window, some sequence of `eps`-quasi-representations reaches ratio
  `|k|/(2 pi beta*_W)`.

**What cannot prove it.** By item 8 of the theorem node, every argument that uses only the scalar data of the defects
reaches the threshold exactly: the determinant cocycle, its integrality, `K_1` classes, and Tr log counting. A proof
must use the traceless (`su(d)`) part of the defects `D(g,h)`. The natural place to look is the support of an
extremal cycle `z*` of the LP for `beta*_W`, since the extremal relaxation data are scalar there. This is a heuristic
pointer, not a proved localization.

## Attempts
- **2026-09-18, swarm-0917-w7-w7-deligne-follow: posed.** It is the weakening of the sublinear-winding prerequisite
  given by the sharp constant. There is no test yet. The determinant class is excluded by item 8 of the theorem node.
- **2026-09-18, swarm-0917-w14-w14-deligne-last1 (quantifier-shift): the limsup collapses to one scale.** See
  `sp4-winding-ratio-is-an-infimum-over-scales`, ESTABLISHED.
  - *Mechanism.* Tensor products add normalized windings and add defects:
    `kappa_r(pi (x) sigma)/(d_1 d_2) = kappa_r(pi)/d_1 + kappa_r(sigma)/d_2` once both defects are at most
    `1/(6g-1)`, since all eigenangles of the relator word are then within `pi/3`. So `S_W` is monotone and
    superadditive on `(0, 1/(6g-1)]`, and Fekete's lemma at zero gives
    `Theta(W) = lim S_W(eps)/eps = inf_{eps <= 1/(6g-1)} S_W(eps)/eps`.
  - *Reduction.* This claim is equivalent to one inequality `S_W(eps_1) < tau_W eps_1` at one scale, recorded as the
    OPEN `sp4-quasirep-single-scale-winding-deficit`, with route `sp4-winding-deficit-from-one-scale`.
  - *All-MF branch.* `P_op = R/Z` forces `S_W(eps) >= tau_W eps` at every scale and on every window.
  - *Obstruction to refutations.* Tensor powers, direct sums and conjugation move winding lower bounds only to
    larger scales. So no finite family of quasi-representations can refute this claim, while one scale suffices to
    prove it. The determinant relaxation stays strictly above `tau_W eps` at every fixed scale, so the class kill of
    item 8 of the sharp-constant node persists at each scale.
