---
rg: 2
id: twisted-generator-liftability-proof
kind: route
title: Stinespring-dilate the generator lift, average the corner with property (T), and hit Deligne invisibility
target: twisted-generator-liftability-implies-e3-nonhyperlinear
requires:
  - kazhdan-almost-invariant-corner-near-invariant-projection
  - deligne-triple-cover-fd-central-invisibility
---

**`(1) => (2)`.**  Suppose `Theta : A_alpha -> prod_omega M_(d_n)` is a
unital *-homomorphism and `phi_n` are ucp maps with
`Theta(u_s) = [(phi_n(u_s))]` for the canonical generators `s` of a
finite Kazhdan generating set `S` of `Gamma = Sp_4(Z)` (enlarging the
generator list is harmless).  Stinespring gives unital *-representations
`rho_n : A_alpha -> B(H^_n)` and isometries `V_n : C^(d_n) -> H^_n` with
`phi_n = V_n^* rho_n(.) V_n`; then `pi_n(g) := rho_n(u_g)` is a genuine
`alpha`-projective unitary representation of `Gamma`.  Since
`Theta(u_s)` is a unitary of the tracial ultraproduct,
`|| phi_n(u_s)^* phi_n(u_s) - 1 ||_(2, d_n) -> 0` along `omega`, so with
`P_n = V_n V_n^*`:

```text
|| P_n^perp pi_n(s) P_n ||_HS^2 = d_n - || P_n pi_n(s) P_n ||_HS^2 = o(d_n),
```

and likewise for `s^(-1)` (using `phi_n(u_s^*)`), giving
`|| [pi_n(s), P_n] ||_HS = o(sqrt d_n)` for all `s in S`.

The conjugation map `Ad pi_n : g -> pi_n(g) (.) pi_n(g)^*` is a genuine
unitary representation of `Gamma` on `HS(H^_n)`: the multiplier is a
scalar and cancels in `Ad`.  `Gamma` has property (T), so the corner
lemma `kazhdan-almost-invariant-corner-near-invariant-projection`
applies verbatim to the almost-invariant projection `P_n` under
`Ad pi_n` and yields a finite-rank projection `E_n` commuting with
every `pi_n(g)`, of rank `d_n(1 + o(1)) >= 1` along `omega`.  Then
`V_n := ran E_n` is a nonzero finite-dimensional `pi_n(Gamma)`-invariant
subspace, and `pi_n|_(V_n)` is a nonzero finite-dimensional
`alpha`-projective unitary representation of `Gamma`.  Such a
representation is a finite-dimensional unitary representation of the
triple cover `E_3` sending the central `z` to a nontrivial scalar,
contradicting `deligne-triple-cover-fd-central-invisibility`.  Hence no
`Theta` admits generator lifts; if TGL1 holds, no `Theta` exists at all.

**`(2) => (1)`** is vacuous quantification.

**The goal consequence.**  If `E_3` were hyperlinear, `L(E_3)` would
embed trace-preservingly in `R^omega`; cutting by the central projection
`p_alpha = (1/3) sum_k conj(omega)^k z^k` embeds the fibre
`p_alpha L(E_3)` into `p R^omega p`, which is again a tracial matrix
ultraproduct (compress each coordinate by a projection of the right
rank), and the canonical `alpha`-projective unitaries generate it: a
unital *-homomorphism `A_alpha -> prod_omega M_(d'_n)` exists,
contradicting `(2)`.  So TGL1 implies `E_3` is not hyperlinear.
