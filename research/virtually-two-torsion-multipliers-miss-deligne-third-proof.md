---
rg: 2
id: virtually-two-torsion-multipliers-miss-deligne-third-proof
kind: route
title: Induce the squared class from the stabilizer, then apply pointwise closedness of coboundaries
target: virtually-two-torsion-multipliers-miss-deligne-third
requires:
  - deligne-triple-cover-fd-central-invisibility
  - sp4-metaplectic-class-pointwise-coboundary-limit
---

**Step 1 (exact projective representations are representations of E_3).**
Let `pi : Gamma -> U(V)` with `dim V < infinity` and
`pi(g)pi(h) = c(g,h) pi(gh)`, where `c = c_j * delta(lambda)` for a scalar
cochain `lambda`.  Replacing `pi` by `lambda^(-1) pi` turns the multiplier
into exactly `c_j`.  Then `rho(z^m s(g)) = exp(2 pi i j m/3) pi(g)` is a
genuine unitary representation of `E_3`: the product rule follows from
`s(g)s(h) = z^(b(g,h)) s(gh)` and centrality of `z`.  It has
`rho(z) = exp(2 pi i j/3) != 1` for `j = 1, 2`, contradicting
`deligne-triple-cover-fd-central-invisibility` (DTC2).  Hence **no
finite-dimensional unitary projective representation has multiplier class
`[c_1]` or `[c_2]`.**

**Step 2 (squares die on Gamma' implies a finite-dimensional model).**  Let
`c in Z^2(Gamma,T)` with `c|Gamma' = delta(lambda)` for some finite-index
`Gamma'`.  Then `chi = lambda^(-1)` is a one-dimensional `c|Gamma'`-projective
representation of `Gamma'`.  Projective induction gives a finite-dimensional
`c`-projective unitary representation.  Concretely, let `N = [Gamma:Gamma']` and form the
left module `M = C^c[Gamma] ⊗_{C^c[Gamma']} C_chi` over the twisted group
algebra (`u_g u_h = c(g,h) u_gh`).  Choose coset representatives
`t_1, ..., t_N`.  The vectors `e_i = u_(t_i) ⊗ 1` form a basis of `M`.  If
`g t_i = t_k h` with `h in Gamma'`, then

```text
u_g e_i = c(g,t_i) c(t_k,h)^(-1) chi(h) e_k,
```

so `u_g` is a monomial matrix with unimodular entries, hence unitary.  The
module relation gives `u_g u_h = c(g,h) u_gh`.  So `[c]` is realized in
dimension `N`.

**Step 3 (VT1).**  Suppose `omega` is virtually 2-torsion and
`omega ~ c_1`.  Then `omega^2 ~ c_1^2 = c_2`, since `b` is integer valued, and
`omega^2|Gamma'` is a coboundary.  Hence `c_2|Gamma'` is a coboundary.  By
Step 2, `[c_2]` is realized in finite dimension, contradicting Step 1.  If
`omega ~ c_2`, then `omega^2 ~ c_4 = c_1` and the same argument applies.

**Step 4 (VT2).**  If `mu_n rho_n` were an asymptotic `c_j`-model, compare
the two asymptotic product rules on the same unitaries:

```text
|omega_n(g,h) * delta(mu_n)(g,h) - c_j(g,h)| -> 0.
```

Since `omega_n -> omega`, the coboundaries `delta(mu_n)` converge pointwise
to `c_j omega^(-1)`.  By `sp4-metaplectic-class-pointwise-coboundary-limit`,
`B^2(Gamma,T)` is closed in the product topology.  So `c_j omega^(-1)` is a
coboundary, i.e. `omega ~ c_j`, contradicting Step 3.
