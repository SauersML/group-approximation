---
rg: 2
id: congruence-exit-tensoring-total-collapse-proof
kind: route
title: Split bounded-type projections along an exact tensor factor and average the packet over its fixed vectors
target: congruence-exit-tensoring-forces-total-packet-collapse
requires:
  - kazhdan-bounded-unitary-types-are-finite
  - kazhdan-bounded-types-form-central-summand
  - commutant-density-forces-bounded-type-mass
  - toeplitz-self-embedding-fixes-unbounded-congruence-types
---

Normalized traces throughout: `tr_n` on `M_n`, `tau` on `M`, and `tau (x) tr_m`
on `M (x) M_m`.

## 1. Individual type projections

Fix an irreducible finite-dimensional type `theta` of `Lambda`, of degree
`t`.  The proof of `kazhdan-bounded-types-form-central-summand` uses Wang
isolation to produce the ideal of `C*_max(Lambda)` with spectrum
`{theta}`.  That ideal is `M_t`, and its unit `p_theta` is central.  Then

```text
C*_max(Lambda) p_theta ≅ M_t    (via theta),
theta'(p_theta)=delta_(theta,theta') for every irreducible theta'.   (1)
```

For any tracial `pi`, `pi` restricts to a unital `*`-homomorphism
`M_t -> e_theta M e_theta`, where `e_theta=pi(p_theta)`.  Uniqueness of the
trace on `M_t` gives

```text
tau o pi = tau(e_theta) tr_t          on C*_max(Lambda) p_theta.        (2)
```

Distinct `e_theta` are orthogonal, so `sum_theta tau(e_theta)<=1`.

## 2. Bounded-type mass of a tensor product

Let `rho:Lambda->U(m)` be irreducible of degree `m`, and fix a type `sigma`
of degree `s`.  Put

```text
Y=(id (x) rho)(Delta p_sigma) in C*_max(Lambda) (x) M_m,
```

where `Delta g = g (x) g`.  For every representation `vartheta` of
`C*_max(Lambda)`, `(vartheta (x) id)(Y)` is the `sigma`-isotypic projection
of `vartheta (x) rho`.  Finite-dimensional Frobenius duality gives

```text
Hom(sigma, vartheta (x) rho) ≅ Hom(sigma (x) rho-bar, vartheta).
```

So `(vartheta (x) id)(Y)` vanishes unless `vartheta` meets the finite set
`S` of constituents of `sigma (x) rho-bar`.  Put `P_S=sum_(theta in S) p_theta`.
Then `Y((1-P_S) (x) 1)` vanishes in every irreducible representation, hence
is zero.  Therefore

```text
Y = sum_(theta in S) Y(p_theta (x) 1),
Y(p_theta (x) 1) in M_t (x) M_m.                                        (3)
```

Under `theta (x) id`, `Y(p_theta (x) 1)` is the `sigma`-isotypic projection
of `theta (x) rho`, whose rank is

```text
s mult(sigma, theta (x) rho) = s dim Hom(sigma (x) rho-bar, theta) <= s (s m / t).
```

Also `Hom(sigma, theta (x) rho) != 0` gives `Hom(theta-bar (x) sigma, rho) != 0`,
so `m <= t s`.  By `(2)`,

```text
(tau (x) tr_m)((pi (x) rho)(Y(p_theta (x) 1)))
  = tau(e_theta) rank/(t m) <= tau(e_theta) s^2/t^2 <= tau(e_theta) s^4/m^2.
```

Summing over `theta` and then over the `N_K` types `sigma` of degree at most
`K`:

```text
mu_K(pi (x) rho) <= N_K K^4 / m^2.                                     (4)
```

If `rho` is reducible with constituents `rho_i` of degrees `m_i>=D`, then
`pi (x) rho` is the direct sum of the `pi (x) rho_i` with trace weights
`m_i/m`.  So `mu_K(pi (x) rho) <= sum_i (m_i/m) N_K K^4/m_i^2 <= N_K K^4/D^2`.
This is the second half of `(CET1)`.

## 3. Packet mass of a tensor product

Let `e=rho(|B|^-1 sum_(b in B) b)`, the projection onto `(C^m)^B`, with
`tr_m(e)=beta`.  Since `rho(b)e=e`,

```text
(pi (x) rho)(z)(1 (x) e) = sum_b z_b pi(b) (x) rho(b)e = pi(z) (x) e,
```

and `1 (x) e` commutes with `(pi (x) rho)(B)`.  So
`(pi (x) rho)(z) >= pi(z) (x) e`, and taking traces gives
`q(pi (x) rho) >= beta q(pi)`.  This is the first half of `(CET1)`.

If `M` embeds trace-preservingly in `R^omega`, then `M (x) M_m` embeds in
`M_m(R^omega) ≅ R^omega`, and `pi (x) rho` is a representation of `G`
because `rho` is.  The finite-dimensional case is immediate.

## 4. Placement implies collapse

Suppose `(CET2)` holds for a class `C` and some `pi in C` has `q(pi)=q>0`.
Put `q_0=beta q`.  By Section 3, `pi (x) rho_j in C` and
`q(pi (x) rho_j)>=q_0` for every `j`.  So
`f(q_0) <= mu_(K(q_0))(pi (x) rho_j) <= N_K K^4/D_j^2`.  Letting
`j->infinity` contradicts `f(q_0)>0`.

For `(CET3)`, `(BTM3)` of `commutant-density-forces-bounded-type-mass` gives
`g(q_0) <= mu_K^2 + 1/(K+1)^2`.  Choose `K` with `1/(K+1)^2 <= g(q_0)/2`.
Then every finite-dimensional `pi` with `q(pi)>=q_0` has
`mu_K(pi)>=sqrt(g(q_0)/2)`, and Section 4 applies.

## 5. The Toeplitz exits

In `toeplitz-unbounded-fixed-congruence-types-proof`,
`theta_q:T->F_q` kills `1+xy` and satisfies `theta_q o sigma=theta_q`.  So
`bar_theta_q:Gamma->SL_r(F_q)` is onto (the elementary matrices generate
`SL_r` over a field) and `rho_q=eta_q o bar_theta_q` is irreducible on
`Gamma`, of degree `N_q-1`, with `rho_q o alpha=rho_q`.  Setting `t |-> 1`
defines a representation of the ascending HNN group, and of every quotient
whose extra relators hold in these representations.

For finite `B<=Gamma`, the fixed space of `B` in the permutation
representation on the `N_q` projective points has dimension equal to the
number of `B`-orbits.  That is at least `N_q/|B|`.  Removing the trivial
summand,

```text
beta_q >= (N_q/|B| - 1)/(N_q - 1) >= 1/|B| - 1/(N_q-1),
```

which is at least `1/(2|B|)` for large `q`.  So `(CET-H)` holds and `(CET4)`
follows.

## 6. Remarks behind the consequences

`tau_can(z)=tau_B(z)>0` for the canonical trace of `G`.  So collapse on
Connes-embeddable representations makes `tau_can` non-embeddable, and `G`
is then not hyperlinear.

For finitely generated `G`, a finite-dimensional unitary image is a finitely
generated linear group, hence residually finite (Malcev).  Choose a finite
quotient injective on the image of `B`.  Its regular representation factors
through `G` and gives `q>0` whenever `pi(z) != 0`.  Conversely a finite
quotient with `z` nonzero in its group algebra gives a finite-dimensional
`q>0`.  So finite-dimensional collapse is the statement that `z` dies in
every finite quotient of `G`.
