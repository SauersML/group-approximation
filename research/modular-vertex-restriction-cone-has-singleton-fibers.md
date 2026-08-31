---
rg: 2
id: modular-vertex-restriction-cone-has-singleton-fibers
kind: claim
title: The modular-vertex endpoint cone has singleton fibers and contains every finite Plancherel window
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that proves equality of fixed-vector spaces and a uniform congruence conjugation gap; this upgrades finite-dimensional co-density to a full restriction-category and multiplicity-cone calculation.
  finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence: that classifies finite-dimensional endpoints as odd-congruence representations; this computes their restriction fibers over the modular vertex and locates the Plancherel ray.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that finds generally nontrivial fibers after restriction to the smaller BS/Iwahori core; this shows that restriction to the full modular vertex has no multiplicity-kernel direction at all.
---

Let `p` be prime and put

```text
A=SL_2(Z[1/p]),       C=SL_2(Z).                         (MVC1)
```

Let `Rep_cong^(p')(C)` be the finite-dimensional unitary
`C`-representations which factor through `SL_2(Z/m)` for some
`m` coprime to `p`. Restriction is an order equivalence

```text
Res_C^A:Rep_fd(A) -> Rep_cong^(p')(C).                   (MVC2)
```

More explicitly:

1. every object on the right has a unique extension to `A` up to unitary
   equivalence;
2. for any finite-dimensional `A`-representations `rho,sigma`,

   ```text
   Hom_A(rho,sigma)=Hom_C(rho restricted to C,
                          sigma restricted to C);        (MVC3)
   ```

3. at a fixed prime-to-`p` quotient
   `Q_m=SL_2(Z/m)`, label both sides by `Irr(Q_m)`. The restriction
   matrix is the identity. Hence the feasible endpoint multiplicity
   semigroup is the whole nonnegative orthant and every restriction fiber
   is a singleton, modulo harmless inflation to a common level.

After projectivizing by dimension, the closure of the normalized endpoint
rays is the full standard simplex

```text
theta_pi>=0,       sum_pi theta_pi=1,
theta_pi=M_pi dim(pi)/sum_rho M_rho dim(rho).           (MVC3a)
```

Every rational simplex point is realized by an integral multiplicity vector.

The Plancherel target is not merely in the closure of the feasible rays. At
every fixed level its multiplicity vector is the integral endpoint vector

```text
M_pi=dim(pi),       pi in Irr(Q_m),                      (MVC4)
```

whose normalized type weights are `dim(pi)^2/|Q_m|`.

There is also an explicit exact finite-window approximation at the infinite
modular vertex. For every finite `F subset C`, choose one nonzero entry
`a_g` of `g-I` for each `g in F minus {e}`, put

```text
P_F=product_(g in F minus {e}) |a_g|,
m_F=1+p P_F,                                             (MVC5)
```

with the empty product equal to one, and take
`Lambda_F=lambda_(SL_2(Z/m_F))` after reduction of `A`.

such that

```text
tr(Lambda_F(g))=delta_(g,e)       for every g in F.      (MVC6)
```

Consequently the regular character of `C` belongs to the pointwise
closure of normalized endpoint characters, and its projection to every
finite coordinate window is attained exactly. In particular there is no
finite-support Farkas functional separating the Plancherel target from the
endpoint character cone.

This completely removes representation-ring feasibility at the full
modular vertex. It does not solve Iwahori basin capture: character-window
attainment does not align a supplied matrix tuple, choose its moving
conductor, or control the smaller BS/Iwahori restriction fiber. The
nonhyperlinear-group root remains open.

DERIVATION
modular-vertex-restriction-cone-proof
