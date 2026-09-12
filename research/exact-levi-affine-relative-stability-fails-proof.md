---
rg: 2
id: exact-levi-affine-relative-stability-fails-proof
kind: route
title: Mackey orbit count on the column spectrum forces the Weil block into the trivial orbit
target: exact-levi-affine-relative-stability-fails
requires: []
---

**Step 1 (the asymptotic representation).**  With `Z X = zeta X Z`,
`rho(v) rho(w) = X^(v_1) Z^(v_2) X^(w_1) Z^(w_2) = zeta^(v_2 w_1) rho(v + w)`,
and `(EL1)` gives `W_p(g) rho(v) = omega_g(v) rho(g v) W_p(g)`.  Hence for
`x = (v, g)`, `y = (w, h)` in `G`,

```text
phi_p(x) phi_p(y) = rho(v) W_p(g) rho(w) W_p(h)
                  = omega_g(w) rho(v) rho(g w) W_p(g h)
                  = omega_g(w) zeta^(v_2 (g w)_1) phi_p(xy),
```

a scalar `zeta^(N(x,y))` with `N(x, y)` an integer bounded by a quadratic
polynomial in the word lengths of `x, y` (the entries of `v, w, g` grow at
most exponentially in word length, but `N` is a fixed polynomial in those
entries; for `x, y` in a fixed ball the bound is independent of `p`).  So
`|| phi_p(x) phi_p(y) - phi_p(xy) ||_op = |zeta^N - 1| <= 2 pi |N| / p`,
which is `(EL2)`.  On the Levi, `phi_p(0, g) = W_p(g)` is a homomorphism
through `SL_2(Z) -> SL_2(F_p)`.  (For `p` odd the Weil representation of
`SL_2(F_p)` is linear, not merely projective, so no phase is hidden in the
Levi.)

**Step 2 (finite invariant column spectrum).**  Let `pi` be a unitary
representation of `G` on a finite-dimensional `H'`.  The commuting
unitaries `pi(e_1), pi(e_2)` have joint spectral projections `E_chi`,
`chi` in a finite subset `Sigma` of the dual torus `T^2`, and
`pi(g) E_chi pi(g)^(-1) = E_(g . chi)` for `g in SL_2(Z)` (equivariance of
the column).  So `Sigma` is a finite `SL_2(Z)`-invariant set.  A point
`chi = (e^(2 pi i a), e^(2 pi i b))` with `(a, b)` not rational has infinite
orbit under the two unipotents `(a, b) -> (a + n b, b)`, `(a, b) -> (a, b + n a)`;
hence every `chi in Sigma` is a torsion point, of some exact order `m_chi`.

**Step 3 (orbit decomposition).**  For an orbit `O subset Sigma` put
`H_O = (+)_(chi in O) E_chi H'`; it is `G`-invariant and `H' = (+)_O H_O`.
Fix `chi in O`, `H_chi = Stab_(SL_2(Z))(chi)`, and let `theta_chi` be the
representation of `H_chi` on `E_chi H'`.  The Levi permutes the summands
`E_(g chi) H'` transitively with stabilizer `H_chi`, so

```text
pi|_(SL_2(Z)) on H_O  =  Ind_(H_chi)^(SL_2(Z)) theta_chi,
dim H_O = |O| . dim theta_chi.                                        (EL5)
```

(This is the finite-dimensional Mackey decomposition for a semidirect
product by an abelian normal subgroup; it needs only that the spectral
projections are permuted.)  On the trivial orbit `O = {1}` the column acts
as the identity.

**Step 4 (orbit sizes).**  `SL_2(Z)` acts transitively on primitive vectors
of `(Z/m)^2`, so the orbit of a point of exact order `m >= 2` is the set of
all points of exact order `m`, of size

```text
Phi(m) = m^2 prod_(l | m) (1 - l^(-2)) >= 3,       Phi(m) >= p^2 - 1 if p | m.  (EL6)
```

(`Phi(2) = 3` is the minimum; for `p | m`, `Phi(m) >= Phi(p) (m/p)^2 >= p^2 - 1`.)

**Step 5 (the Weil constituents live in the trivial orbit).**  Suppose
`W^eps` (`eps = +` or `-`) is a constituent of `pi|_(SL_2(Z))` on `H_O` for a
nontrivial orbit `O` of order `m >= 2`.  By Frobenius reciprocity,
`Hom_(H_chi)(W^eps|_(H_chi), theta_chi) != 0`, so `theta_chi` contains an
irreducible constituent of `W^eps|_(H_chi)`.

*Case `gcd(m, p) = 1`.*  `H_chi` contains the principal congruence subgroup
`Gamma(m)` (it acts trivially on `m`-torsion), and `Gamma(m)` maps ONTO
`SL_2(F_p)` (surjectivity of `SL_2(Z) -> SL_2(Z/mp)` and the Chinese
remainder theorem).  Therefore `W^eps|_(Gamma(m))`, hence `W^eps|_(H_chi)`,
is still irreducible, `theta_chi` contains all of `W^eps|_(H_chi)`, and by
`(EL5), (EL6)`

```text
dim H_O >= |O| . dim W^eps >= 3 (p - 1) / 2.
```

*Case `p | m`.*  By `(EL6)`, `dim H_O >= |O| >= p^2 - 1`.

In both cases `dim H_O >= 3(p - 1)/2 > p + r = dim H'` as soon as
`r < (p - 3)/2`, which is `(EL3)` -- a contradiction.  Hence every copy of
`W^+` and of `W^-` in `pi|_(SL_2(Z))` lies in `H_(\{1\})`, where
`pi(Z^2) = 1`.

**Step 6 (conclusion).**  In block form `pi|_(SL_2(Z)) = W_p (+) sigma`, the
block `C^p` carries `W^+ (+) W^-` and is therefore contained in the
`W^+`- and `W^-`-isotypic subspaces, i.e. in `H_(\{1\})`.  So `pi(v)|_(C^p) = 1`
for all `v in Z^2`, which is (b).  Then

```text
|| pi(e_1) - (X (+) 1_r) ||_2^2
  >= (1/(p + r)) Tr_(C^p) |1 - X|^2
  =  (1/(p + r)) sum_(k=0)^(p-1) |1 - zeta^k|^2
  =  2p / (p + r),
```

which is `(EL4)`; the computation for `e_2` against `Z` is identical
(`Z` is unitarily conjugate to `X` by the Fourier transform `W_p(s)`).

**Step 7 (the stability statement).**  A relative exact-Levi modulus would
give, for each `p`, a genuine `pi` on `C^p (+) C^(r_p)` with
`r_p = o(p)`, Levi restriction `W_p (+) sigma_p`, and
`|| pi(e_1) - (X (+) 1) ||_2 <= f(2 pi q(1)/p) -> 0`.  For `p` large,
`r_p < (p-3)/2`, so `(EL4)` gives `|| pi(e_1) - (X (+) 1) ||_2 >= sqrt 2 - o(1)`,
a contradiction; this is (c).  The defect bound `(EL2)` is in operator
norm, so the same family refutes the operator-norm and Frobenius versions
of the exact-Levi relative statement as well.
