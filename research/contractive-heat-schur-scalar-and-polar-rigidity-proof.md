---
rg: 2
id: contractive-heat-schur-scalar-and-polar-rigidity-proof
kind: route
title: Retain coefficient heat mass and polar-round its irreducibly scalar Gram
target: irreducible-kazhdan-representations-have-uniform-hs-rigidity
requires:
  - kazhdan-approximate-coefficients-have-curved-hodge-control
artifacts:
  - research/artifacts/irreducible-kazhdan-local-hs-rigidity-2026-09-05.md
---

Let h=|S|, K0=|R|+4C_H for the required curved Hodge constants, and
choose eta0<=min(1/4,sqrt(mu/(4h))). Starting at I_d, the contractive
coefficient heat flow for T_s(A)=rho(s)A U_s* has initial normalized
mass one and energy at most h eta0^2. At time log(1/delta)/mu,
for sufficiently small positive delta, it gives an operator contraction
A with

```text
c=||A||_2^2>=1/2,
sum_s||rho(s)A-AU_s||_2^2<=B delta^2,
B=h eta0^2+K0/mu.
```

Put Q=AA*. The two-term product expansion and operator contractivity
give `||rho(s)Qrho(s)*-Q||_2<=2||rho(s)A-AU_s||_2`. Irreducibility
makes the invariant matrices of Ad(rho) scalar, so the Kazhdan bound
gives `||Q-cI||_2<=2sqrt(B)delta/kappa`. For T=A/sqrt(c), it follows
that `||TT*-I||_2<=4sqrt(B)delta/kappa`.

Complete the polar factor of the square T to a unitary V. Its singular
values satisfy |s-1|<=|s^2-1|, including s=0. Therefore

```text
||T-V||_2<=4sqrt(B)delta/kappa,
||rho(s)V-VU_s||_2
 <=sqrt(B)(sqrt(2)+8/kappa)delta.
```

Conjugating proves the desired correction at small positive defect,
with no padding. At delta=0, heat converges to a nonzero exact
intertwiner A_infinity, whose normalized squared mass is at least 3/4.
Schur's lemma gives A_infinity A_infinity*=cI with c>0; equal source
and target dimension make A_infinity/sqrt(c) unitary. Thus the
correction is exact in this case too.

Finally fix a uniform small-defect threshold delta_1 for the heat
argument. For delta>=delta_1, take V=I and bound the error by
eta0<=(eta0/delta_1)delta. Enlarging L proves the full basin statement.
The artifact records the heat thresholds and all normalizations. Its
Schur step is precisely why a reducible coarse comparison has a
different conclusion. Larger irreducible targets are treated below
with controlled padding.

For the fixed spectral basin, assume S symmetric and choose a
coefficient eigenvector A with eigenvalue lambda<=epsilon^2, normalized
by Tr(A*A)=d. Put H=A*A and X_s=A*rho(s)A. The symmetry formula for
Delta and the weighted inner product with AH give the exact identity

```text
lambda Tr(H^2)
 =(1/h)sum_s[Tr(H^2)-||X_s||HS^2+||X_s-HU_s||HS^2].
```

These traces and HS norms are unnormalized. The cross terms agree by
Re Tr(H X_s U_s*)=Re Tr(X_s* H U_s). Also the squared displacement
of Q=AA* under rho(s) is 2[Tr(H^2)-||X_s||HS^2]. Dropping the last
nonnegative squares and applying the Kazhdan bound to Ad(rho) yields

```text
Tr(H^2)-d <= (2h lambda/kappa^2)Tr(H^2).
```

Thus, for a=2h epsilon^2/kappa^2<1, the normalized Gram bound is
||H-I||_2^2<=a/(1-a). Polar completion to V0 costs at most
sqrt(a/(1-a)) in normalized HS norm. Since the total normalized edge
energy of A is h lambda, the orbit distance of U to rho is at most
xi(epsilon)=sqrt(h)epsilon+2sqrt(a/(1-a)). Choose a fixed epsilon_*
with xi(epsilon_*)<=eta0 and apply the already proved HS-basin result
to V0*rho V0. Its correction stays in rho's conjugacy class. Testing
Delta on a unitary realizing orbit distance e gives the converse
minimum-eigenvalue bound e^2. No finite-image hypothesis is used.

For the rectangular version with N>=d, normalize a low eigenvector
A:C^d->C^N by Tr(AA*)=N. The same weighted identity, now with the
Schur projection of AA* equal to I_N, gives

```text
Tr((A*A)^2)-N<=a Tr((A*A)^2),
||AA*-I_N||HS^2<=aN/(1-a),
N^2/d<=Tr((A*A)^2)<=N/(1-a).
```

Pad A with N-d zero columns and polar-complete it to a unitary on
C^N. Zero columns add no residual against U direct_sum I_(N-d).
The normalized Gram and edge bounds again give coarse orbit distance
at most xi(epsilon_*)<=eta0. The same-dimensional basin theorem now
produces sigma conjugate to rho with total unnormalized generator
error at most L delta(U)sqrt(d), since the padded defect is exactly
delta(U)sqrt(d/N).

If q=N-d>0, sigma has dimension at least two and is irreducible, so
left multiplication by sigma on the added q columns has no invariant
vector. Property (T) on their inclusion J_q gives
kappa sqrt(q)<=max_s||sigma(s)J_q-J_q||HS<=L delta(U)sqrt(d).
This proves the quadratic padding bound and rules out q>0 at zero
defect. The original d columns, carried back to rho by the conjugating
unitary, form an isometry with the same residual bound. Testing the
rectangular connection on this isometry gives minimum eigenvalue at
most L^2 delta(U)^2, completing `(IHR2)`.
