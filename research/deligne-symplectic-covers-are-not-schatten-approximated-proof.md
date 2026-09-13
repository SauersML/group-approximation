---
rg: 2
id: deligne-symplectic-covers-are-not-schatten-approximated-proof
kind: route
title: Descend Frobenius stability to the finite covers, round the mark to exact finite order, and apply Malcev
target: deligne-symplectic-covers-are-not-schatten-approximated
requires: [blsw-real-lattice-frobenius-stability, deligne-covers-of-sp2g-z-have-finite-residual-2z, finitely-generated-linear-groups-are-residually-finite]
---

Notation as in the target: `g >= 3`, `n >= 3`, `Gamma~` the preimage of
`Gamma = Sp_(2g)(Z)` in the universal cover, `Z = <z> = ker(Gamma~ -> Gamma)`,
`Gamma_n = Gamma~ / <z^n>`, `J = z^2` of order `m = n / gcd(n, 2)`.

**Step 1: stability (item 1).**
- `Sp(2g, R)` is simple with finite center and real rank `g >= 3`. By BLSW
  Theorem 2.10, `Gamma~` has `[T_2]`, so it is Frobenius stable by BLSW Theorem
  1.1(F). This is the first step of BLSW's own proof of Theorem 1.3.
- Apply BLSW Corollary 2.14 to `N = <z^n>`.
  - `Gamma~` is finitely generated.
  - `Gamma_n = Gamma~/N` is finitely presented: `Gamma` is finitely presented
    and the kernel `C_n` is finite.
  - `Sp_(2g)(Z)` has the congruence subgroup property (quoted in the BLSW
    citation). By BLSW Theorem 2.11, `PR(Gamma~) = kZ` for some `k >= 1`.
  - Then `N cap PR(Gamma~) = lcm(n, k) Z` has finite index in `N = nZ`.
- So `Gamma_n` is Frobenius stable.

**Step 2: the mark is invisible.**
- By `deligne-covers-of-sp2g-z-have-finite-residual-2z`, `J` lies in the finite
  residual of `Gamma_n`.
- Every homomorphism `rho : Gamma_n -> U(d)` has finitely generated linear
  image, which is residually finite by Malcev. If `rho(J) != 1`, some finite
  quotient of `rho(Gamma_n)` separates `rho(J)` from `1`, and that is a finite
  quotient of `Gamma_n` not killing `J`, which is impossible. So `rho(J) = 1`.

**Step 3: rounding to exact order `m`.** Let `A` be unitary. Let `B = f(A)`,
where `f` sends each eigenvalue to a nearest `m`-th root of unity, with one fixed
choice on ties. Then `B^m = 1` and `B` commutes with `A`.
- Write an eigenvalue as `lambda = xi e^(ix)`, with `xi^m = 1` and `|x| <= pi/m`.
- Then `|lambda - xi| = 2|sin(x/2)|` and `|1 - lambda^m| = 2|sin(mx/2)|`.
- With `u = m|x|/2 <= pi/2`, concavity gives `sin(u) >= 2u/pi`. Hence
  `|1 - lambda^m| >= (2m/pi) |lambda - xi|` and `|lambda - f(lambda)| <= |1 - lambda^m|`.
- `A - B` and `1 - A^m` are simultaneously diagonal, so their singular values
  compare entrywise. Therefore

  ```text
  ||A - f(A)||_p <= ||1 - A^m||_p        for every p.                    (R1)
  ```

**Step 4: collapse (item 2).** Let `1 <= p <= 2` and let `phi_k` be a
`||.||_p`-asymptotic homomorphism. Suppose, after passing to a subsequence,
`||phi_k(J) - 1||_p >= c > 0`.
1. By unitary invariance, `||phi_k(1) - 1||_p = ||phi_k(1)^2 - phi_k(1)||_p`,
   which tends to 0.
2. Telescoping over `J^m = 1` gives `||phi_k(J)^m - 1||_p -> 0`. Each step is
   `||phi(J) phi(J^j) - phi(J^(j+1))||_p`, up to unitary factors.
3. Put `U_k = f(phi_k(J))`. By `(R1)`, `||U_k - phi_k(J)||_p -> 0`, so
   eventually `||U_k - 1||_p >= c/2`. In particular `U_k != 1`.
4. So `U_k` has an eigenvalue `xi != 1` with `xi^m = 1`, and
   `||U_k - 1||_2 >= |xi - 1| >= 2 sin(pi/m)`.
5. Schatten norms decrease in `p`, so `||X||_2 <= ||X||_p` for `p <= 2`.
   - Hence `phi_k` is also a Frobenius asymptotic homomorphism.
   - Also `||phi_k(J) - 1||_2 >= 2 sin(pi/m) - ||U_k - phi_k(J)||_p`, which is
     at least `sin(pi/m)` eventually.
6. By Step 1 there are genuine `rho_k` with `||rho_k(J) - phi_k(J)||_2 -> 0`. So
   `rho_k(J) != 1` eventually, contradicting Step 2.

Hence `||phi_k(J) - 1||_p -> 0`, and no `||.||_p`-asymptotic homomorphism
separates `J`. For odd `n`, `m = n` and `J` generates `C_n`, which gives the
statement about `z`.

**Step 5: the sector gap (item 3).**
- The group is finitely presented and Frobenius stable. So the uniform form of
  stability applies (the BLSW introduction, quoted in its citation): for every
  `epsilon > 0` there is `delta > 0` such that, for all `d`, every map
  `rho : S cup {z} -> U(d)` with all relator defects `||rho(r) - I||_2 < delta`
  has a genuine homomorphism `rho~` with `||rho~(s) - rho(s)||_2 < epsilon` on
  `S cup {z}`.
- Take `epsilon = sin(pi/m)/2` and put `delta_n = delta`.
- Suppose `rho(z) = zeta I` with `zeta^n = 1`, `zeta^2 != 1`, and all relator
  defects below `delta_n`.
- Step 2 gives `rho~(J) = rho~(z)^2 = 1`.
- For unitaries, `||X^2 - Y^2||_2 <= 2||X - Y||_2`. Hence
  `|1 - zeta^2| d^(1/2) = ||rho~(z)^2 - zeta^2 I||_2 < 2 epsilon = sin(pi/m)`.
- `zeta^2` is a nontrivial `m`-th root of unity, so `|1 - zeta^2| >= 2 sin(pi/m)`.
  With `d >= 1` this is a contradiction.
- So some relator has `||rho(r) - I||_2 >= delta_n`. Dividing by `d^(1/2)` gives
  the normalized form of `(SG1)`.

**Scope.** Only Step 1 uses `g >= 3`. Steps 2--5 hold for any finitely presented
group with a central finite-order element in its finite residual, provided the
group is Frobenius stable.
