---
rg: 2
id: deligne-sector-siegel-spectrum-full-torus-proof
kind: route
title: Levi shears sweep irrational points, van der Corput sweeps unbounded torsion, and the finite branch hands a finite quotient to the Deligne residual
target: deligne-sector-siegel-spectrum-is-full-torus
requires: [deligne-multiplier-trivial-on-sl2xsl2-and-parabolics, higher-rank-lattice-normal-subgroups-central-or-finite-index, deligne-covers-of-sp2g-z-have-finite-residual-2z, deligne-maslov-sector-traces-are-central-regular]
artifacts:
  - research/artifacts/deligne-sector-siegel-spectrum-2026-09-17.md
---

Notation of the target.  `e(t) = exp(2 pi i t)`, `||t||` is the distance
to the nearest integer, and a point `(x,y,z)` of `T^3` is the character
`(a,b,c) -> e(xa + yb + zc)` of `U = Z^3`.

1. **Honest parabolic representation.**  By
   `deligne-multiplier-trivial-on-sl2xsl2-and-parabolics` there is a
   homomorphism `phi : p^-1(P_S(Z)) -> T` with `phi(z) = omega`.  Then
   `V(g) = conj(phi(g)) sigma(u_g)` is multiplicative and `V(z) = 1`, so `V`
   is a unitary representation of `P_S(Z)` in `B`.  `C^*(V(U))` is a quotient
   of `C^*(Z^3) = C(T^3)`, hence equals `C(Y)` for a closed `Y` in `T^3`.

2. **Levi invariance.**  `m(A) n(X) m(A)^-1 = n(A X A^T)`, so
   `Ad V(m(A))` restricts to an automorphism of `C(Y)` carrying the
   coordinate function of `X` to that of `A X A^T`.  So `Y` is invariant
   under the dual maps `chi -> chi o Ad m(A)`.  Two of them:
   - `A = [[1,k],[0,1]]` gives `(a,b,c) -> (a + 2kb + k^2 c, b + kc, c)`, whose
     dual is `T_k(x,y,z) = (x, y + 2kx, z + ky + k^2 x)`, for all `k in Z`;
   - `A = [[0,1],[1,0]]` swaps `a` and `c`; its dual is `S(x,y,z) = (z,y,x)`.

3. **Lemma A: a non-torsion point forces `Y = T^3`.**  Let `(x,y,z) in Y`.
   - *`x` irrational.*  For `(m,n) != (0,0)` the polynomial
     `2mkx + n(ky + k^2 x)` in `k` has an irrational non-constant coefficient
     (`nx` if `n != 0`, `2mx` if `n = 0`).  By Weyl's equidistribution theorem
     for polynomial sequences, `k -> (y + 2kx, z + ky + k^2 x)` is equidistributed
     in `T^2`.  So the closure of `{T_k(x,y,z)}` is `{x} x T^2`, inside `Y`.
   - *`x` rational, `z` irrational.*  Apply `S` and the previous case.
   - *`x`, `z` rational, `y` irrational.*  With `a = ord(x)`,
     `T_a(x,y,z) = (x, y, z + ay)`, and `z + ay` is irrational.  Use the
     previous case.
   - *Spreading.*  So `{x_0} x T^2` lies in `Y` for some irrational `x_0`.  For
     every irrational `t`, `(x_0, 0, t)` is in `Y`, so `S` gives `(t, 0, x_0)` in
     `Y`, and the first case gives `{t} x T^2` inside `Y`.  The union over
     irrational `t` is dense and `Y` is closed, so `Y = T^3`.

4. **Lemma B: torsion points of unbounded order force `Y = T^3`.**  Suppose
   `Y` meets `(Q/Z)^3` in points `p_s` whose orders tend to infinity.
   - *Reduction.*  Pass to a subsequence where `q_s = ord(x_s) -> infinity`.
     - If instead `ord(z_s)` is unbounded, replace `p_s` by `S p_s`.
     - If both `ord(x_s)` and `ord(z_s)` are at most `M_0` but `ord(y_s)` is
       unbounded, set `M = M_0!`.  The third coordinate of `T_M p_s` is
       `z_s + M y_s`, of order at least `ord(y_s)/(M M_0)`, which is unbounded.
       Then apply `S`.
   - *Averages.*  Put `K = q_s^2` and
     `nu_s = K^-1 sum_(0 <= k < K) delta_(y_s + 2k x_s, z_s + k y_s + k^2 x_s)`
     on `T^2`.  Its `(m,n)` Fourier coefficient has modulus `|S_s| / K`, where
     `S_s = sum_(k<K) e(f(k))` and `f(k) = 2mk x_s + n(k y_s + k^2 x_s)`.
   - *`n = 0`, `m != 0`.*  For `q_s > 2|m|`, `||2m x_s|| >= 1/q_s`, and the
     geometric sum gives `|S_s| <= 1/(2||2m x_s||) <= q_s/2`, so
     `|S_s|/K <= 1/(2 q_s)`.
   - *`n != 0`: the van der Corput identity.*  Expanding `|S_s|^2` gives
     `|S_s|^2 <= K + 2 sum_(h=1)^(K-1) |sum_(k < K-h) e(f(k+h) - f(k))|`,
     with `f(k+h) - f(k) = 2nh x_s k + c_h`.  So the inner sum is at most
     `min(K, 1/(2||2nh x_s||))`.
     - Split `1 <= h < K` into `q_s` blocks of `q_s` consecutive integers.
       With `x_s = a_s/q_s` in lowest terms and `g = gcd(2n, q_s) <= 2|n|`,
       `2nh x_s mod 1` runs over the multiples of `g/q_s`, each `g` times per
       block.
     - Each block contributes at most `gK` from the zero values and at most
       `g q_s (1 + log q_s)` from the others.
     - Hence `|S_s|^2 <= K + 2 q_s (gK + g q_s (1 + log q_s))`.  Dividing by
       `K^2 = q_s^4` gives `|S_s|^2/K^2 <= q_s^-2 + 2g/q_s + 2g(1 + log q_s)/q_s^2`,
       which tends to `0`.
   - *Limit.*  So `nu_s -> Haar(T^2)` weak*.  The measure
     `mu_s = delta_(x_s) (x) nu_s = K^-1 sum_k delta_(T_k p_s)` is supported in `Y`.
     Along a subsequence with `x_s -> x_inf`, `mu_s -> delta_(x_inf) (x) Haar`.
     `Y` is closed, so `{x_inf} x T^2` lies in `Y`.  This set contains
     non-torsion points, so Lemma A gives `Y = T^3`.

5. **Lemma C: the finite branch is empty.**  Otherwise, by Lemmas A and B, `Y`
   is a finite set of torsion points.
   - *Radical dies.*  Let `N` be the lcm of their orders.  For
     `X in Sym_2(Z)`, `V(n(NX)) = V(n(X))^N` has spectrum
     `{e(N(xa+yb+zc)) : (x,y,z) in Y} = {1}`, so it equals `1`.  Hence
     `sigma(u_g) = phi(g) 1` for every `g` in `p^-1(n(N Sym_2(Z)))`.
   - *Commutators die.*  For such `g` and any `h in E_3`,
     `sigma(u_([h,g])) = sigma(u_h) phi(g) sigma(u_h)^* conj(phi(g)) = 1`.  So
     `K = ker(h -> sigma(u_h))` is a normal subgroup of `E_3` whose image
     contains `[m(A), n(N E_22)] = n(N [[1,1],[1,0]])`, with `A = [[1,1],[0,1]]`.
     That element is not `+-I`.
   - *Finite index.*  By `higher-rank-lattice-normal-subgroups-central-or-finite-index`
     (`Sp_4(R)`, real rank 2), `p(K)` has finite index in `Gamma`.  Since
     `ker p` is finite, `K` has finite index in `E_3`.
   - *Contradiction.*  By `deligne-covers-of-sp2g-z-have-finite-residual-2z`,
     `z^2` lies in `K`, i.e. `sigma(u_(z^2)) = 1`.  But
     `sigma(u_(z^2)) = omega^2 1 != 1` because `B != 0`.
   - *Conclusion.*  So `Y = T^3`, which is (S1).

6. **(S2).**  If `g` lifts `n(X)` with `X = (a,b,c) != 0`, then
   `sigma(u_g) = phi(g) V(n(X))`.  The spectrum of `V(n(X))` is the image of
   `Y = T^3` under `(x,y,z) -> e(xa+yb+zc)`, which is `T`.  Conjugating in `E_3`
   and multiplying by central `z^j` (a scalar `omega^j`) preserve full
   circular spectrum.

7. **(S3).**  `tau o sigma` is a tracial state on `A_omega`.  By
   `deligne-maslov-sector-traces-are-central-regular` it vanishes on `u_g` for
   noncentral `g`.  A lift of `n(X)` with `X != 0` is noncentral, since
   `n(X) != +-I`.  So the measure on `Y = T^3` has Fourier coefficients
   `tau(V(n(X))) = conj(phi(g)) tau(sigma(u_g)) = 0` for `X != 0`, and total
   mass `1`.  It is Haar measure.  QED.
