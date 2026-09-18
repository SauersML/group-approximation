---
rg: 2
id: fpbs-rotation-boundary-class-refutes-shadow-summability-proof
kind: route
title: An irrational-rotation code with the inversion symmetry s(-x) = -s(x) makes every level of the shadow sum at least a continuous autocorrelation over 4m, so it diverges under every reweighting; the joint returns of a pair force theta' in plus-or-minus theta + Z alpha, so they are a.e. finite
target: fpbs-rotation-boundary-class-refutes-shadow-summability
requires:
  - fpbs-dini-boundary-class-diagonal-dissipative
  - fpbs-dini-singular-boundary-classes-exist-but-one-way-die
---

Full written proof. Notation is as in `fpbs-dini-boundary-class-diagonal-dissipative` and its proof: thin shadows
`O_s(g)`, shadow sums `S_s`, the return masses `a_W(g)`, and the inputs (I1)--(I4). `|E|` denotes Lebesgue measure on
`T = R/Z`, and `||x||` the distance from `x` to `Z`.

## Imported inputs

- **(S) Schottky subgroups and Morse stability.** A nonelementary hyperbolic `Gamma` contains a free subgroup
  `F = <a,b>` of rank 2 whose orbit map `F -> Gamma` is a quasi-isometric embedding of the Cayley tree of `F` (ping-pong
  with large powers of two independent loxodromics). There is then an `F`-equivariant homeomorphism `iota` from `dF`
  onto the limit set `Lambda_F`, and a constant `H` such that the image of every tree ray from `e` is within Hausdorff
  distance `H` of a geodesic ray from `o` with the same endpoint. This is input (S) of
  `fpbs-dini-singular-boundary-classes-exist-but-one-way-die-proof`.
- **(W) Weyl.** For irrational `beta`, the sequence `r beta mod 1` is equidistributed.
- **(M), (LI).** Used only in Section 6, the extension of Theorem 3 to general `Gamma`. **(M)** Every torsion-free
  nonelementary hyperbolic group contains a malnormal quasiconvex free subgroup of rank 2 (I. Kapovich, *A
  non-quasiconvexity embedding theorem for hyperbolic groups*, Math. Proc. Cambridge Philos. Soc. 127 (1999)).
  **(LI)** For quasiconvex subgroups `H`, `K` of a hyperbolic group, `Lambda(H) ∩ Lambda(K) = Lambda(H ∩ K)` (the
  limit-set intersection property; e.g. Gitik--Mitra--Rips--Sageev, Trans. AMS 350 (1998), and Swarup). Both are
  quoted, not reproved.

## 1. The rotation code

Fix an irrational `alpha`. Put:
- `s(x) = +1` for `x` in `[0,1/2)` and `s(x) = -1` for `x` in `[1/2,1)`;
- `t_n = a` for odd `n` and `t_n = b` for even `n`.

Let `Omega = T x Z/2` carry `P = Leb x (uniform)`. For `omega = (theta, j)`, put
`zeta_n(omega) = t_{n+j}^{s(theta + n alpha)}` for `n` in `Z`, and let `zeta^+(omega)` be the ray `zeta_1 zeta_2 ...`.

The shift `sigma(theta, j) = (theta + alpha, j + 1)` preserves `P`. It is ergodic: an eigenvalue of the `Z/2` factor is
`±1`, and `e^{2 pi i k alpha} = -1` would force `alpha` rational. And `zeta_{n+1}(omega) = zeta_n(sigma omega)`.

Let `Omega_0` be the set of `(theta, j)` with `theta + n alpha` not in `{0, 1/2}` for all `n` in `Z`. It is conull and
`sigma`-invariant. Put `mu = zeta^+_* P`.

**Lemma 1.1 (basic properties).**
1. Every `zeta^+(omega)` is reduced: consecutive letters are one `a^{±1}` and one `b^{±1}`.
2. On `Omega_0`, `zeta^+` is injective.
3. On `Omega_0`, no ray `zeta^+(omega)` is eventually periodic.
4. **Tail rigidity.** If `omega, omega'` are in `Omega_0` and `sigma^p zeta^+(omega) = sigma^q zeta^+(omega')` for
   some `p, q >= 0` (as rays), then `sigma^p omega = sigma^q omega'`.
5. `mu` is nonatomic.

*Proof.*
1. Clear.
2. The type of `zeta_1` determines `j`. Take `theta != theta'` with `||theta - theta'|| < 1/2`. The set
   `{-n alpha : n >= 1}` is dense, so some `-n alpha` lies in the short open arc between them. That arc has length less
   than `1/2`, so it does not contain the other discontinuity `1/2 - n alpha` of `x -> s(x + n alpha)`. Hence
   `s(theta + n alpha) != s(theta' + n alpha)`.

   If `||theta - theta'|| = 1/2`, then `s(theta + alpha) = -s(theta' + alpha)`, so the rays again differ.
3. Suppose `zeta^+(omega)` is eventually periodic with period `p`. Then `zeta^+(sigma^N omega) = zeta^+(sigma^{N+p} omega)`,
   so `theta + N alpha = theta + (N+p) alpha` by (2), which forces `p alpha` in `Z`. This is impossible.
4. `sigma^p zeta^+(omega) = zeta^+(sigma^p omega)`, and similarly for `omega'`. Apply (2).
5. Follows from (2). ∎

**Lemma 1.2 (inversion identity).** For `omega = (theta, j)` in `Omega_0` and `m >= 1`, put
`tau_m(theta, j) = (-theta - (m+1) alpha, j + m + 1)`. Then

`(zeta_1 ... zeta_m (omega))^{-1} = zeta_1 ... zeta_m (tau_m omega)`.

Moreover `tau_m` is a `P`-preserving involution of `Omega_0`.

*Proof.* The `k`-th letter of the left side is
`zeta_{m+1-k}(omega)^{-1} = t_{m+1-k+j}^{-s(theta + (m+1-k) alpha)}`.

The `k`-th letter of the right side is `t_{k+j+m+1}^{s(-theta - (m+1-k) alpha)}`.
- The indices `m+1-k+j` and `k+j+m+1` differ by `2k`, so the letter types agree.
- The exponents agree because `s(-x) = -s(x)` for `x` not in `{0, 1/2}`.

The map `tau_m` is an involution because `-(-theta - (m+1) alpha) - (m+1) alpha = theta`, and `j + 2(m+1) = j`. It
preserves `P` since reflection and translation preserve Lebesgue measure. ∎

**Cells.** For `m >= 1` and a reduced word `w` of length `m`, put `C_w = {omega in Omega_0 : zeta_1..zeta_m(omega) = w}`,
so that `mu[w] = P(C_w)`. For fixed `j`, the function `theta -> zeta_1..zeta_m(theta, j)` is constant on each arc of
the partition of `T` by the at most `2m` points `{-n alpha, 1/2 - n alpha : 1 <= n <= m}`. So at most `4m` of the
`C_w` are nonempty, and they partition `Omega_0`. By Lemma 1.2, `tau_m(C_w) = C_{w^{-1}}`, hence
`mu[w^{-1}] = mu[w]`.

## 2. The rotation class

Let `Gamma` be nonelementary hyperbolic, and let `F`, `iota`, `H` be as in (S). For `Gamma = F_2` take `F = Gamma`
and `iota = id`. Put `B = zeta^+(Omega_0)`, the set of rotation rays, and `nu = sum_{g in Gamma} c_g g_* iota_* mu`
with all `c_g > 0` and `sum c_g = 1`.

**Lemma 2.1.** `nu` is `Gamma`-quasi-invariant, ergodic and nonatomic.

*Proof.*
- *Quasi-invariance.* `h_* nu = sum_g c_g (hg)_* iota_* mu` has the same null sets as `nu`, since all `c_g > 0`.
- *Nonatomic.* This follows from Lemma 1.1(5), because `iota` is injective.
- *Ergodicity.* Let `E` be `Gamma`-invariant. Then `nu(E) = sum_g c_g iota_* mu(g^{-1} E) = mu(iota^{-1} E)`. The set
  `iota^{-1} E` is `F`-invariant. Since `zeta^+(sigma omega) = zeta_1(omega)^{-1} zeta^+(omega)`, the function
  `1_{iota^{-1}E} ∘ zeta^+` is `sigma`-invariant. By ergodicity of `sigma`, it is `P`-a.e. constant. So
  `nu(E) ∈ {0, 1}`. ∎

## 3. Theorem 1: no measure in the class is shadow-summable

**Lemma 3.1 (shadow comparison).** Put `s_0 = H + 2 delta`. For `g ∈ F` and `zeta ∈ [g]_F` (the cylinder of rays in
the tree of `F` through `g`), `iota(zeta) ∈ O_{s_0}(g)`. For `Gamma = F_2` with its free generators, `O_0(g) = [g]`.

*Proof.*
- The tree ray from `e` to `zeta` passes through `g`, so its image passes through `g o`.
- By (S), some geodesic ray `rho` from `o` to `iota(zeta)` has a point `rho(t)` with `d(go, rho(t)) <= H`. Then
  `t >= |g| - H`.
- For `t' >= t`, `d(go, rho(t')) <= H + t' - t`. So
  `(go | rho(t'))_o >= (|g| + t' - H - t' + t)/2 >= |g| - H`.
- Passing to the boundary loses at most `2 delta` (I1). So `(go | iota(zeta))_o >= |g| - H - 2 delta`, which is at
  least `|g| - s_0 - 2 delta`.

In the tree, `(g | zeta)_e >= |g|` holds exactly when `zeta ∈ [g]`. ∎

**Theorem 1.** Let `A` be a Borel subset of `dF` with `mu(A) > 0`. Then
`sum_{g in F} mu(A ∩ [g]) mu(A ∩ [g^{-1}]) = infinity`. Consequently:
- `S_s(lambda) = infinity` for every `s >= s_0` and every finite `lambda >= c iota_*(mu|_A)` with `c > 0`;
- every finite measure `lambda` in the class of `nu` is of this form, so none is shadow-summable.

*Proof.*

*Step 1: reduction to the displayed sum.* Suppose `lambda ~ nu`. Since `iota_* mu << nu`, the density of the
absolutely continuous part of `lambda` with respect to `iota_* mu` is positive `iota_* mu`-a.e. Hence some `c > 0`
makes `A = iota^{-1}{density >= c}` of positive `mu`-measure, and `lambda >= c iota_*(mu|_A)`. By Lemma 3.1 and
injectivity of `iota`, `lambda(O_s(g)) >= c mu(A ∩ [g])` for `g ∈ F` and `s >= s_0`. The same holds for `g^{-1}`.
Summing over `g ∈ F`, which is a subset of `Gamma`, gives `S_s(lambda) >= c^2 sum_{g in F} mu(A ∩ [g]) mu(A ∩ [g^{-1}])`.

*Step 2: one level.* Put `Ã = (zeta^+)^{-1}(A) ∩ Omega_0`, and fix `m >= 1`.
- `mu(A ∩ [w]) = P(Ã ∩ C_w)`.
- By Lemma 1.2, `mu(A ∩ [w^{-1}]) = P(Ã ∩ tau_m C_w) = P(tau_m Ã ∩ C_w)`.

Since `P(Ã ∩ C_w) >= P(Ã ∩ tau_m Ã ∩ C_w)` and likewise for the other factor, Cauchy--Schwarz over the at most `4m`
nonempty cells gives

`L_m(A) := sum_{|w| = m} mu(A ∩ [w]) mu(A ∩ [w^{-1}]) >= sum_w P(Ã ∩ tau_m Ã ∩ C_w)^2 >= P(Ã ∩ tau_m Ã)^2 / (4m)`.

*Step 3: the autocorrelation.* Write `Ã = ∪_j Ã_j x {j}`. For odd `m`, `tau_m(theta, j) = (-theta - (m+1) alpha, j)`,
so `P(Ã ∩ tau_m Ã) = (1/2) sum_j f_j(-(m+1) alpha)`. Here `f_j(t) = |Ã_j ∩ (t - Ã_j)| = (1_{Ã_j} * 1_{Ã_j})(t)`.

Each `f_j` is continuous, as the convolution of two `L^2` functions, and `int f_j = |Ã_j|^2`. Fix `j` with
`|Ã_j| > 0`. Then `f_j >= delta > 0` on some open arc `J`.

*Step 4: equidistribution.* For `m = 2r - 1`, the level satisfies `L_m(A) >= delta^2 / (16 m)` whenever
`-2r alpha mod 1 ∈ J`. By (W) with `beta = 2 alpha`, the set `R` of such `r` has density `|J|`. Summation by parts gives
`sum_{r in R, r <= N} 1/r >= (|J|/2) log N - O(1)`, so `sum_m L_m(A) = infinity`. ∎

**Remark 3.2 (the unrestricted level sum).** For `A = dF` the bound is sharper: `mu[w^{-1}] = mu[w]`, so
`L_m = sum_{|w| = m} mu[w]^2 >= 1/(4m)` at **every** level. The script finds `sum_{k <= m} L_k ≈ 0.32 log m`.

## 4. Theorem 2: an invariant measure, and the sharp sum diverges (`Gamma = F_2`)

In this section and the next, `Gamma = F = F_2`. For `omega ∈ Omega_0` and `k ∈ Z`, let `gamma_k(omega) ∈ F` be:
- `(zeta_1 ... zeta_k(omega))^{-1}` if `k >= 0`;
- `zeta_{k+1} ... zeta_0(omega)` if `k < 0`.

These are reduced words of length `|k|`, and `gamma_k(omega) zeta^+(omega) = zeta^+(sigma^k omega)`.

**Lemma 4.1 (orbits through rotation rays).** Let `omega ∈ Omega_0` and `gamma ∈ F`. Then `gamma zeta^+(omega) ∈ B`
if and only if `gamma = gamma_k(omega)` for some `k`, and that `k` is unique.

*Proof.*
- If `gamma zeta^+(omega) = zeta^+(omega')`, then the two rays are tail-equivalent up to shift, since
  `F_2`-orbits on `dF_2` are the shift-tail classes. So `sigma^p zeta^+(omega) = sigma^q zeta^+(omega')`, and
  Lemma 1.1(4) gives `omega' = sigma^k omega` with `k = p - q`.
- Then `gamma^{-1} gamma_k(omega)` fixes `zeta^+(omega)`. A nontrivial element of `F_2` fixes only its two eventually
  periodic endpoints, and Lemma 1.1(3) says `zeta^+(omega)` is not eventually periodic. So
  `gamma = gamma_k(omega)`.
- Uniqueness holds because `|gamma_k| = |k|` and `gamma_{-k} != gamma_k` for `k != 0`: the letter types differ. ∎

**The invariant measure.** On `Y = F x Omega_0`, with counting times `P`, let
`T(g, omega) = (g zeta_1(omega), sigma omega)`.
- `T` is a measure-preserving bijection. For fixed `omega`, `g -> g zeta_1(omega)` is a bijection of `F`, and `sigma`
  preserves `P`.
- `T` commutes with the left action of `F`.
- The map `pi(g, omega) = g zeta^+(omega)` satisfies `pi ∘ T = pi`.

By Lemma 4.1 and the triviality of stabilizers, the fibres of `pi` are exactly the `T`-orbits. Here
`T^k(g, omega) = (g gamma_k(omega)^{-1}, sigma^k omega)`. Along an orbit, `|g gamma_k^{-1}| >= |k| - |g|`, which tends
to infinity. Let `D` consist of the points of `Y` whose first coordinate has minimal length in its orbit, and that come
first in the `Z`-order of the orbit among such points. Then `D` is a Borel fundamental domain.

Put `m_infinity(E) = (count x P)(pi^{-1}(E) ∩ D)`.

**Lemma 4.2.**
1. `m_infinity` is `F`-invariant, sigma-finite and equivalent to `nu`.
2. `m_infinity|_B = mu`, so `m_infinity(B) = 1`.
3. The action `(dF_2, m_infinity)` is ergodic, conservative and amenable.

*Proof.*
1. *Invariance.* For a `T`-invariant set `S`, the value `(count x P)(S ∩ D')` does not depend on the fundamental domain
   `D'`, since `D' = ⊔_k T^k(D ∩ T^{-k} D')` and `T` preserves measure. Then
   `m_infinity(hE) = (count x P)(pi^{-1}E ∩ h^{-1} D)`, and `h^{-1} D` is another fundamental domain.

   *Sigma-finiteness and equivalence.* Since `D ⊂ Y`, `m_infinity <= sum_g g_* mu`. A `T`-invariant set of positive
   measure meets `D` in positive measure, so `m_infinity ~ sum_g c_g g_* mu = nu`.
2. `{e} x Omega_0` meets every `T`-orbit at most once, because `gamma_k != e` for `k != 0`. Also `pi^{-1}(E)` lies in
   the `T`-saturation of `{e} x Omega_0` when `E ⊂ B`. So `m_infinity(E) = P((zeta^+)^{-1} E) = mu(E)`.
3. *Ergodicity* follows from Lemma 2.1. *Conservativity:* every point `zeta^+(omega)` of `B` returns to `B` under the
   distinct elements `gamma_k(omega)`, `k >= 0`, and `F B` is conull. *Amenability:* every action of a free group on
   its boundary is amenable for every quasi-invariant measure (Adams, *Boundary amenability for word hyperbolic
   groups*, Topology 33 (1994)). ∎

**Theorem 2.** Put `U = [a] ∪ [a^{-1}]` and `V = [b] ∪ [b^{-1}]` (disjoint clopen sets), `B_W = B ∩ W`, and
`a_W(g) = m_infinity(B_W ∩ g^{-1} B_W)`. Then `sum_g a_U(g) a_V(g) = infinity`.

*Proof.*

*Setup.* By Tonelli, the sum equals `int_{B_U x B_V} #{g : g z ∈ B_U, g z' ∈ B_V} d(m_infinity x m_infinity)`. Here
`B_U = zeta^+(Omega_0 ∩ {j = 0})` and `B_V = zeta^+(Omega_0 ∩ {j = 1})`, each of measure `1/2`. Take
`z = zeta^+(theta, 0)`, `z' = zeta^+(theta', 1)`, an even `k >= 2`, and `g = gamma_k(theta, 0) = W_k^{-1}`, where
`W_k = zeta_1..zeta_k(theta, 0)`.

*First coordinate.* `g z = zeta^+(theta + k alpha, 0)` lies in `B_U`.

*Second coordinate.* `g z' = W_k^{-1} zeta^+(theta', 1)`. There is no cancellation: `W_k^{-1}` ends in an
`a`-letter and `z'` begins with a `b`-letter.
- By Lemma 1.2, `W_k^{-1} = zeta_1..zeta_k(-theta - (k+1) alpha, 1)`.
- The ray `zeta^+(theta' - k alpha, 1)` consists of `zeta_1..zeta_k(theta' - k alpha, 1)` followed by
  `zeta^+(theta', 1)`.
- Comparing exponents, `g z' = zeta^+(theta' - k alpha, 1) ∈ B` as soon as
  `s(theta' - i alpha) = s(psi - i alpha)` for `0 <= i <= k-1`, where `psi = -theta - alpha`.
- `g z'` begins with `zeta_k(theta, 0)^{-1}`, a `b`-letter, so it lies in `V`.

Call this condition `theta' ~_k psi`. It says that `theta'` and `psi` lie in one cell of the partition `Q_k` of `T`
by the at most `2k` points `{i alpha, 1/2 + i alpha : 0 <= i < k}`.

*The count.* Distinct `k` give distinct `g`. Since `theta -> psi` preserves Lebesgue measure, Cauchy--Schwarz gives
`int int 1[theta' ~_k psi(theta)] d theta d theta' = sum_{Q in Q_k} |Q|^2 >= 1/(2k)`. Hence

`sum_g a_U(g) a_V(g) >= (1/4) sum_{k even, k >= 2} 1/(2k) = infinity`. ∎

So the sharp first-moment sum of Remark 3 of the Dini proof diverges on a class that contains an invariant
measure. Here the Maharam extension is a trivial product, so the imp action itself is the natural test object.

## 5. Theorem 3: pointwise match rigidity (`Gamma = F_2`)

The divergence in Theorem 2 comes from the *expected* number of joint returns. Each individual pair still returns only
finitely often. The reason is that infinitely many joint returns pin down an algebraic relation between the two
rotation parameters.

**Right-end readings.** For `omega ∈ Omega_0`, `k != 0` and `0 <= r < |k|`, let `R_k(omega)(r)` be the letter of
`gamma_k(omega)` at distance `r` from its right end (position `|k| - r`). From the definition of `gamma_k`:
- `R_k(omega)(r) = zeta_{r+1}(omega)^{-1}` for `k > 0`;
- `R_k(omega)(r) = zeta_{-r}(omega)` for `k < 0`.

So the right end of `gamma_k(omega)` always sits at index `0` of the bi-infinite word of `omega`. The reading depends on
`k` only through its sign.

**Lemma 5.1 (two-sided injectivity).** Let `X, X' ∈ T` satisfy `X - t alpha, X' - t alpha ∉ {0, 1/2}` for all `t >= 0`. If
`s(X - t alpha) = s(X' - t alpha)` for all `t >= 0`, then `X = X'`. The same holds with `X + t alpha`, `X' + t alpha`
for `t >= 0`.

*Proof.* The discontinuities of `x -> s(x - t alpha)` are `t alpha` and `1/2 + t alpha`.
- Suppose `0 < ||X - X'|| < 1/2`. The set `{t alpha : t >= 0}` is dense, so some `t alpha` lies in the short open arc
  between `X` and `X'`. That arc has length less than `1/2`, so it does not contain `1/2 + t alpha`. Then
  `s(X - t alpha) != s(X' - t alpha)`.
- If `||X - X'|| = 1/2`, then already `s(X) = -s(X')`.

The second version follows in the same way from the density of `{-t alpha : t >= 0}`. ∎

**Proposition 5.2 (rigidity).** Let `omega = (theta, j)` and `omega' = (theta', j')` be in `Omega_0` with
`theta' ∉ (theta + Z alpha) ∪ (-theta + Z alpha)`. Then for all `x, y ∈ F`, the set of pairs `(k, k') ∈ Z^2` with

`gamma_k(omega) = x gamma_{k'}(omega') y` (as elements of `F`)

is finite.

*Proof.* Suppose the set is infinite, and put `c = |x| + |y|`.

*Lengths.* `|gamma_k| = |k|` and `|gamma_{k'}| = |k'|`, so `| |k| - |k'| | <= c` for every solution. For each `k'`
there are at most `2c + 1` values of `k`. So along the solutions `|k'| -> infinity`, and hence `|k| -> infinity`.

*Bounded cancellation.* Let `W = gamma_{k'}(omega')`, a reduced word of length `L = |k'| > c`.
- Write `x = x_1 x_2`, where `x_2` is the longest suffix of `x` that cancels against a prefix of `W`. Put
  `p = |x_2| <= |x|`.
- Write `y = y_2 y_1`, where `y_2` is the longest prefix of `y` that cancels against a suffix of `W`. Put
  `q = |y_2| <= |y|` and `e = |y_1|`.
- Since `L > p + q`, the two cancellations do not interact. The reduced form of `x W y` is
  `x_1 W[p+1 .. L-q] y_1`.

Reading this word from the right end and comparing with `gamma_k(omega)` gives

`R_k(omega)(e + t) = R_{k'}(omega')(q + t)` for `0 <= t <= L - p - q - 1`. (5.1)

*Passing to a subsequence.* The data `(sign k, sign k', q, e)` take finitely many values. Pass to infinitely many
solutions on which they are constant. Along these, `L - p - q - 1 >= |k'| - c - 1 -> infinity`, and (5.1) does not
depend on the solution except through its range of `t`. So (5.1) holds for **all** `t >= 0`.

*Four cases.* Recall `zeta_n(theta, j) = t_{n+j}^{s(theta + n alpha)}`. Only the exponents are needed, and every
argument of `s` below avoids `{0, 1/2}` because `omega, omega' ∈ Omega_0` and `s(-x) = -s(x)` there.
1. `k, k' > 0`. Then `zeta_{e+t+1}(omega) = zeta_{q+t+1}(omega')` for all `t >= 0`, so
   `sigma^e zeta^+(omega) = sigma^q zeta^+(omega')`. Lemma 1.1(4) gives `theta + e alpha = theta' + q alpha`.
   So `theta' ∈ theta + Z alpha`.
2. `k, k' < 0`. Then `s(theta - (e+t) alpha) = s(theta' - (q+t) alpha)` for all `t >= 0`. Lemma 5.1 with
   `X = theta - e alpha` and `X' = theta' - q alpha` gives `theta' ∈ theta + Z alpha`.
3. `k > 0 > k'`. Then `zeta_{e+t+1}(omega)^{-1} = zeta_{-q-t}(omega')`, so
   `-s(theta + (e+t+1) alpha) = s(theta' - (q+t) alpha)`. By `s(-x) = -s(x)`, the left side is
   `s(-theta - (e+1) alpha - t alpha)`. Lemma 5.1 with `X = -theta - (e+1) alpha` and `X' = theta' - q alpha` gives
   `theta' = -theta - (e + 1 - q) alpha ∈ -theta + Z alpha`.
4. `k < 0 < k'`. Then `zeta_{-e-t}(omega) = zeta_{q+t+1}(omega')^{-1}`, so
   `s(theta - (e+t) alpha) = s(-theta' - (q+1) alpha - t alpha)`. Lemma 5.1 gives `theta = -theta' - (q+1-e) alpha`,
   so `theta' ∈ -theta + Z alpha`.

Every case contradicts the hypothesis. ∎

The proof uses one solution per value of `t`. So it gives a quantitative version: a solution with `|k'| > N + c + 1`
forces `s(X - t alpha) = s(X' - t alpha)` for `t < N`. Then the short arc between `X` and `X'` contains no point
`t alpha` with `t < N`, so `||X - X'||` is at most the largest gap of `{t alpha : t < N}`. That gap is `O(1/N)` for
badly approximable `alpha`. This is the source of the bound
`count * ||x - y|| <= 1.03` in the script.

**The null set.** Put `Bad = {(omega, omega') ∈ Omega_0^2 : theta' ∈ (theta + Z alpha) ∪ (-theta + Z alpha)}`. For
each `theta` its section is countable, so `(P x P)(Bad) = 0` by Fubini. Put

`N = (dF x dF minus FB x FB) ∪ ⋃_{h, h' ∈ F} (h x h')(zeta^+ x zeta^+)(Bad)`.

This is Borel, since `zeta^+` is injective and Borel on `Omega_0` (Lusin--Souslin).

**Lemma 5.3.** `(nu x nu)(N) = 0`.

*Proof.* `nu` gives `FB` full measure, so it suffices to show `(g_* mu x g'_* mu)((h x h')(zeta^+ x zeta^+)(Bad)) = 0`
for all `g, g', h, h' ∈ F`. Equivalently, `(mu x mu)` of the set `(g^{-1} h x g'^{-1} h')(zeta^+ x zeta^+)(Bad)`
intersected with `B x B` vanishes.
- Take a point `(zeta^+(omega_1), zeta^+(omega_2))` of this set, with preimage `(omega, omega') ∈ Bad`.
- By Lemma 4.1, `omega_1 = sigma^k omega` and `omega_2 = sigma^{k'} omega'` for some `k, k'`.
- The relation defining `Bad` is invariant under `theta -> theta + k alpha`, `theta' -> theta' + k' alpha`. So
  `(omega_1, omega_2) ∈ Bad`.

Hence the set lies in `(zeta^+ x zeta^+)(Bad)`, which is `mu x mu`-null by injectivity. ∎

**Theorem 3 (`Gamma = F_2`).**
1. For every `(eta, eta') ∉ N` and every finite `H ⊂ F`, put `B_H = ⋃_{u ∈ H} uB`. Then
   `#{g ∈ F : g eta ∈ B_H and g eta' ∈ B_H} < infinity`.
2. Let `(Z, mu_Z)` be an imp `F`-space with a measurable equivariant `xi : Z -> dF`, such that
   `xi_*(mu_Z|_E) << nu` for every `E` of finite measure. Then `F` acts totally dissipatively on `(Z x Z, mu_Z x mu_Z)`.
   If `Z` is ergodic, it is not PDR (as in Theorem A of `fpbs-dini-boundary-class-diagonal-dissipative`).

*Proof of 1.* Write `eta = h zeta^+(omega)` and `eta' = h' zeta^+(omega')`. Since `(eta, eta') ∉ N`, we have
`(omega, omega') ∉ Bad`. Fix `u, u' ∈ H`. By Lemma 4.1:
- `g eta ∈ uB` if and only if `g = u gamma_k(omega) h^{-1}` for some `k`, and distinct `g` give distinct `k`;
- `g eta' ∈ u'B` if and only if `g = u' gamma_{k'}(omega') h'^{-1}` for some `k'`.

Both hold if and only if `gamma_k(omega) = x gamma_{k'}(omega') y` with `x = u^{-1} u'` and `y = h'^{-1} h`. By
Proposition 5.2 there are finitely many such `(k, k')`, hence finitely many `g`. Summing over the finitely many
`(u, u')` proves 1.

*Proof of 2.*
- *A cover.* Since `xi_*(mu_Z|_E) << nu` and `nu(dF minus FB) = 0`, almost every `z` has `xi(z) ∈ FB`. Choose
  finite-measure sets `E_n` increasing to `Z` and finite sets `H_n` increasing to `F`. Put
  `E'_n = E_n ∩ xi^{-1}(B_{H_n})`. These increase to a conull subset of `Z`.
- *Pairs avoid `N`.* The measure `(xi x xi)_*(mu_Z|_{E'_n} x mu_Z|_{E'_n})` is the product of two measures `<< nu`, so
  it is `<< nu x nu`. By Lemma 5.3, a.e. pair `(z, z') ∈ E'_n x E'_n` has `(xi z, xi z') ∉ N`.
- *Finite returns.* If `g(z, z') ∈ E'_n x E'_n`, then `g xi(z)` and `g xi(z')` lie in `B_{H_n}`. By part 1, a.e.
  `(z, z') ∈ E'_n x E'_n` has only finitely many such `g`.
- *Dissipativity.* Let `C` be the conservative part of the diagonal action. By the recurrence theorem for countable
  groups (e.g. Aaronson, *An introduction to infinite ergodic theory*, §1.6), a.e. point of `C ∩ (E'_n x E'_n)` returns
  to `E'_n x E'_n` under infinitely many `g`. So `C ∩ (E'_n x E'_n)` is null for every `n`, and `C` is null. ∎

So no imp action with this boundary class, amenable or not, can serve as a BB certificate. This is consistent with
`F_2` having cost `2`.

## 6. Theorem 3 for a torsion-free hyperbolic `Gamma`, conditional on (M) and (LI)

Let `Gamma` be torsion-free and nonelementary hyperbolic. By (M), choose `F = <a,b>` malnormal and quasiconvex, so that
(S) holds for it (a quasiconvex free subgroup has a quasi-isometrically embedded tree). Build `nu` from `F` as in
Section 2. Theorems 1 and 2 apply to this `F` unchanged. Theorem 2 is about the `F`-action on `dF`.

**Lemma 6.1.** Let `gamma ∈ Gamma` and `zeta ∈ dF`. If `gamma iota(zeta) ∈ Lambda_F`, then `gamma ∈ F`.

*Proof.* `iota(zeta) ∈ Lambda_F ∩ gamma^{-1} Lambda_F = Lambda(F) ∩ Lambda(gamma^{-1} F gamma)`. Both subgroups are
quasiconvex, so by (LI) this is `Lambda(F ∩ gamma^{-1} F gamma)`. If `gamma ∉ F`, malnormality makes the intersection
trivial and its limit set empty. ∎

**Theorem 3' (conditional).** Under (M) and (LI), both parts of Theorem 3 hold for `Gamma`, with `B` replaced by
`iota(B)`, `F` by `Gamma` in the choice of `H` and of the translates, and `N` defined with `h, h' ∈ Gamma`.

*Proof.*

*Returns reduce to `F`.* Let `eta = h iota zeta^+(omega)` and `eta' = h' iota zeta^+(omega')` with `h, h' ∈ Gamma`, and
let `u, u' ∈ Gamma`.
- If `g eta ∈ u iota(B)`, then `u^{-1} g h iota(zeta^+(omega)) ∈ Lambda_F`. By Lemma 6.1, `u^{-1} g h ∈ F`.
- Then `iota` is equivariant and injective, so `u^{-1} g h zeta^+(omega) ∈ B`, and Lemma 4.1 gives
  `u^{-1} g h = gamma_k(omega)`.
- Likewise `u'^{-1} g h' = gamma_{k'}(omega')`.

So joint returns correspond to solutions of `gamma_k(omega) = x gamma_{k'}(omega') y`, with `x = u^{-1} u'` and
`y = h'^{-1} h` now in `Gamma`.

*Forcing `x, y ∈ F`.* Suppose there are infinitely many solutions.
- For fixed `k'`, the element `gamma_k(omega)` is determined, hence so is `k`. So there are two solutions
  `(k_1, k'_1)`, `(k_2, k'_2)` with `k'_1 != k'_2`.
- Put `f_i = gamma_{k_i}(omega) ∈ F` and `c = gamma_{k'_1}(omega')^{-1} gamma_{k'_2}(omega') ∈ F`. Here `c != e`,
  because the points `gamma_{k'}(omega') zeta^+(omega') = zeta^+(sigma^{k'} omega')` are distinct.
- Then `y^{-1} c y = f_1^{-1} f_2 ∈ F ∩ y^{-1} F y` is nontrivial. Malnormality gives `y ∈ F`.
- So `x = f_1 y^{-1} gamma_{k'_1}(omega')^{-1} ∈ F`.

Now Proposition 5.2 applies and gives finitely many solutions. This contradiction proves the analogue of Theorem 3(1).

*The null set.* The proof of Lemma 5.3 goes through. The only change is that `g^{-1} h iota(zeta) ∈ iota(B)` first
forces `g^{-1} h ∈ F` by Lemma 6.1.

*Part 2.* The proof of Theorem 3(2) is unchanged. ∎

**Where torsion-freeness enters.** It enters only through (M). A group with torsion can have every free quasiconvex
subgroup non-malnormal. Then a translate `y` outside `F` with `y^{-1} F y ∩ F != e` gives new solutions that
Proposition 5.2 does not control. Theorems 1 and 2 need no torsion-freeness.

## 7. Remarks

**What dies, exactly.** The suggested attack was to generalise Lemma 3 of the Dini proof: "two reversal matches of one
pair of rays at nearby scales force periodicity, so matches are lacunary". Take a reversal match at length `m`
(`w^{-1}` is a prefix) and another at `m' ∈ (m, 2m)`.
- Their overlap forces the prefix of length `m'` to have period `m' - m`.
- That is a *local* period, not a global one.
- Sturmian and rotation words have local periods (the continuant denominators `q_n` of `alpha`) at every scale.

So the step "periodicity is impossible, hence lacunary" fails. Theorem 2 quantifies it: matches occur at every scale
`k` with probability at least about `1/(2k)`. The script's tail `P(count >= k) ≈ 0.55/k` agrees.

**Why first moments cannot work.** Theorems 1 and 2 are first-moment divergences: expected match mass. Theorem 3 is a
pointwise, a.e.-finite statement. The gap is a heavy tail: the count is a.e. finite with infinite mean. Any criterion
that sums probabilities, as Borel--Cantelli does, loses exactly this information.

**Rational calibration.** For rational `alpha` every ray is periodic. Lemma 1.1(3) fails, the fixed points of elements
carry mass, and Proposition 5.2 fails too (`Bad` has positive measure). This is correct: periodic rays are fixed by
elements, and their pairs return infinitely often.

**Next step: type III classes.** Here the class contains an invariant sigma-finite measure (Theorem 2), so the
Maharam extension of `(dF_2, nu)` is a product. The open case is a rotation code whose cylinder weights follow a
nontrivial multiplicative cocycle over the rotation (Anzai/Denjoy skew weights), so that the class is type III. In the
Maharam extension, a return also has to match the Radon--Nikodym coordinate, and rigidity has to be proved for the
skew product rather than the rotation. The named statement is **pointwise match rigidity**: for an ergodic imp action
of a torsion-free hyperbolic group with boundary map `xi`, a.e. crossing pair `(z, z')` has only finitely many `g` with
`g(z, z')` in a fixed product of finite-measure sets. That statement would imply the claimed non-existence of BB
certificates for hyperbolic groups in the same way Theorem 3 does here.
