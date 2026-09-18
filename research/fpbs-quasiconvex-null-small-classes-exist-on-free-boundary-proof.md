---
rg: 2
id: fpbs-quasiconvex-null-small-classes-exist-on-free-boundary-proof
kind: route
title: Proof that a symmetric dyadic-odometer code with killing words for every finite non-covering Stallings graph gives an ergodic nonatomic boundary class of F_2 that is quasiconvex-null, has no shadow-summable measure, and is singular to every Dini measure
target: fpbs-quasiconvex-null-small-classes-exist-on-free-boundary
requires:
  - fpbs-dini-boundary-class-diagonal-dissipative
  - fpbs-quasiconvex-limit-set-classes-are-never-pdr
---

# Proof

**Notation.**
- `F_2 = <a, b>`, with letters `a, A = a^{-1}, b, B = b^{-1}`. Letters `a, A` are **`a`-type** and `b, B` are
  **`b`-type**.
- `dF_2` is the set of infinite reduced words, and `[w]` is the cylinder of rays beginning with the reduced word `w`.
- `sigma` is the one-sided shift on rays (delete the first letter). If `eta = l eta'` with `eta'` reduced, then
  `l^{-1} eta = eta'`.
- A word is **alternating** if consecutive letters have different types. Alternating words are reduced.
- A **folded graph** `Delta` is a finite vertex set `V` with two partial injections `sigma_a, sigma_b` of `V`. Reading
  `a` moves by `sigma_a` and reading `A` by `sigma_a^{-1}`. It is a **covering** if both are total.
- In the tree `Cay(F_2)` we have `delta = 0` and `O_s(g) ⊇ O_0(g) = [g]`. So `S_s(lambda) >= S_0(lambda) =
  sum_g lambda[g] lambda[g^{-1}]` for every `s >= 0`.

## Step 1. Killing words (Lemma 1)

**Lemma 1.** Let `Delta` be a finite folded graph none of whose connected components is a covering. For each type
`t` and all large `m`, some alternating word of length `m` beginning with a letter of type `t` is readable from no
vertex of `Delta`.

*Proof.* Take the states `(v, t)`, where `t` is the type of the next letter. The transfer matrix `M` has entry
`M[(v,a-type),(w,b-type)] = #{e = ±1 : sigma_a^e(v) = w}`, and the `b`-type rows are defined in the same way. Every
row sum of `M` is at most 2. The number of alternating words of length `m` with first type `t` that are readable from
some vertex is at most `sum_v (M^m 1)_{(v,t)} <= C m^{2|V|} rho(M)^m`. There are `2^m` such words in total. So it
suffices to show that `rho(M) < 2`. We have `rho(M) <= 2` because the row sums are at most 2.

Suppose `rho(M) = 2`. The Frobenius normal form gives a strongly connected class `C` of states such that the
restriction `M_C` has spectral radius 2. The row sums of `M_C` are at most 2. An irreducible nonnegative matrix whose
row sums are all at most `r`, with at least one strictly smaller, has spectral radius `< r`. So every row of `M_C` sums
to exactly 2, meaning both edges out of every state of `C` stay in `C`. Put `P = {v : (v, a-type) in C}` and
`Q = {w : (w, b-type) in C}`. Then:
- `sigma_a` and `sigma_a^{-1}` are defined on all of `P` and map `P` into `Q`;
- `sigma_b` and `sigma_b^{-1}` are defined on all of `Q` and map `Q` into `P`.

These are injections, so `|P| <= |Q| <= |P|`. Hence each of the four maps is a bijection, and `sigma_a(P) = Q =
sigma_a^{-1}(P)`. The second equality gives `sigma_a(Q) = P`, and in the same way `sigma_b(Q) = P` and `sigma_b(P) =
Q`. So `sigma_a^{±1}` and `sigma_b^{±1}` are defined on all of `W = P ∪ Q` and preserve it.

Hence no edge joins `W` to its complement. An edge `u -> u'` with `u` in `W` has `u'` in `W`. An edge `u' -> u` with
`u` in `W` has `u' = sigma^{∓1}(u)`, which is in `W`. So `W` is a nonempty union of components on which both maps are
total, that is, a covering component. This is a contradiction. For a disjoint union, `rho` is the maximum over the
components. `□`

(The script checks `rho < 2` for all 26131 connected non-covering folded graphs with at most 4 vertices: the largest
value is `1.7989`.)

**Lemma 2.** Let `H <= F_2` be finitely generated and nontrivial, with Stallings core `Delta_H`. Then every ray in
`Lambda_H` has a tail that is readable in `Delta_H`, starting at some vertex. `Delta_H` is not a covering if and only
if `[F_2 : H] = infinity`. Also, `Delta_{gHg^{-1}} ≅ Delta_H` as labelled graphs, and `Lambda_{gHg^{-1}} = g Lambda_H`.

*Proof.* Choose the base point `*` in the core, replacing `H` by a conjugate if necessary; this changes `Lambda_H` by
a translate and does not change the core. The tree `T_H` spanned by the axes of the elements of `H` is the universal
cover of `Delta_H`, and `Lambda_H = d T_H`. A ray in `d T_H` from `e` stays in `T_H` after the finite segment that
joins `e` to `T_H`. After that segment it reads a path in `Delta_H`. Stallings: a finite core is a covering iff the
index is finite. The last two assertions are standard. `□`

Fix an enumeration `(Delta_i)_{i >= 1}` of the countably many finite connected folded non-covering graphs, up to
isomorphism.

## Step 2. The code

Put `q_n = 2^{n+2}` and let `Omega = lim Z/q_n`, with Haar measure `m` and the translation `x -> x+1`. The
translation is uniquely ergodic, hence ergodic. We build labellings `F_n : Z/q_n -> {a, A, b, B, hole}` by induction.
Every `F_n` has three properties:
- **(T)** a non-hole value at `y` is `a`-type if `y` is even and `b`-type if `y` is odd;
- **(S)** `F_n(-y) = F_n(y)^{-1}` whenever `F_n(y)` is not a hole;
- **(H)** the holes of `F_n` are exactly the residues `0` and `q_n / 2`.

The base case is `F_0` on `Z/4`, with `F_0(1) = b`, `F_0(3) = B`, and holes at `0` and `2`.

**Toeplitz step.** Lift `F_n` to `Z/q_{n+1}` periodically. The lifted holes are `0, q_{n+1}/4, q_{n+1}/2,
3q_{n+1}/4`. Put `F(q_{n+1}/4) = l` and `F(3q_{n+1}/4) = l^{-1}`, where `l` is either `a`-type letter (`q_{n+1}/4 =
q_n/2` is even). The residues `q_{n+1}/4` and `3q_{n+1}/4` are negatives of each other mod `q_{n+1}`. So (T), (S) and
(H) hold again.

**Overwrite step** (only at stages `n = n_j`, with `n_1 < n_2 < ...` sparse). Let `k_j` be an alternating word of
length `l_j` given by Lemma 1 for `Delta_1 ⊔ ... ⊔ Delta_j`. Its first letter has type equal to the parity of a chosen
residue `r_j`, with `q_{n_j}/8 <= r_j <= q_{n_j}/4`. Overwrite:
- `F(r_j + i) = k_j[i]` for `0 <= i < l_j`;
- the mirror window: `F(-(r_j + i)) = k_j[i]^{-1}`.

We need `l_j < q_{n_j}/8`, so that the windows avoid the holes and each other. Since `-y` has the same parity as `y`,
(T) and (S) are preserved. The parameters are chosen so that
- `(O1)` `sum_j 2 l_j / q_{n_j} < infinity`;
- `(O2)` `sum_{i > j} 2 (l_i + l_j) / q_{n_i} < 1 / (2 q_{n_j})` for every `j`.

For example, choose `n_j` inductively, huge compared with `l_j`, which is fixed by `Delta_1, ..., Delta_j` via
Lemma 1.

**The limit.** For `y in Omega`, `F_n(y) := F_n(y mod q_n)`. The value at `y` changes from stage `n` to stage `n+1`
only if one of two things happens:
- `y` is a stage-`n` hole. The set of such `y` has measure `2/q_n`, which is summable.
- `y` lies in a stage-`n` overwrite window. The measure of these is `2 l_j / q_{n_j}`, which is summable by (O1).

By Borel--Cantelli, for a.e. `y` the sequence `F_n(y)` is eventually constant and not a hole. Put `F(y)` equal to that
limit. Every translate `y = x + t` (`t in Z`) is again a.e. good, so for a.e. `x` all of `F(x+1), F(x+2), ...` are
letters. Put

`zeta(x) = F(x+1) F(x+2) F(x+3) ...`,

which is alternating by (T), hence a ray in `dF_2`. Then `sigma zeta(x) = zeta(x+1)`, that is,
`zeta(x+1) = F(x+1)^{-1} zeta(x)`. Put `nu_0 = zeta_* m`, which is `sigma`-invariant, and
`nu = sum_g c_g g_* nu_0` with all `c_g > 0`. Then `nu` is quasi-invariant and `nu_0 << nu`. (S) passes to the limit:
`F(-y) = F(y)^{-1}` for a.e. `y`.

**Survival of the killing windows.** Let `P_j = {x in Omega : F(x+1) ... F(x+l_j) = k_j}`. At stage `n_j`, every `x`
with `x ≡ r_j - 1 (mod q_{n_j})` has `F_{n_j}(x+1) ... F_{n_j}(x+l_j) = k_j`.
- Later holes lie in the residue class `0 mod q_{n_j}`, because `q_n/2 ≡ 0` for `n > n_j`. That class is outside the
  window, so no hole ever touches it.
- A later overwrite at stage `n_i > n_j` meets the window of `x` with probability at most `2(l_i + l_j)/q_{n_i}`.

Hence, by (O2), `m(P_j) >= 1/q_{n_j} - 1/(2 q_{n_j}) > 0`.

## Step 3. Ergodic, quasiconvex-null, nonatomic

**Ergodic.** Let `E ⊂ dF_2` be Borel and `F_2`-invariant. Then `nu(E) = sum_g c_g nu_0(g^{-1}E) = nu_0(E)`. Put
`A_E = zeta^{-1}(E)`. Then `x in A_E` iff `zeta(x+1) = F(x+1)^{-1} zeta(x) in E`. So `A_E` is translation-invariant
modulo null sets, and `nu(E) = m(A_E)` is 0 or 1.

**Quasiconvex-null.** In `F_2`, the finitely generated subgroups are exactly the quasiconvex ones. Let `U` be the
union of `F_2 Lambda_H` over all finitely generated `H` of infinite index. This is a countable union and is
`F_2`-invariant. `Lambda_{1}` is empty. For `H ≠ 1`, Lemma 2 shows that a point of `F_2 Lambda_H` has a tail that is
readable in `Delta_H ≅ Delta_i` for some `i`.

Fix `i`. Since `m(P_i) > 0` and the translation is ergodic, Birkhoff's theorem gives, for a.e. `x`, infinitely many
`t >= 0` with `x + t in P_i`. So every tail of `zeta(x)` contains `k_i` as a subword. If a tail were readable from a
vertex of `Delta_i`, then `k_i` would be readable from some vertex of `Delta_i`. This is impossible, because `k_i` is
unreadable in `Delta_1 ⊔ ... ⊔ Delta_i`. Hence `nu_0(U) = 0`, and so `nu(U) = 0` by invariance. This is item 2.

**Nonatomic.** `nu_0` is `sigma`-invariant, since `sigma zeta(x) = zeta(x+1)`. It is ergodic, being a factor of `m`.
Suppose `eta` is an atom. Poincaré recurrence applied to `{eta}` gives `sigma^p eta = eta` for some `p >= 1`. So `eta
= u u u ...` with `u` cyclically reduced, and `eta in Lambda_{<u>}`. But `<u>` is cyclic, hence of infinite index in
`F_2`, and this contradicts `nu_0(U) = 0`. So `nu_0` is nonatomic, and therefore so is `nu`. This finishes item 1.

## Step 4. No shadow-summable measure (item 3)

Let `lambda ~ nu` be a probability measure. Then `nu_0 << lambda`. Put `h = d nu_0 / d lambda`, and choose `c > 0`
such that `A' = {h <= 1/c}` has `nu_0(A') > 0`. Then `lambda(E) >= c nu_0(E ∩ A')` for every Borel `E`.

Put `A = zeta^{-1}(A')`, so that `m(A) = nu_0(A') > 0`. Put `C_w = zeta^{-1}[w] = {x : F(x+1) ... F(x+m) = w}` for
`|w| = m`. Then

`S_s(lambda) >= S_0(lambda) >= c^2 sum_{m >= 1} T_m`, where `T_m = sum_{|w| = m} m(C_w ∩ A) m(C_{w^{-1}} ∩ A)`.

**The involution.** Put `tau_m(x) = -x-m-1`. It preserves `m`. By (S),
`F(tau_m x + i) = F(-(x + m + 1 - i)) = F(x+m+1-i)^{-1}` for `1 <= i <= m`. So `prefix_m(tau_m x) =
prefix_m(x)^{-1}` and `tau_m C_w = C_{w^{-1}}`. Put `a_w = m(C_w ∩ A)` and `b_w = m(C_{w^{-1}} ∩ A) = m(C_w ∩ tau_m
A)`. Then `T_m = sum_w a_w b_w >= sum_w min(a_w, b_w)^2`.

**Cells.** Fix `K >= 1`. For `m` large, choose `N = N(m)` with `q_N in [Km, 2Km]`. Let `G_m` be the set of `x` such
that:
- none of `x+1, ..., x+m` is a stage-`N` hole;
- none of them lies in an overwrite window of a stage `n_i > N`.

On `G_m`, the word `prefix_m(x)` is determined by `x mod q_N`. So the set `W_m` of prefixes realized on `G_m` has
`|W_m| <= q_N <= 2Km`. Moreover,

`Err_m := m(Omega \ G_m) <= 2m/q_N + sum_{n_i > N} 2(m + l_i)/q_{n_i} <= 4/K + eps_N`,

where `eps_N = sum_{n_i > N} 2 l_i / q_{n_i} -> 0` by (O1). Since `G_m ⊂ ∪_{w in W_m} C_w`, Cauchy--Schwarz gives

`T_m >= (sum_{w in W_m} min(a_w, b_w))^2 / |W_m| >= (m(A ∩ tau_m A ∩ G_m))^2 / (2Km)
      >= (f(c_m) - Err_m)_+^2 / (2Km)`,

where `c_m = -(m+1)` and `f(c) = m(A ∩ (c - A))`. Note that `tau_m A = c_m - A`.

**Equidistribution.** `f` is continuous on `Omega`, being a convolution of two `L^2` functions. By Fubini,
`int f = m(A)^2`, and so `int f^2 >= m(A)^4`. Choose `K >= 20/m(A)^2` and put `eps = 5/K`. For large `m` we have
`Err_m <= eps`, so `T_m >= g_m/(2Km)` with `g_m = (f(c_m) - eps)_+^2`.

The dyadic odometer is uniquely ergodic, and `phi = (f - eps)_+^2` is continuous. Hence

`(1/M) sum_{m <= M} g_m -> int phi >= int f^2 - 2 eps int f >= m(A)^4 - 10 m(A)^2 / K >= m(A)^4 / 2`.

By Abel summation, `sum_m g_m / m = infinity`, since the partial sums of `g_m` grow at least like `M m(A)^4 / 3`.
Hence `sum_m T_m = infinity`, and `S_s(lambda) = infinity` for every `s`. `□`

## Step 5. Dini-singular (item 4)

`[nu]` is an ergodic quasi-invariant class. By Theorem C of `fpbs-dini-boundary-class-diagonal-dissipative`, it is
either absolutely continuous with respect to a finite Dini measure `lambda`, or singular to every such measure.

In the first case, put `lambda' = min(d nu / d lambda, 1) lambda`, normalized. We have `lambda' <= lambda` up to the
normalizing constant, so its modulus is at most a constant times that of `lambda`, and `lambda'` is Dini. Also
`lambda' ~ nu`. By Theorem B.1 there, `lambda'` is shadow-summable, which contradicts Step 4. So `[nu]` is singular to
every Dini measure. `□`

## Step 6. Consequence

On `F_2`, `[nu]` passes the Dini filter (Step 5), the shadow filter (Step 4) and the quasiconvex filter of
`fpbs-quasiconvex-limit-set-classes-are-never-pdr` (Step 3). But `F_2` has no BB certificate at all. A certificate
would give fixed price 1 by Bevilacqua--Bowen, arXiv:2510.05459, Theorem 8.1, while `F_2` has cost 2 (Gaboriau). So
these three filters do not characterize certificate classes. A proof that some hyperbolic group has no certificate
must use a further property. `□`

## Calibration

`experiments/quasiconvex-null-classes-2026-09-17/odometer_code.py`, with output `odometer_code.out`, checks the
following:
- Lemma 1 for every graph with at most 4 vertices;
- a length-12 alternating killing word for all 703 graphs with at most 3 vertices;
- properties (T) and (S), reducedness and the `tau_m` identity on the code at `Z/2^15`;
- `m T_m in [0.167, 0.250]` for the Haar class, for `m <= 1024`.
