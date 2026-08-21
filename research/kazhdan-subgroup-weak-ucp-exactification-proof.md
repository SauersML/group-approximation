---
rg: 2
id: kazhdan-subgroup-weak-ucp-exactification-proof
kind: route
title: Kazhdan-average the Stinespring corner to an exact C-invariant subspace, then polar-correct the letter inside the C-commutant
target: kazhdan-subgroup-weak-ucp-exactifies-microstates
requires: []
---

Notation as in the claim.  `|| . ||_HS` is the UNNORMALIZED
Hilbert--Schmidt norm on `B(H^_n)`; `|| x ||_(2,d) = || x ||_HS / sqrt d`.
All limits are `n -> infinity`; `o(1)` means a sequence tending to `0`
that may depend on the group element but not on the vector.

**Step 0 (restrict).**  `phi_n|_C` is a hyperlinear approximation of `C`
(asymptotic multiplicativity and the separation `liminf || phi_n(c) - 1 ||_2
>= sqrt 2`, `c != e`, are inherited from `G`).  Weak ucp-stability gives
genuine representations `pi_n : C -> U(H^_n)`, `H^_n supseteq H_n = C^(d_n)`,
with

```text
|| phi_n(c) - P_n pi_n(c) P_n ||_(2,d_n) -> 0   for every c in C.   (P1)
```

**Step 1 (the corner almost commutes with `pi_n(C)`).**  Write
`pi = pi_n`, `P = P_n`, `P^perp = 1 - P`.  Then

```text
|| P^perp pi(c) P ||_HS^2 = Tr(P pi(c)^* P^perp pi(c) P)
                          = d_n - || P pi(c) P ||_HS^2,
```

and by `(P1)` `|| P pi(c) P ||_HS >= || phi_n(c) ||_HS - o(sqrt d_n)
= sqrt d_n - o(sqrt d_n)`, so `|| P^perp pi(c) P ||_HS = o(sqrt d_n)`;
the same with `c^(-1)` bounds `|| P pi(c) P^perp ||_HS`.  Hence

```text
|| [pi(c), P] ||_HS = o(sqrt d_n)   for every c in C.              (P2)
```

**Step 2 ((T) on the Hilbert--Schmidt space).**  `Ad pi : c |-> pi(c)(.)pi(c)^*`
is a unitary representation of `C` on the Hilbert space `HS(H^_n)` (this
is where infinite-dimensionality of `H^_n` is harmless: Hilbert--Schmidt
operators form a Hilbert space regardless).  By `(P2)` the unit vector
`xi = P / sqrt d_n` is `(S, o(1))`-invariant.  Let `P_inv` be the
orthogonal projection onto the `Ad pi(C)`-invariant vectors
`pi(C)' cap HS(H^_n)`.  With the Kazhdan pair `(S, kappa)`
(Bekka--de la Harpe--Valette Prop. 1.1.9),

```text
|| xi - P_inv xi || <= (1/kappa) max_(s in S) || Ad pi(s) xi - xi || =: delta_n -> 0.  (P3)
```

Realize `P_inv xi` as a limit of averages: with `M = (1/2)(1 + (1/|S|)
sum_(s in S) Ad pi(s))`, the lazy Markov operator, (T) gives
`spec(M|_(inv^perp)) subseteq [0, 1 - kappa^2/4]`, so `M^k xi -> P_inv xi`
in `HS`.  Each `M^k` is a convex combination of conjugations, hence
maps positive contractions to positive contractions; `HS`-limits of
positive contractions are positive contractions (HS convergence implies
strong convergence).  Therefore

```text
Q := sqrt(d_n) . P_inv xi  is a POSITIVE CONTRACTION in pi(C)',
|| Q - P ||_HS <= delta_n sqrt d_n.                                 (P4)
```

(Operator-norm control of `Q` is the point of using the averages rather
than an abstract nearest invariant vector; it is needed in the next line.)

**Step 3 (spectral projection).**  Put `D = Q - P` (self-adjoint,
`|| D ||_op <= 2`, `|| D ||_HS <= delta_n sqrt d_n`).  Then
`Q^2 - Q = PD + DP + D^2 - D`, so
`|| Q^2 - Q ||_HS <= 3 delta_n sqrt d_n + || D ||_op || D ||_HS
<= 5 delta_n sqrt d_n`.  The pointwise inequality

```text
| 1_([1/2, infinity))(x) - x | <= 2 | x^2 - x |   for all real x    (P5)
```

(checked on the five intervals `x < 0`, `[0,1/2)`, `[1/2,1]`, `x > 1`
and at `x = 1/2`, where both sides equal `1/2`) and the functional
calculus give, for `E := 1_([1/2, infinity))(Q)`,

```text
|| E - Q ||_HS <= 2 || Q^2 - Q ||_HS <= 10 delta_n sqrt d_n,
|| E - P ||_HS <= 11 delta_n sqrt d_n.                              (P6)
```

`E` is a spectral projection of the compact operator `Q` away from `0`,
hence FINITE RANK, and `E in pi(C)'` because `Q in pi(C)'`.  Set
`V_n := ran E`, `d'_n := rank E`.  For projections
`|| E - P ||_HS^2 = Tr E + Tr P - 2 Tr(EP) >= | Tr E - Tr P |`, so
`| d'_n - d_n | <= 121 delta_n^2 d_n`, i.e. `d'_n / d_n -> 1`.  The
restriction `rho_n := pi_n|_(V_n)` is a GENUINE finite-dimensional
unitary representation of `C`.

**Step 4 (identify the corner with `V_n`).**  Let `X = E P` with polar
decomposition `X = W_n |X|`, `|X| = (P E P)^(1/2)`.  Since
`0 <= Y := PEP <= P` and `|| Y - P ||_HS = || P(E - P)P ||_HS <= 11 delta_n
sqrt d_n`, and `0 <= 1 - sqrt y <= 1 - y` on `[0,1]`, we get
`|| |X| - P ||_HS <= 11 delta_n sqrt d_n`; with `|| X - P ||_HS <= 11
delta_n sqrt d_n` and `W_n P = W_n` this yields

```text
|| W_n - P ||_HS <= 22 delta_n sqrt d_n,                            (P7)
```

so `W_n : H_n -> V_n` is a partial isometry with
`|| W_n^* W_n - 1_(H_n) ||_(2,d_n) -> 0` and
`|| W_n W_n^* - 1_(V_n) ||_(2,d'_n) -> 0` (the latter via `(P6)`).

**Step 5 (transport and exactify on `C`).**  Define on `V_n`

```text
phi~_n(g) := W_n phi_n(g) W_n^* + (1_(V_n) - W_n W_n^*),   g in G.  (P8)
```

Because `W_n` is near-unitary in normalized HS and the padding corner has
vanishing normalized trace, `phi~_n` is again a hyperlinear approximation
of `G` and `|| phi~_n(g) - W_n phi_n(g) W_n^* ||_(2,d'_n) -> 0`.  For
`c in C`, by `(P7)`, `(P1)` and `(P6)` (all multiplied by contractions):

```text
|| rho_n(c) - W_n phi_n(c) W_n^* ||_(2,d'_n)
  <= || E pi(c) E - P pi(c) P ||_(2,d'_n) + || P pi(c) P - phi_n(c) ||_(2,d'_n)
     + || phi_n(c) - W_n phi_n(c) W_n^* ||_(2,d'_n)  ->  0.           (P9)
```

Put `phi'_n(c) := rho_n(c)` for `c in C` and `phi'_n(g) := phi~_n(g)`
for `g in G - C`.  A pointwise `|| . ||_2`-small change of a hyperlinear
approximation is a hyperlinear approximation (both defining conditions are
pointwise limits), so `phi'_n` is one, genuine on `C`: this is `(i)` and
`(iii)` for `g != t`.

**Step 6 (the letter).**  `T' := phi~_n(t) in B(V_n)` satisfies
`|| T'^* T' - 1 ||_2 -> 0` and, by asymptotic multiplicativity of `phi_n`
on `[t, s] = e` and `(P9)`, `|| [T', rho_n(s)] ||_(2,d'_n) -> 0` for
`s in S`.  Now run Step 2 inside the FINITE-dimensional representation
`Ad rho_n` of `C` on `B(V_n)`: the lazy averages of `T'` converge to
`X' := P'_inv T' in rho_n(C)' cap B(V_n)`, a contraction, with
`|| X' - T' ||_2 <= (1/kappa) max_s || [T', rho_n(s)] ||_2 -> 0`, hence
`|| X'^* X' - 1 ||_2 -> 0`.  `B := rho_n(C)' cap B(V_n)` is a
finite-dimensional von Neumann algebra, so the polar decomposition
`X' = U |X'|` has `U` a partial isometry IN `B`, which extends to a unitary
`T'' in B` (in a finite von Neumann algebra `1 - U^*U ~ 1 - UU^*`).  Using
`0 <= | 1 - sqrt y | <= | 1 - y |` for `y >= 0`,

```text
|| T'' - X' ||_2 = || T''(1 - |X'|) ||_2 <= || 1 - X'^* X' ||_2 -> 0.  (P10)
```

Set `phi'_n(t) := T''`.  It is a unitary commuting exactly with
`rho_n(C) = phi'_n(C)`, and `|| phi'_n(t) - W_n phi_n(t) W_n^* ||_2 -> 0`,
completing `(ii)` and `(iii)`.

**Wreath variant.**  For `W` the lamp `e` is an involution; take `T'`
self-adjoint (replace by `(T' + T'^*)/2`, an `o(1)` change), note the
averages preserve self-adjointness, so `X'` is self-adjoint in `B`, and
replace the polar step by `T'' := sgn(X') in B`, using
`| sgn(x) - x | <= | x^2 - 1 |` for real `x` (check on `[0,1]`, `x > 1`,
and by symmetry): `|| T'' - X' ||_2 <= || X'^2 - 1 ||_2 -> 0`.  The other
lamps are the `phi'_n(a)`-conjugates of `T''`; their relations hold
asymptotically because `phi'_n` is pointwise close to `phi~_n`.

**Ultraproduct consequence.**  `pi := [phi'_n|_A]` has trace
`lim tr phi'_n(a) = delta_e(a)` (regular), `pi|_C` is the ultraproduct
of the genuine `rho_n`, and `k := [T'']` commutes with `pi(C)` exactly
because it does so at every finite level.  Finally
`tau(k pi(a_1) k^* pi(a_1)^*) = lim tr phi'_n([t, a_1]) = delta_e([t, a_1])
= 0` since `[t, a_1] != e` in `G` by Britton's lemma (`a_1 notin C`), so
`k notin pi(A)'`.  (For `W`: `e a_1 e a_1^(-1)` is a product of two distinct
lamps, nontrivial, trace `0`.)  This is the stated witness on the
`C`-exact face.
