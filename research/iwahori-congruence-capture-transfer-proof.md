---
rg: 2
id: iwahori-congruence-capture-transfer-proof
kind: route
title: Induce the transported congruence vertex, then round its almost-invariant copy of the other vertex by Selberg (tau)
target: iwahori-congruence-capture-transfers-across-one-edge
requires:
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - flexible-hs-metric-controls-words-and-padding
  - congruence-repair-bypasses-koopman-cycle-firewalls
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

Notation is as in the target. All norms `||.||_2` are normalized
Hilbert--Schmidt norms on the space indicated, and `||.||_HS` is the
unnormalized Frobenius norm. Fix a finite generating set `S_C` of `C`. Let
`S_+` be the generating set of `B_+` in the definition of `def`, and put
`S_- = sigma(S_+)`, a generating set of `B_- = sigma(B_+)`. Let `c_1, c_2, c_3`
be coset representatives of `C / B_-`.

**Selberg input.** `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, item 3,
records Selberg's theorem that `C` has property `(tau)` with respect to the
congruence subgroups `Gamma(N)`. Selberg's bound `lambda_1 >= 3/16` holds at
every level `N`, odd or even. In the form used here: there is `kappa > 0`,
depending only on `S_C`, such that every unitary representation `V` of `C`
factoring through some `SL_2(Z/N)` satisfies

```text
||v - E v|| <= kappa^(-1) max_(c in S_C) ||c v - v||,            (S)
```

with `E` the orthogonal projection onto `V^C`. Apply (S) to `v - Ev`, which
has no invariant component.

## Step 0. Exact case set-up

Let `pi = (pi_+, pi_-)` act on `C^d`, with `pi_+` trivial on `Gamma(m)`. Put
`eps = def(pi)`.

**The transported representation is congruence.** Define
`psi = pi_+ o sigma^(-1)`, an exact representation of `B_-`. Here
`sigma^(-1)[[a,b],[c,d]] = [[a,b/2],[2c,d]]`. If `g in Gamma(2m)`, then
`b/2 = 0 mod m`, `2c = 0 mod 4m` and `a = d = 1 mod 2m`, so
`sigma^(-1)(g) in Gamma(m)`. Moreover `Gamma(2m) <= Gamma^0(2) = B_-`. Hence
`psi` is trivial on `Gamma(2m)`, which is normal in `C`.

**The edge defect is a restriction defect.** For `s in S_+`,
`psi(sigma s) = pi_+(s)`, so

```text
max_(t in S_-) ||psi(t) - pi_-(t)||_2 = eps.                      (0)
```

## Step 1. Induction is Lipschitz and lands in level 2m

Realize `Ind_(B_-)^C phi` on `C^3 (x) C^d` in block form. Block `(i, j)` of
`g` is `phi(c_i^(-1) g c_j)` when that element lies in `B_-`, and zero
otherwise. Each block row has exactly one nonzero block.

The set `F = { c_i^(-1) g c_j in B_- : g in S_C }` is finite. Let `L` be the
largest word length over `S_-` of an element of `F`. Put `A = Ind psi` and
`pi' = Ind(Res_(B_-) pi_-)`. By (0) and the unitary telescoping of words,
every nonzero block of `A(g) - pi'(g)` has `d`-normalized norm `<= L eps`.
There are three such blocks in dimension `3d`, so

```text
eta := max_(g in S_C) ||A(g) - pi'(g)||_2 <= L eps.               (1)
```

If `n in Gamma(2m)`, then `c_i^(-1) n c_j in B_-` only when `i = j`, and
`psi(c_i^(-1) n c_i) = 1` because `Gamma(2m)` is normal. So `A` is trivial
on `Gamma(2m)`. In particular `A(C)` is finite.

## Step 2. The second vertex is an exact summand of `pi'`

The map `J v = 3^(-1/2) (pi_-(c_1)^(-1) v, pi_-(c_2)^(-1) v, pi_-(c_3)^(-1) v)`
is an isometry `C^d -> C^3 (x) C^d`. It intertwines `pi_-` with `pi'`: this
is the standard embedding of `pi_-` in `Ind Res pi_- = pi_- (x) l^2(C/B_-)`
as `pi_- (x) 1`. Let `W = J(C^d)` and `P = J J^*`. Then `[P, pi'(C)] = 0`,
`tau(P) = 1/3` for the normalized trace `tau` on `M_(3d)`, and
`J^* pi'(g) J = pi_-(g)`. By (1),

```text
||[A(g), P]||_2 = ||[A(g) - pi'(g), P]||_2 <= 2 eta      (g in S_C).   (2)
```

## Step 3. Selberg rounds `P` to an exact subrepresentation of `A`

The conjugation representation `X -> A(g) X A(g)^*` on `(M_(3d), <,>_HS)` is
unitary and trivial on `Gamma(2m)`. By (S) and (2), the orthogonal projection
`E` onto the fixed space `A(C)'` satisfies

```text
||P - E(P)||_2 <= 2 eta / kappa =: delta.                         (3)
```

Since `A(C)` is finite, `E` is the average of `A(g) . A(g)^*` over that
finite group. Hence `Y = E(P)` satisfies `0 <= Y <= 1` and `Y in A(C)'`.

Let `Q = 1_[1/2, 1](Y)`. Then `Q in A(C)'`, so `U = ran Q` is an exact
subrepresentation of `A`, trivial on `Gamma(2m)`.

`Q` is the Hilbert--Schmidt-nearest projection to `Y`. For a projection `R`,
`||Y - R||_HS^2 = tr Y^2 + tr(R(1 - 2Y))`, and `tr(R X) >=` the sum of the
negative eigenvalues of `X` (Ky Fan), with equality at `R = Q`. Therefore
`||Q - P||_2 <= ||Q - Y||_2 + ||Y - P||_2 <= 2 delta`.

For two projections,
`||Q - P||_2^2 = tau(Q) + tau(P) - 2 tau(QP) >= |tau(Q) - tau(P)|`. So with
`r = rank Q`,

```text
|r - d| <= 3d * 4 delta^2 = 12 delta^2 d.                          (4)
```

## Step 4. An isometric copy of `C^d` inside a congruence representation

Let `T = Q J : C^d -> U`, and let `e = ||(1 - Q) J||_HS`. Since
`(1 - Q) P = (P - Q) P`, we have

```text
e^2 <= ||P - Q||_HS^2 <= 3d * 4 delta^2 = 12 delta^2 d.
```

The singular values `s_i` of `T` lie in `[0, 1]`, and
`sum_i (1 - s_i^2) = e^2`. Take the polar decomposition `T = V |T|`. Then

- `||V - T||_HS^2 = sum_(s_i > 0) (1 - s_i)^2 <= e^2`;
- the kernel of `T` has dimension `k <= e^2`.

Let `U' = U (+) C^k`. Extend `V` to an isometry `V' : C^d -> U'` that sends
`ker T` onto `C^k`, so that `||V' - V||_HS^2 = k <= e^2`.

Put `rho_- = A|_U (+) 1_k`, an exact representation of `C` on `U'`, trivial
on `Gamma(2m)`, of dimension `D = r + k >= d`. In the ambient space
`H = C^(3d) (+) C^k`, let `M = A (+) 1` and `M' = pi' (+) 1`, and regard
`J : C^d -> H`. Then `V'` maps into the `M`-invariant subspace `U'`, and:

- `||V' - J||_HS <= ||V' - V||_HS + ||V - T||_HS + ||T - J||_HS <= 3e`;
- `||(M(g) - M'(g)) V'||_HS <= ||A(g) - pi'(g)||_HS <= sqrt(3d) eta`.

Also `J^* M'(g) J = pi_-(g)`. Hence

```text
V'^* M V' - J^* M' J = (V' - J)^* M V' + J^* (M - M') V' + J^* M' (V' - J),
a := ||pi_-(g) - V'^* rho_-(g) V'||_HS <= 6e + sqrt(3d) eta.
```

So `a / sqrt(d) <= alpha := sqrt(3) eta (24/kappa + 1)`. From (4) and
`k <= e^2`,

```text
(D - d)/D <= 24 delta^2.                                          (5)
```

## Step 5. The exact case of (CT1)

Choose a unitary `Phi : C^D -> U'` extending `V'` on `C^d (+) 0`, and put
`rho^_- = Phi^* rho_- Phi`. Write `X = rho^_-(g)` for `g in S_C`, and let
`p` be the projection onto `C^d (+) 0`.

- The off-diagonal corners of the unitary `X` satisfy
  `||p^perp X p||_HS^2 = d - ||p X p||_HS^2 <= 2 sqrt(d) a`, and likewise for
  `p X p^perp`, since `||p X p||_HS >= sqrt(d) - a`.
- The last corner has `||p^perp X p^perp||_HS^2 <= D - d`.

So the zero-padding distance satisfies

```text
d_2(pi_-(g), rho^_-(g))^2 <= (a^2 + 4 sqrt(d) a)/D + (D - d)/D
                          <= alpha^2 + 4 alpha + 24 delta^2.
```

Now let `pi^# = (pi_+ (+) 1_(D-d), rho^_-)`. This is an exact pair on `C^D`
whose vertices are trivial on `Gamma(m)` and `Gamma(2m)` respectively, so
`pi^#` lies in the class `C` of (DCC1). On the `+` side the only change is the
padding, which costs `sqrt((D-d)/D) <= sqrt(24) delta` by (5). By (1) and (3),
`eta <= L eps`, `delta <= 2 L eps / kappa` and `alpha <= sqrt(3) L eps (24/kappa + 1)`.
Hence, for `eps <= 1`,

```text
A_cong(pi) <= d_2(pi, pi^#) <= C_0 sqrt(eps),
C_0^2 = 3 L^2 (24/kappa + 1)^2 + 4 sqrt(3) L (24/kappa + 1) + 96 L^2/kappa^2.
```

For `eps > 1`, use `A_cong(pi) <= 2 <= 2 sqrt(eps)`: any trivial pair of
dimension `d` is congruence. Replace `C_0` by `max(C_0, 2)`. Nothing here
depends on `d` or `m`.

## Step 6. Approximate first vertex

Let `L_+` be the largest `S_C`-word length of an element of `S_+`.

1. The class of congruence representations of `C` is closed under adding
   trivial summands. So by `flexible-hs-metric-controls-words-and-padding`
   (`A <= A_up <= 2A`), for every `theta > 0` there is an exact congruence
   `rho_+` on `C^(D_1)` with `D_1 >= d` and `b := d_2(pi_+, rho_+) <= 2 A_+(pi) + theta`.
2. Put `pi^1 = (rho_+, pi_- (+) 1_(D_1 - d))`. The same lemma gives
   `sqrt((D_1 - d)/D_1) <= b`, so `d_2(pi, pi^1) <= b`.
3. For `s in S_+`, bound `def(pi^1)` in three pieces:
   - the word bound of that lemma gives `L_+ b` for `rho_+(s)` against `pi_+(s) (+) 0`;
   - the original defect gives `eps` for `pi_+(s) (+) 0` against `pi_-(sigma s) (+) 0`;
   - the padding costs `b`.

   So `def(pi^1) <= eps + (L_+ + 1) b`.
4. `d_2` is a metric on pairs, so apply Step 5 to the exact pair `pi^1`:

   ```text
   A_cong(pi) <= b + C_0 sqrt(eps + (L_+ + 1) b).
   ```

5. Let `theta -> 0` and put `C = C_0 sqrt(2 L_+ + 2)`. This gives the upper
   bound in (CT1).

The lower bound `A_+ <= A_cong` holds because the `+` vertex of a
congruence pair is a congruence representation, and `d_2` on pairs dominates
`d_2` on each vertex.

**The other vertex.** Swap the roles of the two vertices, using
`pi_- o sigma` on `B_+`. For `g in Gamma(2m)`,
`sigma(g) = [[a,2b],[c/2,d]]` lies in `Gamma(m)`, and
`Gamma(2m) <= Gamma_0(2) = B_+`. Steps 1--6 then apply verbatim with `B_+`
in place of `B_-`.

## Consequences

- **Consequence 1.** Let `def(pi_n) -> 0` and `A_+(pi_n) -> 0`.
  1. By (CT1), choose exact congruence pairs `rho_n` on `C^(D_n)` with
     `d_2(pi_n, rho_n) -> 0`.
  2. Let `L_B` be the largest `S_C`-word length of an element of
     `S_+ ∪ sigma(S_+)`. Local defect is `2 L_B`-Lipschitz in `d_2` by
     `flexible-hs-metric-controls-words-and-padding`, so `def(rho_n) -> 0`.
  3. `congruence-repair-bypasses-koopman-cycle-firewalls` applies to the
     same-dimensional exact congruence pairs `rho_n`. It gives compatible
     `pi~_n` on `C^(D_n)` with `d_2(rho_n, pi~_n) -> 0`.
  4. Hence `D(pi_n) <= d_2(pi_n, rho_n) + d_2(rho_n, pi~_n) -> 0`.

  For the converse, `A_+ <= D` because the `+` vertex of a compatible pair is
  a restriction of a representation of `SL_2(Z[1/2])`, which is congruence
  (Consequence 3).
- **Consequence 2.** If `def(pi_n) -> 0` and `D(pi_n) >= delta_0`, then
  `A_+(pi_n)` has no subsequence tending to `0`, by Consequence 1 applied to
  that subsequence. So `liminf A_+(pi_n) > 0`, and the same holds for `A_-`.
- **Consequence 3.** A compatible `pi~` restricts on `C_+` to the restriction
  of a representation of `SL_2(Z[1/2])`. That restriction is odd congruence by
  `finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence`. So
  `D(pi_n) -> 0` gives odd-congruence capture of `pi_(n,+)`.
