---
rg: 2
id: sln-relators-force-linear-commutator-growth-proof
kind: route
title: Rank is subadditive over van Kampen cells, and the dyadic shortcut filling of [u^L,v^L] in SL_n(Z), n >= 5, has linear area
target: sln-relators-force-linear-commutator-growth
requires: []
---

Notation as in the claim. `Area(w)` is the least number of relator cells in a van Kampen diagram
for a null-homotopic word `w`. `delta` is the Dehn function of `<S | R>`.

**Step 1 (rank-area inequality).** Suppose `w` is trivial in `Gamma` with `Area(w) = A`. Then in the
free group `w = prod_(i <= A) g_i r_i^(+-1) g_i^(-1)`. Two facts give the bound:
- `XY - I = X(Y - I) + (X - I)`, so `rank(XY - I) <= rank(X - I) + rank(Y - I)`;
- rank of `X - I` is invariant under conjugation and inversion.

Hence `rank(rho(w) - I) <= k A`. This is the rank form of `hs-dehn-modulus-bounded-by-dehn-function`.
The same bound holds for `rank(rho(w_1) - rho(w_2))` whenever `w_1 = w_2` in `Gamma`, because this
equals `rank(rho(w_1 w_2^(-1)) - I)`.

Changing the finite presentation changes `k` by a constant factor, since each old relator has
bounded area in the new presentation. So the result does not depend on the presentation.

**Step 2 (short words for dyadic powers).** Fix an elementary matrix `u`. By
Lubotzky-Mozes-Raghunathan (`n >= 3`) there is `C_0` and there are words `w_j` with
`w_j = u^(2^j)` in `Gamma`, `|w_j| <= C_0 (j + 1)`, and `w_0 = u`.

**Step 3 (dyadic conversion, linear area).** For `J >= 1` the word `u^(2^J) w_J^(-1)` has area at most
`C_2 2^J`. Start from `w_0^(2^J)`. At stage `j = 0, ..., J-1` the word is `w_j^(2^(J-j))`. Replace
each of its `2^(J-1-j)` adjacent pairs `w_j w_j` by `w_(j+1)`. Each replacement uses one diagram for
the null-homotopic word `w_j w_j w_(j+1)^(-1)`, which has length `<= 3 C_0 (j + 2)`. By Young
(`n >= 5`), `delta(t) <= C_1 t^2`. So

```text
Area(u^(2^J) w_J^(-1)) <= sum_(j < J) 2^(J-1-j) C_1 (3 C_0 (j+2))^2 <= C_2 2^J,
```

because `sum_j (j+2)^2 / 2^j` converges.

For general `L`, write `L = sum_(j in E) 2^j` in binary and put `W_L = prod_(j in E) w_j`. The free
identity `u^L = prod_(j in E) u^(2^j)` then gives
`Area(u^L W_L^(-1)) <= C_2 sum_(j in E) 2^j <= C_2 L`. The word `W_L` has length
`<= C_0 (log_2 L + 2)^2`.

**Step 4 (the commutator).** Let `u, v` be commuting elementary matrices and `W_L(u)`, `W_L(v)`
the words from Step 3. The word `[W_L(u), W_L(v)]` is null-homotopic, because `u^L` and `v^L`
commute. Its length is `<= 4 C_0 (log_2 L + 2)^2`, so its area is `<= 16 C_1 C_0^2 (log_2 L + 2)^4`.

Replace the four blocks `u^(+-L)` and `v^(+-L)` of `[u^L, v^L]` by `W_L(u)^(+-1)` and
`W_L(v)^(+-1)`. This gives

```text
Area([u^L, v^L]) <= 4 C_2 L + 16 C_1 C_0^2 (log_2 L + 2)^4 <= C_n L.
```

Step 1 then gives `phi(L) <= C_n k L` and `rank(rho(u)^L - rho(W_L)) <= C_2 k L`. QED.

**Step 5 (transfer to `Gamma_n`, `g >= 5`).** Embed `SL_g(R)` into `Sp_(2g)(R)` by
`A -> diag(A, A^(-T))`. The maximal compact `SO(g)` maps into `U(g)`, and
`det: U(g) -> S^1` induces `pi_1(Sp_(2g)(R)) = Z`. On `SO(g)`, `det = 1`, so the covering restricts to
the trivial covering over `SL_g(R)` and `SL_g(Z)` lifts to a subgroup `j(SL_g(Z))` of `Gamma_n`.

The images of the finitely many relators of `SL_g(Z)` are trivial in `Gamma_n`. So they have area at
most some `A_0` there, and `rho o j` is a rank-`A_0 k` tuple of `SL_g(Z)`. Steps 1-4 apply, with
`SL_5(Z)` inside `SL_g(Z)` whenever `g >= 5`.

**Step 6 (lower bound in `P`).** The tuples of `sl2-relators-do-not-force-linear-commutator-growth`
have all relator ranks `<= 24` and `phi(L) = 12 L^2`. So Step 1 forces
`Area_P([b^L, c^L]) >= L^2 / 2`. In `P`, Step 3 fails at the step where `delta_P` is exponential.

**Where the argument would fail for `SL_3`.** Only in the use of `delta(t) <= C_1 t^2` in Steps 3
and 4. Polynomial bounds on the specific loops `w_j w_j w_(j+1)^(-1)` and `[W_L(u), W_L(v)]` would
suffice. Any bound with `sum_j Area(w_j w_j w_(j+1)^(-1)) / 2^j < infinity` would suffice for Step 3.
