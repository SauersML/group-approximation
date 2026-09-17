# Expand the Clifford correlation, then Cauchy--Schwarz against merged right SDP vectors

*Attempt artifact (2026-09-17), formerly route `clifford-long-codes-pairing-vector-proof` into `clifford-long-codes-realize-pairing-value-in-binary-noise-test`, requires [sd-rich-and-unique-games-sos-gaps-interconvert, unique-games-entangled-value-approximable-by-sdp]. Demoted from the graph together with the other two routes of this result because referee lenses 1 and 2 of three returned *refuted* on `entanglement-sound-soundness-cannot-prove-ugc` (missing outer completeness hypothesis in B3; overclaimed class kill for 2-to-1 soundness); lens 3 returned *survives*. See `## Attempts` in the claim. Restore it as a route once the statements are corrected and a full referee pass survives.*

**C1.**

- Anticommutation gives `gamma(w)^2 = sum_i w_i^2 I`, and `gamma` is Hermitian.
- The Jordan--Wigner generators are traceless, and so are `gamma_i gamma_j` for
  `i != j`, since they are Pauli strings other than the identity. So
  `tau(gamma(w) gamma(w')) = <w, w'>`.
- Orthogonality of the `w_(u,x)` gives `|sum_x (-1)^(X_x) w_(u,x)|^2 = 1`, so
  `F_u(X)` is a Hermitian unitary.
- Adding `1` to `X` flips every sign, so `F_u(X + 1) = -F_u(X)`. With answer bit
  `a` defined by `F = (-1)^a`, this is the folding `F(X + 1) = F(X) + 1`.

**C2.** For Hermitian `A` and `B` on `C^d`, and `phi` the maximally entangled
state, `<phi| A (x) conj(B) |phi> = tau(A B)`. Equal answers therefore have
probability `(1 + tau(F_u(X) F_v(Y)))/2`. By C1,

```text
tau(F_u(X) F_v(Y)) = sum_(x,y) (-1)^(X_x + Y_y) <w_(u,x), w_(v,y)>.
```

The three noise steps are independent and each has correlation `rho` on `Z_2`,
so

```text
E[(-1)^(X_x + Y_y)] = rho^3 [pi_(u,b)(x) = pi_(v,b)(y)].
```

Hence the expected correlation is `rho^3 E_b E_(u,v|b) sum_j <W_(u,b,j), W_(v,b,j)>`.
Because `u` and `v` are independent given `b`, this equals
`rho^3 E_b sum_j |E_(u|b) W_(u,b,j)|^2`. The strategy is a finite-dimensional
entangled strategy, so the lower bound on `val*` follows.

**C3.** Take SDP 1 vectors for `U` (item 1 of `unique-games-entangled-value-approximable-by-sdp`):

- `u_(u,a)` orthogonal over `a` with `sum_a u_(u,a) = z`, `|z| = 1`, hence
  total squared mass 1;
- `v_(v,c)` likewise;
- `<u_(u,a), v_(v,c)> >= 0` for all `u, a, v, c`.

Put `w_(u,x) = u_(u,x)`. A right vertex of `Psi(U)` is `b = (v, sigma)`, with
`pi_(u,b) = sigma o phi_(uv)` and `u|b` distributed as `u|v`. Put
`V_j = sum_(c in sigma^(-1)(j)) v_(v,c)`, so `sum_j |V_j|^2 = 1`.

By Cauchy--Schwarz in `(R^D)^k`,
`sum_j |E_u W_(u,b,j)|^2 >= (E_(u|v) sum_j <W_(u,b,j), V_j>)^2`.
Expanding the inner sum gives
`sum_x sum_(c: sigma(c) = sigma(phi_(uv)(x))) <u_(u,x), v_(v,c)>`. Keeping only
`c = phi_(uv)(x)` and using nonnegativity, this is at least
`s_(uv) = sum_x <u_(u,x), v_(v,phi_(uv)(x))> >= 0`. So

```text
E_b sum_j |E_(u|b) W_(u,b,j)|^2 >= E_v (E_(u|v) s_(uv))^2 >= (E_(uv) s_(uv))^2 = omega_sdp1(U)^2
```

by Jensen, for the optimal SDP solution.

**C4.** KRT p. 6, quoted in the citation route, supplies unique games with
alphabet `k`, `omega_sdp1 >= 1 - 9 eta` and `val <= 2/k^eta`, in the two-prover
form of their footnote 2. For even `k` write `k = 2k'`.

- Part (a) of `sd-rich-and-unique-games-sos-gaps-interconvert` gives
  `val(Psi(U)) <= 2 val(U) <= 4/k^eta`, and makes every left vertex fully rich.
- C2 and C3 give `val* >= (1 + rho^3 (1 - 9 eta)^2)/2`.
- Dictators `F_u(X) = X_(a(u))` on a satisfying labeling accept with probability
  `(1 + rho^3)/2` by the same correlation computation.

Given `delta < (1 + rho^3)/2` and `eta' > 0`, choose `eta` so small that
`(1 + rho^3 (1 - 9 eta)^2)/2 > delta`, then `k` so large that `4/k^eta <= eta'`.
This refutes `D_cl` at `(delta, eta')`.
