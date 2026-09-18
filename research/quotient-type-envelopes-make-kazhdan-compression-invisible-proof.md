---
rg: 2
id: quotient-type-envelopes-make-kazhdan-compression-invisible-proof
kind: route
title: Collapse the chain in characteristic finite quotients, transport commutation through the Kazhdan constant of the graph vector, and absorb flexible padding
target: quotient-type-envelopes-make-kazhdan-compression-invisible
requires: []
artifacts:
  - research/quotient-type-envelopes-make-kazhdan-compression-invisible.md
---

Notation is that of the claim.
- `psi = (m -> u m u^-1)` is an automorphism of `M`, since `u M u^-1 = M`.
- `L_j = u^-j L u^j` for `j >= 0`, so `L_0 = L` and `N = ⋃_j L_j`.
- `d_H(a,b) = |{y : a y != b y}| / |Omega|` on `Sym(Omega)`. It is bi-invariant.

Standard facts used:
- A finitely generated group has only finitely many subgroups of each finite index,
  since each is determined by a homomorphism to a finite symmetric group on its cosets.
- A Kazhdan pair `(S, kappa)` for `L` means: `S` is finite and generates `L`, and every
  unitary representation with no nonzero invariant vector satisfies
  `max_{s in S} ||pi(s) w - w|| >= kappa ||w||` for all `w` (Bekka–de la Harpe–Valette,
  Ch. 1).
- `S_U` is the metric ultraproduct. Two sequences represent the same element iff their
  `d_H` tends to `0` along `U`.

## 1. (Q1) The chain collapses in every finite quotient of `M`

**The chain.** From `u L u^-1 <= L`, conjugating by `u^-j` gives `L_{j-1} <= L_j`, so the
`L_j` increase. Each `L_j` lies in `M`, because `M` is normalized by `u`. Also
`psi(L_j) = L_{j-1} <= L_j`, so each `L_j` is itself compressed by `u`.

**Characteristic cofinal subgroups.** For `d >= 1` let `M_d` be the intersection of all
normal subgroups of `M` of index at most `d`. There are finitely many of them, so `M_d`
has finite index. It is characteristic, so `psi(M_d) = M_d`. Every finite-index normal
subgroup `R` of `M` contains `M_{[M:R]}`.

**Image equality.** Fix `d` and let `bar` denote the image in the finite group `M/M_d`.
`psi` induces an automorphism `psi_bar` of `M/M_d`. For any `H <= M` with `psi(H) <= H`,

```text
psi_bar(H_bar) = psi(H)_bar <= H_bar,   and   |psi_bar(H_bar)| = |H_bar|,
```

so `psi(H) M_d = H M_d`. Apply this to `H = L_j`: `L_{j-1} M_d = L_j M_d` for all `j >= 1`.
By induction `L_j M_d = L M_d = psi(L) M_d` for all `j`, hence `N M_d = psi(L) M_d`.

**Every finite quotient.** Let `q : M -> Q` be onto a finite group, and put `R = ker q`.
Then `R ⊇ M_d` with `d = |Q|`, so `q(N) = q(L) = q(psi(L)) = q(u L u^-1)`.

**Closure.** Since `cl_M(H) = ⋂_R H R` over finite-index normal `R`, this says
`N ⊆ cl_M(u L u^-1)`. If `u L u^-1 != L`, any `l in L \ u L u^-1` lies in the closure but
not in the subgroup, so `u L u^-1` is not separable.

Property (T) is not used in this section.

## 2. (Q2) Kazhdan uniformity of the graph vector

Let `rho : M -> Sym(Omega)` be an honest action on a finite set, and let `c in Sym(Omega)`.

**The representation.** `L` acts on `Omega` through `y -> rho(u y u^-1)`, a homomorphism
because `u y u^-1 in M`. Let `pi` be the resulting unitary representation of `L` on
`l^2(Omega x Omega)`, acting diagonally:

```text
(pi(y) f)(a, b) = f(g^-1 a, g^-1 b),   g = rho(u y u^-1).
```

**The graph vector.** Put `v = |Omega|^-1/2 · 1_{Gamma_c}`, where
`Gamma_c = {(a, c a) : a in Omega}`. Then `pi(y) v` is the normalized indicator of
`{(g a, g c a)} = Gamma_{g c g^-1}`. Two graphs of permutations meet exactly over the points
where the permutations agree, so

```text
||pi(y) v - v||^2 = 2 d_H(g c g^-1, c) = 2 d_H(c g, g c),
```

using right invariance of `d_H` (multiply both permutations on the right by `g`).

**The Kazhdan estimate.** Let `P` be the orthogonal projection onto the `pi(L)`-invariant
vectors, and put `w = v - P v`. The invariant subspace and its orthogonal complement are
both `pi`-invariant, and the complement contains no nonzero invariant vector. So

```text
kappa ||w|| <= max_s ||pi(s) w - w|| = max_s ||pi(s) v - v|| = (2 delta)^{1/2},
```

where `delta = max_{s in S} d_H(c rho(u s u^-1), rho(u s u^-1) c)`. For every `y in L`,

```text
||pi(y) v - v|| = ||pi(y) w - w|| <= 2 ||w|| <= 2 (2 delta)^{1/2} / kappa,
```

and therefore `d_H(c g, g c) <= 4 delta / kappa^2` for every `g in rho(u L u^-1)`.

**Passing to the chain.** `rho(M)` is a finite quotient of `M`. By Section 1,
`rho(N) = rho(u L u^-1)`. So for every `x in N`, `rho(x) = g` for some `g in rho(u L u^-1)`,
and

```text
d_H(c rho(x), rho(x) c) <= 4 delta / kappa^2.                        (Q2)
```

The bound is uniform in `x`, `Omega`, `rho` and `c`. This uniformity is the only use of
property (T).

## 3. (Q3) Transfer to the flexible ultraproduct

Let `sigma` be quotient-type on `M`, with `Omega'_n ⊇ Omega_n` and honest actions
`rho_n : M -> Sym(Omega'_n)`. Put `eps_n = |Omega'_n \ Omega_n| / |Omega_n|`, so
`eps_n -> 0` along `U`.

**Representatives.** For `m in M`, the partial injection `y -> rho_n(m) y` on
`{y in Omega_n : rho_n(m) y in Omega_n}` extends to some `tau_n(m) in Sym(Omega_n)`, and
`sigma(m) = [tau_n(m)]_U`. Since `rho_n(m)` is a bijection of `Omega'_n`, at most
`eps_n |Omega_n|` points `y in Omega_n` have `rho_n(m) y notin Omega_n`. This count is
uniform in `m`.

**Padding the centralizing element.** Let `c = [c_n]_U` commute with `sigma(u L u^-1)`,
with `c_n in Sym(Omega_n)`. Let `c'_n in Sym(Omega'_n)` be `c_n` on `Omega_n` and the
identity off it.

For `g in M`, a point `y in Omega'_n` with `c'_n rho_n(g) y != rho_n(g) c'_n y` falls into
one of four cases:
- `y notin Omega_n`;
- `y in Omega_n` and `rho_n(g) y notin Omega_n`;
- `y in Omega_n` and `rho_n(g) c_n y notin Omega_n`;
- none of the above, and then `c_n tau_n(g) y != tau_n(g) c_n y`.

Each of the first three cases has at most `eps_n |Omega_n|` points. For the third this uses
that `c_n` permutes `Omega_n`. So

```text
d_H^{Omega'_n}(c'_n rho_n(g), rho_n(g) c'_n) <= 3 eps_n + d_H^{Omega_n}(c_n tau_n(g), tau_n(g) c_n).   (3.1)
```

**Applying (Q2).** Take `g = u s u^-1` for `s in S`. Then `sigma(g)` commutes with `c`, so
the right side of (3.1) tends to `0` along `U`. Hence
`delta'_n = max_s d_H^{Omega'_n}(c'_n rho_n(u s u^-1), rho_n(u s u^-1) c'_n) -> 0`.

Apply (Q2) to the honest action `rho_n` on `Omega'_n` and to `c'_n`. For every `x in N`,

```text
d_H^{Omega'_n}(c'_n rho_n(x), rho_n(x) c'_n) <= 4 delta'_n / kappa^2 -> 0.
```

**Back to `Omega_n`.** A point `y in Omega_n` with `c_n tau_n(x) y != tau_n(x) c_n y` has
one of three properties:
- `rho_n(x) y notin Omega_n`;
- `rho_n(x) c_n y notin Omega_n`;
- `c'_n rho_n(x) y != rho_n(x) c'_n y`.

Hence

```text
d_H^{Omega_n}(c_n tau_n(x), tau_n(x) c_n) <= 2 eps_n + (1 + eps_n) · 4 delta'_n / kappa^2 -> 0,
```

so `c` commutes with `sigma(x)`. This proves `C(sigma(u L u^-1)) ⊆ C(sigma(N))`. The
constant `kappa` does not depend on `n`, which is where the uniformity of (Q2) is consumed.

**Equalities.** From `u L u^-1 <= L <= N`,

```text
C(sigma(u L u^-1)) ⊆ C(sigma(N)) ⊆ C(sigma(L)) ⊆ C(sigma(u L u^-1)),
```

so all three centralizers are equal.

**Normalization.** Let `C = C_{S_U}(sigma(L))`. Then
`sigma(u) C sigma(u)^-1 = C_{S_U}(sigma(u L u^-1)) = C`. Conjugating this identity by
`sigma(u)^-1` gives `sigma(u)^-1 C sigma(u) = C`.

## 4. (Q4), (Q5), and the level models of mapping tori

**(Q4).** Let `c in C_G(u L u^-1)` and `x in N`. Then `sigma(c)` commutes with
`sigma(u L u^-1)`. By (Q3) it commutes with `sigma(N)`, so `sigma([c, x]) = 1`. For
`c in C_G(L)`, the element `u c u^-1` lies in `C_G(u L u^-1)`, and `L ⊆ N`. So
`sigma([u c u^-1, l]) = 1` for all `l in L`.

**(Q5).** If `sigma` is injective, (Q4) gives `[c, x] = 1` in `G` for all
`c in C_G(u L u^-1)` and `x in N`. Then

```text
C_G(u L u^-1) ⊆ C_G(N) ⊆ C_G(L) ⊆ C_G(u L u^-1),
```

and `u C_G(L) u^-1 = C_G(u L u^-1) = C_G(L)`.

**Level models are quotient-type.** Let `M` be finitely generated and residually finite,
`psi in Aut(M)`, and `G = M ⋊_psi Z` with `u` the generator, so `u a u^-1 = psi(a)`.

Fix a finite set `F ⊆ M \ {1}` and `m >= 1`. Choose a finite-index normal `M_1` with
`M_1 ∩ F = ∅`, and put `M_0 = ⋂_{|i| < m} psi^i(M_1)`. This is finite-index and normal.
Let `pi` be the regular action of `M` on `X = M / M_0`.

On `Omega = X × Z/m` define

```text
sigma(a)(x, j) = (pi(psi^-j(a)) x, j)   (a in M, representative 0 <= j < m),
sigma(u)(x, j) = (x, j + 1),
sigma(a u^k) = sigma(a) sigma(u)^k.
```

- *Honest on `M`.* On each level `a -> pi ∘ psi^-j (a)` is an action, so `sigma|_M` is an
  honest action of `M` on `Omega`. This is the exact case of quotient-type, with
  `Omega' = Omega`.
- *Almost multiplicative.* `sigma(u)^k sigma(b) sigma(u)^-k (x, j) = (pi(psi^{-(j-k)}(b)) x, j)`
  whenever `j - k` does not wrap modulo `m`. This agrees with `sigma(psi^k(b))`. So
  `sigma(a u^k) sigma(b u^l)` and `sigma(a u^k b u^l)` differ on at most a `|k|/m`
  fraction of the points.
- *Asymptotically free.* For `a in F` and `0 <= j < m`, `psi^-j(a) notin M_0`, because
  `M_0 ⊆ psi^-j(M_1)` and `a notin M_1`. So `pi(psi^-j(a))` has no fixed point on `X`,
  and `sigma(a)` has no fixed point. For `0 < |k| < m`, `sigma(a u^k)` shifts every level,
  so it has no fixed point either.

Letting `F` exhaust `M \ {1}` and `m -> infinity` gives a sofic embedding of `G` that is
quotient-type on `M`. The same holds for any model that restricts to `M` as a disjoint
union, over levels, of such honest actions, up to an `o(1)` set of points. By (Q5), the
defect at `u` vanishes in every such `G`.

For the mapping torus itself this also follows from
`locally-residually-finite-targets-kill-compression-defects`: a finitely generated
residually finite group extended by `Z` is residually finite, via the characteristic
`M_d` of Section 1. The new content is that the kill survives two things: `o(1)`
perturbation of the envelope model, and passage to any larger group, for example a
centralizing HNN extension, whose approximations restrict to such models on `M`.

## 5. Remarks

- Property (T) is used only in (Q2), and only for `L`. Neither `M` nor `G` nor `u` needs
  it, and no infranormality is assumed.
- Finite generation of `M` is used only in Section 1, to make `M_d` finite-index and
  characteristic. The honest finite actions in the quotient-type hypothesis supply the
  finite quotients.
- **Sharpness of the hypothesis.** In the centralizing HNN
  `H = <G, c | [c, u L u^-1] = 1>` with `u L u^-1 != L`, Britton's lemma gives
  `[c, l] != 1` for `l in L \ u L u^-1`. By (Q4), no sofic approximation of `H` is
  quotient-type on `M`. So soficity of `H`, and with it any refutation of (CKN) through
  `H`, needs approximations that are flexibly unstable on `M`.
- Envelopes without finite quotients, such as the `K` of `(EK1)`, have no honest finite
  actions beyond the trivial one. For them the hypothesis is vacuous, and nothing here
  bears on `(EK1)`.
