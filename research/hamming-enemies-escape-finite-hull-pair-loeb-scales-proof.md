---
rg: 2
id: hamming-enemies-escape-finite-hull-pair-loeb-scales-proof
kind: route
title: Proof that flat and finite-hull Gamma-commutant pieces of sofic models of the Theorem E group commute with sigma(E)
target: hamming-enemies-escape-finite-hull-pair-loeb-scales
requires:
  - kun-thom-sofic-centralizer-normalization
  - kt-sofic-monomial-commutant-core-is-normalized
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

We use the notation of `hamming-enemies-escape-finite-hull-pair-loeb-scales`.
The imports are Kun--Thom Theorem 4.1 (normalization of
`C_(S_U)(sigma(Gamma))`) and Theorem C (for a sofic p.m.p. action, meaning
Păunescu's crossed-product notion, `L^∞(X)^Gamma` is `G`-invariant). Both
are quoted verbatim in `research/artifacts/kun-thom-2608-06222-verified.md`.
Their hypotheses (`Gamma`, `G` Kazhdan and `Gamma` infranormal) hold by
Kun--Thom Theorem E.

## 0. Normal closure

**Lemma 0.** The normal closure `N` of `Gamma` in `G` contains `E`.

*Proof.* `N` is normal and contains every `e_ij(1)`. For `a` in `R`,
`e_ik(a)` is in `E ⊆ G`. The Steinberg relation for distinct `i, j, k` gives

```text
[e_ik(a), e_kj(1)] = e_ij(a) .
```

The left side is `h · e_kj(1) h^-1 · e_kj(1)^-1` with `h = e_ik(a)`, which
lies in `N`. So `N` contains every `e_ij(a)`, `a` in `R`, and these generate
`E`. Here `r >= 3` is used. ∎

**Lemma 0'.** Let `G` act on an abelian von Neumann algebra `A`, and suppose
`A^Gamma` is `G`-invariant as a set. Then `A^Gamma = A^N ⊆ A^E`.

*Proof.* `h · A^Gamma = A^(h Gamma h^-1)`. If `h · A^Gamma ⊆ A^Gamma` for every
`h`, then applying this to `h^-1` gives `h · A^Gamma = A^Gamma`. So
`A^Gamma = A^(h Gamma h^-1)` for every `h`. Each `a` in `A^Gamma` is therefore
fixed by every conjugate of `Gamma`, hence by `N ⊇ E` (Lemma 0). ∎

## 1. Part A

Let `rho : V_T -> S_U` be the restriction of a sofic representation, hence
injective. Suppose `C_(S_U)(rho(Lambda)) != C_(S_U)(rho(Gamma))`, and suppose
`sigma : G -> S_U` is a sofic representation with `sigma|_(V_T) = rho`.

- Theorem 4.1 applies to `sigma`, so `sigma(t)` normalizes
  `C := C_(S_U)(sigma(Gamma))`.
- Also `sigma(t) C sigma(t)^-1 = C_(S_U)(sigma(t Gamma t^-1)) = C_(S_U)(rho(Lambda))`.
- Hence `C_(S_U)(rho(Lambda)) = C_(S_U)(rho(Gamma))`, a contradiction.

**The Pauli walls satisfy the hypothesis.** Let `tau` be a sofic
representation of `Pi_T = P_X ⋊ V_T` and put `rho = tau|_(V_T)`. Let `x_0` be
the base coset `Gamma` in `X = V_T/Gamma`, and let `p_x` be the Pauli
`X`-type generator at site `x`. `V_T` permutes the sites:
`g p_x g^-1 = p_(g x)`.

- For `lambda = t gamma t^-1` in `Lambda`, `lambda t x_0 = t gamma x_0 = t x_0`.
  So `tau(p_(t x_0))` commutes with `rho(Lambda)`.
- Choose `gamma` in `Gamma \ Lambda`, which is nonempty because the
  compression is strict. Then `t^-1 gamma t` is not in `Gamma`, so
  `gamma t x_0 != t x_0`. Hence `gamma p_(t x_0) gamma^-1 = p_(gamma t x_0)`,
  which differs from `p_(t x_0)` in `Pi_T`.
- Since `tau` is injective, `tau(p_(t x_0))` does not commute with
  `rho(gamma)`.

So `tau(p_(t x_0))` lies in `C(rho(Lambda)) \ C(rho(Gamma))`, and no sofic
representation of `G` restricts to `rho`. ∎

*Exact failure step.* An extension would have to make `sigma(t)` normalize the
permutation centralizer of `sigma(Gamma)`. The wall lamp is exactly a
permutation centralizer element that `t` moves out.


## 2. Part B

Let `psi_n(g) = phi_n(g) × phi_n(g)` act on `W_n = Y_n × Y_n`. Fix a pair
scale `Z`, satisfying (Z1)-(Z3). Let `f` be `psi(Gamma)`-invariant and
`(Z, K)`-dominated. Choose representatives `f_n` that vanish off `Z_n` and
satisfy `|f_n| <= K (|Y_n|/|Z_n|)^(1/2)` there, for `U`-almost every `n`. The
norm on `H` is `||f||^2 = lim_U (1/|Y_n|) sum |f_n|^2`, and `psi(g) f` is the
class of `f_n ∘ psi_n(g)^-1`.

**Step 1 (a sofic representation on Z).** Define a permutation `psi'_n(g)` of
`Z_n`: it equals `psi_n(g)` on `Z_n ∩ psi_n(g)^-1 Z_n`, and on the rest it is
any bijection onto `Z_n \ psi_n(g) Z_n`. Put `psi'_n(e) = id`, which is
consistent because `phi_n(e) = id`. By (Z1), `psi'_n(g)` agrees with
`psi_n(g)` off a set `O_n(g)` of size `o(|Z_n|)`.

- *Multiplicativity.* Let `G_n(g,h) = { b in Y_n : phi_n(g) phi_n(h) b = phi_n(gh) b }`,
  and let `B_n` be its complement, so `|B_n| = o(|Y_n|)`. Let `w` be in `Z_n`
  and avoid all of the following:
  - `O_n(h)`;
  - `psi_n(h)^-1 O_n(g)`;
  - `O_n(gh)`;
  - `(B_n × Y_n) ∪ (Y_n × B_n)`.

  Then `psi'_n(g) psi'_n(h) w = psi_n(g) psi_n(h) w = psi_n(gh) w = psi'_n(gh) w`,
  because both coordinates of `w` lie in `G_n(g,h)`. The first three
  exceptional sets have size `o(|Z_n|)`. The last meets `Z_n` in `o(|Z_n|)`
  points by (Z3). So `psi'` is a homomorphism `G -> S_U(Z)`.
- *Canonical trace.* Let `g != e`. A fixed point of `psi'_n(g)` outside
  `O_n(g)` is a fixed point of `psi_n(g)`, so it lies in
  `Fix phi_n(g) × Fix phi_n(g)`. By (Z2) there are `o(|Z_n|)` of them. So
  `tr psi'(g) = 0`.

**Step 2 (the scaled function).** Put
`g_n = (|Z_n|/|Y_n|)^(1/2) f_n|_(Z_n)`. Then `|g_n| <= K`, so
`g = [g_n]` lies in the diagonal ultraproduct
`D^Z = prod_U (D_(Z_n), tr)`, where `tr` is normalized on `Z_n`. For any
function `h_n` on `Z_n`,

```text
(1/|Z_n|) sum_(Z_n) |(|Z_n|/|Y_n|)^(1/2) h_n|^2  =  (1/|Y_n|) sum_(Z_n) |h_n|^2 .   (2.1)
```

For `s` in `Gamma`, `g_n ∘ psi'_n(s)^-1` and the scaled
`f_n ∘ psi_n(s)^-1` agree off `psi'_n(s) O_n(s)`, and on that set both are
bounded by `K`. By (2.1),

```text
|| psi'(s) g psi'(s)^* - g ||_(2,Z)  <=  || psi(s) f - f ||_H + 2K (|O_n(s)|/|Z_n|)^(1/2)  ->  0 .
```

Also `psi(s) f - f` vanishes off `Z_n ∪ psi_n(s) Z_n`, and its part off
`Z_n` is controlled the same way. Hence `g` commutes with `psi'(Gamma)` in
`prod_U M_(Z_n)`.

**Step 3 (a sofic p.m.p. action, and Theorem C).**

- Let `A` be the von Neumann algebra generated by
  `{ psi'(h) g psi'(h)^* : h in G }` inside `D^Z`. It is abelian and
  countably generated, and conjugation by `psi'(G)` preserves it. With the
  trace, `A = L^∞(X, mu)` for a standard probability space, and
  `alpha_h(a) = psi'(h) a psi'(h)^*` is a p.m.p. action `G ↷ X`.
- For `a` in `D^Z` and `h != e`,
  `|tr(a psi'(h))| <= ||a|| · |Fix psi'_n(h)| / |Z_n| -> 0` (Step 1). So the
  map `sum a_h lambda_h -> sum a_h psi'(h)` from the algebraic crossed product
  preserves the trace `tau(sum a_h lambda_h) = tau(a_e)`. It therefore extends
  to a trace-preserving `*`-isomorphism of `L^∞(X) ⋊ G` onto
  `W^*(A ∪ psi'(G))`, which sends `L^∞(X)` into the diagonal and `G` into
  permutations. This is Păunescu's definition, so `G ↷ X` is a sofic p.m.p.
  action.
- By Theorem C, `A^Gamma` is `G`-invariant. `g` lies in `A^Gamma` by Step 2.
  By Lemma 0', `g` is fixed by `alpha(E)`.

**Step 4 (back to f).** For `e` in `E`, the estimate of Step 2 read backwards
gives

```text
|| psi(e) f - f ||_H  <=  || psi'(e) g psi'(e)^* - g ||_(2,Z) + 2K (|O_n(e)|/|Z_n|)^(1/2)  ->  0 .
```

An extra term comes from the part of `psi(e) f` supported on
`psi_n(e) Z_n \ Z_n`. That part is at most
`(1/|Y_n|) |psi_n(e) Z_n Δ Z_n| · c^2 |Y_n|/|Z_n| -> 0` by (Z1), where
`c = K`. So `f` is `psi(E)`-invariant.

**Elements of R.** Let `x = [x_n]` be in `R` with entry functions `f_n`. The
matrix `phi_n(g) x_n phi_n(g)^-1` has entry function `f_n ∘ psi_n(g)^-1`, so

```text
|| [sigma(g), x] ||_2 = || psi(g) f - f ||_H .                                   (2.2)
```

So `f` is `psi(Gamma)`-invariant. If `f` is `(Z, K)`-dominated, then `x`
commutes with `sigma(E)`. This covers the flat case `Z = W`, where
`psi' = psi`, (Z2) holds because `(|Fix|/|Y_n|)^2 -> 0`, and (Z3) holds with
`eta = eps/2`. ∎

## 3. Part C

Let `theta(s) = 1` for `s <= 1`, `theta(s) = 2 - s` for `1 <= s <= 2`, and
`theta(s) = 0` for `s >= 2`. Put `c_n = K (|Y_n|/|Z_n|)^(1/2)` and

```text
chi_(Z,K)(f)_n = 1_(Z_n) · F_n(f_n),     F_n(z) = z theta(|z|/c_n)  (entrywise).
```

- `F_n` is 3-Lipschitz on `C`: it is radial, `z -> z k(|z|)` with
  `0 <= k <= 1`, and `s |k'(s)| <= 2`.
- `F_n` commutes with coordinate permutations. Hence
  `|| psi(s) F(f) - F(f) || <= 3 || psi(s) f - f || = 0` for `s` in `Gamma`.
- Multiplying by `1_Z` costs at most
  `(1/|Y_n|) |psi_n(s) Z_n Δ Z_n| · (2 c_n)^2 = 4K^2 |psi_n(s) Z_n Δ Z_n| / |Z_n| -> 0`,
  by (Z1).

So `chi_(Z,K)(f)` is `psi(Gamma)`-invariant and `(Z, 2K)`-dominated, and by
Part B it is `psi(E)`-invariant. Let `x` be an enemy, with
`delta = ||[x, sigma(u)]||_2 = ||psi(u) f - f||` (by (2.2)). Put
`h = f - chi_(Z,K)(f)`. Then

```text
psi(u) f - f = psi(u) h - h ,   so   delta <= 2 ||h|| .
```

With `Z = W`, `|h_n| <= |f_n|`, and `h_n` is supported on entries with
`|f_n| > K |Y_n|^(-1/2)`. So those entries carry 2-norm mass at least
`delta/2` for every `K`. ∎

## 4. Calibration and checks

- **Nothing false is proved about small projections.** A nonzero flat `x`
  has support of positive density in `W_n`, because
  `(1/|Y_n|) sum |f_n|^2 <= K^2 |supp f_n| / |Y_n|^2`. For example, a
  `Gamma`-invariant block partition into blocks of size `m_n = o(|Y_n|)`
  gives an averaging projection of trace `1/m_n -> 0`, which is 0 in `M`. At
  every scale, dominated vectors are exactly the vectors of the probability
  space `(Z_n, uniform)`. This is the only place where the finite-measure
  hypothesis of Theorem C is used, and it is used honestly.
- **The coset pattern is excluded from the hypotheses, as it must be.** For
  `G ↷ G/Gamma` with counting measure, `delta_(x_0)` is `Gamma`-invariant and
  moved by `u`. The corresponding pair set violates (Z1) at its own density.
  Such sets are exactly the infinite-hull walls of Part C.
- **Kazhdan is load-bearing.** It enters only through Theorems C and 4.1. For
  the dyadic (non-Kazhdan) analogue, Theorem C is unavailable, and sofic
  enemies are not excluded.
- **Relation to the monomial core.** A graph of a permutation commuting with
  `sigma(G)` is a pair scale. Graphs of centralizer permutations of
  `sigma(Gamma)` that `u` moves are not pair scales. They are handled by
  Kun--Thom 4.1 (`kt-sofic-monomial-commutant-core-is-normalized`), which is
  where Part A comes from. So Part B extends the core statement across the
  Fourier-spread (flat) directions. It does not replace it at the monomial
  scale.
