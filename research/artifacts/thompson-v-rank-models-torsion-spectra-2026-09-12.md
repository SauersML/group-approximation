# Torsion spectra of rank models of Thompson's V

Lane `w4-gate-v2`, 2026-09-12. This artifact supports
`v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`. Later sections record calibrations for the V
rank gate `thompson-v-has-no-nontrivial-f2-rank-model` and where it stops.

## 0. Setting

- `X = {0,1}^N`, cylinders `[w]`, and `V` acting by prefix replacement, as in
  `research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md` (cited below as [COV]).
- `F` is a field, `M` a rank ultraproduct of matrix algebras over `F`, and `rk` its rank function.
  A *rank model* of `V` is a group homomorphism `sigma : V -> M^x`.
- `p` is an odd prime different from the characteristic of `F`. Characteristic two is included.
- `F'` is `F` with the `p`-th roots of unity adjoined, and `M'` is the rank ultraproduct over `F'`. It
  contains `M`, and ranks do not change under the extension, since matrix rank is field-independent.

**Definition.** A *clopen `p`-cycle* is an element `g` of `V` with disjoint nonempty clopens
`A_0, ..., A_(p-1)` whose complement `D` is nonempty, such that:
- `g` maps each `A_k` onto `A_(k+1)` (indices mod `p`);
- `g^p = 1`;
- `g` is the identity on `D`.

A finite subgroup `P <= V` is a *clopen-cycle subgroup* if it is elementary abelian of exponent `p` and
every nonidentity element of `P` is a clopen `p`-cycle.

## 1. Trivial-plus-free spectra

**Lemma 1.1 (conjugacy).** Any two clopen `p`-cycles are conjugate in `V`.

*Proof.* Let `g` have pieces `A_k` and complement `D`, and `g'` have pieces `A'_k` and complement `D'`.
- Any two nonempty clopens are related by a prefix bijection. Refine both into equally many cylinders
  and match them, as in [COV] Lemma 2.2. Choose such bijections `phi : A_0 -> A'_0` and `psi : D -> D'`.
- Define `h` by `h = g'^k phi g^(-k)` on `A_k` for `0 <= k < p`, and `h = psi` on `D`.
- `h` is a homeomorphism given by finitely many prefix replacements, so `h` lies in `V`.
- For `y` in `A'_k`: `h^(-1) y = g^k phi^(-1) g'^(-k) y` lies in `A_k`, and `g` carries it into
  `A_(k+1)`. So `h g h^(-1) y = g'^(k+1) phi g^(-(k+1)) g^(k+1) phi^(-1) g'^(-k) y = g' y`.
  For `k = p - 1` this uses `g^p = g'^p = 1`.
- On `D'` both sides are the identity. QED

**Tree groups.** Choose `p` distinct words `c_0, ..., c_(p-1)` of one length whose cylinders do not cover
`X`. For each word `w`, let `tau_w` send `c_k w x` to `c_(k+1) w x` and fix everything else.
- `tau_w` is a clopen `p`-cycle.
- `tau_w = tau_(w0) tau_(w1)`.
- All `tau_w` commute. If `w` and `w'` are incomparable their supports are disjoint. If `w` is a prefix
  of `w'`, then `tau_w` conjugates `tau_(w')` to itself.
- `E_n = <tau_w : |w| = n>` is isomorphic to `(Z/p)^(2^n)`, and `E_n <= E_(n+1)`.

**Lemma 1.2.** Each `E_n` is a clopen-cycle subgroup.

*Proof.* Let `g = prod_w tau_w^(eps_w)` over `|w| = n`, and let `W` be the set of words with
`eps_w != 0`. Put `A_k = union over w in W of [c_(k eps_w) w]`, indices mod `p`.
- For each `w` in `W`, `k -> k eps_w` is a bijection of `Z/p`, so the `A_k` are disjoint and nonempty.
- `g` maps `[c_(k eps_w) w]` onto `[c_((k+1) eps_w) w]`, so it maps `A_k` onto `A_(k+1)`.
- `g` is the identity off `union_j [c_j]`, which is not all of `X`. QED

**Theorem 1.3.** Let `sigma` be a rank model of `V` over `F`. There is one number `a = a_p(sigma)` in
`[0,1]` with the following property. For every clopen-cycle subgroup `P <= V` and every character
`chi : P -> mu_p(F')`, the idempotent

```text
e_chi = |P|^(-1) sum_(g in P) chi(g)^(-1) sigma(g)
```

has `rk(e_chi) = a [chi = 1] + (1 - a) / |P|`. In particular every clopen `p`-cycle `tau` has
`rk(sigma(tau) - 1) = (1 - a)(p - 1)/p`.

*Proof.*
1. `|P|` is odd, hence invertible in `F'`, and `sigma` is an exact homomorphism. So the `e_chi` are
   orthogonal idempotents summing to `1`. By [COV] Lemma 2.1(b), `nu_P(chi) = rk(e_chi)` is a
   probability measure on the dual group `P^`.
2. For `g` in `P` and `zeta` in `mu_p`, put `e_(g,zeta) = p^(-1) sum_k zeta^(-k) sigma(g)^k`. This equals
   the sum of `e_chi` over `chi(g) = zeta`. So `m_zeta(g) = rk(e_(g,zeta))` equals
   `nu_P{chi : chi(g) = zeta}`.
3. `e_(g,zeta)` is a polynomial in `sigma(g)`. If `g' = h g h^(-1)` then
   `sigma(h) e_(g,zeta) sigma(h)^(-1) = e_(g',zeta)`, so `m_zeta(g') = m_zeta(g)` by [COV] Lemma 2.1(a).
   By Lemma 1.1 the numbers `m_zeta(g)` are the same for every clopen `p`-cycle `g` in `V`. Call them
   `m_zeta`.
4. For `j` in `(Z/p)^x`, `chi(g)^j = zeta^j` exactly when `chi(g) = zeta`. So `e_(g^j, zeta^j) = e_(g,zeta)`.
   `g^j` is again a clopen `p`-cycle, so `m_(zeta^j) = m_(zeta^j)(g^j) = m_zeta(g) = m_zeta`. Hence `m_zeta`
   takes one value on `zeta != 1`. With `c = m_1`, that value is `(1 - c)/(p - 1)`.
5. Identify `mu_p(F')` with the complex `p`-th roots of unity, and take the Fourier transform
   `nu^(g) = sum_chi nu_P(chi) chi(g)` on `P`. Then `nu^(1) = 1`, and for `g != 1`
   `nu^(g) = sum_zeta zeta m_zeta = c - (1 - c)/(p - 1) =: a`. The measure `a delta_1 + (1 - a) lambda_P`,
   with `lambda_P` uniform, has the same transform. By Fourier inversion on the finite group `P^`,
   `nu_P = a delta_1 + (1 - a) lambda_P`.
6. `a` depends only on `c`, which is global by step 3. Positivity at `chi != 1` gives `a <= 1`. Positivity
   at `chi = 1` gives `a >= -(1 - a)/|P|` for every `P`. The groups `E_n` have unbounded order, so `a >= 0`.
7. `sigma(tau) - 1 = sum over zeta != 1 of (zeta - 1) e_(tau,zeta)`, a combination of orthogonal
   idempotents with unit coefficients. Its rank is `sum over zeta != 1 of m_zeta = 1 - c`, and
   `c = a + (1 - a)/p`. QED

**Corollary 1.4.** If `sigma` is nontrivial, then `a_p(sigma) < 1` for every odd prime `p` different from
the characteristic, and every clopen `p`-cycle has displacement rank `(1 - a_p)(p - 1)/p > 0`.
Conversely, `a_p(sigma) = 1` for a single `p` forces `sigma(tau) = 1` for a nonidentity `tau`, so `sigma`
is trivial because `V` is simple.

**Corollary 1.5 (disjoint cycles act independently).** For commuting clopen `p`-cycles generating a
clopen-cycle subgroup of order `p^k`, the joint fixed projection has rank `a + (1 - a)/p^k`. As `k` grows
it tends to `a`, whatever the supports of the cycles.

So on every clopen-cycle subgroup a rank model looks like a fraction `a` of trivial representation plus
a fraction `1 - a` of the regular representation. Only the constant `a_p(sigma)` is free.
