# Low-degree strict pairs over finite fields: linear parts, invariant output, unipotent normal form

Lane `gk-n-highalpha`, 2026-09-12. Supports the claims
`low-degree-strict-pairs-have-one-sided-linear-parts`,
`low-degree-invariant-output-reduces-to-corner-fullness`,
`unipotent-automata-over-finite-fields-are-surjective` (open) and
`low-degree-strict-automata-force-matrix-kaplansky-failure` (open).

The question: do large alphabets and nonlinear rules built from the idempotent
structure of `F_q[G]` escape the linear obstructions? For rules of low degree
relative to the field size they do not. Every low-degree strict pair either carries
a one-sided inverse pair of matrices over the group algebra in its linear parts,
or normalizes to a unipotent automaton. Every low-degree invariant-output design is
a matrix corner-fullness equation over the prime field. Genuinely new designs must
use degree products at least `q`, where the reduction `x^q = x` feeds higher decoder
terms into degree one.

## 0. Setting

- `q = p^k`, `F = F_q`, alphabet `A = F^m`, `G` any group.
- An automaton is `tau(x)(g) = F_tau((x(g s))_(s in S))` with finite memory `S`.
- Every map `F^(m|S|) -> F^m` is a unique `m`-tuple of **reduced** polynomials in the
  variables `x_(s,i)`: each exponent is below `q`. Put `deg tau` for the largest total
  degree among the reduced components of the local rule.
- For `A in M_m(F[G])`, `A = sum_s A_s s` with `A_s in M_m(F)`, the linear automaton is
  `tau_A(x)(g) = sum_s A_s x(g s)`, with `x(u)` a column vector. Then
  `tau_C tau_A = tau_(CA)`:
  `tau_C(tau_A x)(g) = sum_t C_t sum_s A_s x(g t s) = sum_u (sum_(ts = u) C_t A_s) x(g u)`.
- **Normalization.** If `sigma tau = id`, put `c = tau(0)`, a constant configuration.
  Replace `tau` by `x -> tau(x) - c` and `sigma` by `y -> sigma(y + c)`. Translation by a
  constant configuration is a bijective automaton commuting with shifts. Injectivity,
  strictness, degrees and right-coset invariance of the output are unchanged. Now
  `tau(0) = 0`, and `sigma(0) = sigma(tau(0)) = 0`.
- The **linear part** `tau_1 = tau_A` collects the degree-one monomials of the
  normalized local rule.

## 1. Theorem 1 (linear parts of a low-degree strict pair)

Let `tau`, `sigma` be automata over `F^m` with `tau(0) = 0` and `sigma tau = id`. If
`deg sigma * deg tau < q`, then `C A = I_m` in `M_m(F[G])`, where `tau_1 = tau_A` and
`sigma_1 = tau_C`.

*Proof.* Fix `g`. Write the reduced local rule of `sigma` as `sum_alpha c_alpha y^alpha`
in the variables `y_(t,j)`, with `c_0 = 0` because `sigma(0) = 0`. Substitute
`y_(t,j) = P_(t,j)(x)`, the `j`-th component of `tau(x)(g t)`. This is a reduced polynomial
of degree at most `deg tau` with zero constant term, in the variables
`x_(u,i) = x_i(g u)`, `u in T S`.

A monomial `y^alpha` of total degree `D` becomes a product of `D` polynomials without
constant term. Before any reduction, each resulting `x`-monomial has total degree
between `D` and `D deg tau`, and each exponent is at most `D deg tau`, which is below `q`.
Product coincidences `t s = t' s'` in `G` identify variables. That merges monomials and
raises exponents, but it keeps total degree and keeps every exponent at most the total
degree, still below `q`.

So the substituted polynomial is already reduced. Its degree-one part comes only from
`D = 1`, that is, from `sigma_1` applied to `tau_1`, and it is the local rule of
`tau_(CA)`. The composite is the identity map, and reduced representations are unique,
so its degree-one coefficients form `C A = I_m`, and every higher coefficient vanishes. QED

## 2. Corollary 2 (dichotomy)

Under the hypotheses of Theorem 1, exactly one of the following holds.

- **(a)** `A C != I_m`. Then `M_m(F[G])` is not directly finite, and `tau_A` is injective
  and not surjective. Viewing `F = F_p^k`, it is also an `F_p`-linear strict automaton over
  `F_p^(mk)`, so `M_(mk)(F_p[G])` is not directly finite.
- **(b)** `A C = I_m`. Then `tau' = tau_C tau` has local rule `x(g) + (terms of degree >= 2)`,
  with decoder `sigma' = sigma tau_A`. Also `deg tau' <= deg tau` and `deg sigma' <= deg sigma`,
  and `tau'` is strict exactly when `tau` is.

*Proof.* (a) `CA = I`, so `tau_A` has left inverse `tau_C`. If `tau_A` were onto it would
be bijective with inverse `tau_C`, forcing `tau_(AC) = id` and `AC = I`.

(b) `A` is a unit with inverse `C`, so `tau_C` is a bijective automaton and `tau'` is
injective, and strict exactly when `tau` is. Composing with a linear automaton adds no
products, so the degree-one part of `tau'` is `tau_(CA) = id`. Linear substitution
does not raise degree. QED

## 3. Corollary 3 (low-degree invariant output)

Let `H <= G` be finite, `H != 1`, and let `tau` be an injective automaton over `F^m`
with right-`H`-invariant output `tau(x)(gh) = tau(x)(g)` and a left inverse `sigma`, with
`deg sigma * deg tau < q`.

- **(i)** If `p` divides `|H|`, this is impossible.
- **(ii)** If `p` does not divide `|H|`, put `e = |H|^-1 sum_(h in H) h`, which lies in
  `F_p[G]`. Then there are `B, C in M_m(F[G])` with `C (e I_m) B = I_m`. Conversely any
  such pair gives the degree-one design `tau_(eB)` with decoder `tau_C`. So low-degree
  invariant-output designs over `F^m` exist exactly when `e` is full at some matrix size
  over `F[G]`, equivalently over `F_p[G]` at matrix size `mk`.

*Proof.* Normalize; the output stays `H`-invariant.

**Invariance of the linear part.** Invariance for every `x` says the reduced local rule in
the variables `x_(hs)` equals the reduced local rule in the variables `x_s`, as reduced
polynomials over the union of both variable sets. On the degree-one part, the coefficient of
`x_u` is `A_(h^-1 u)` on the left and `A_u` on the right. So `A_u = A_(h^-1 u)`, which is
`h A = A`, for every `h in H`.

(i) The coefficients of `A` are constant on the left orbits `H u`, each of size `|H|`. So
the augmentation `eps(A)` is `0` in `M_m(F)`. Theorem 1 gives `C A = I`, so
`eps(C) eps(A) = I_m`, a contradiction.

(ii) `h A = A` for all `h` gives `e A = A`, so `C e A = I` with `B = A`.

Conversely, if `C e B = I`, then `h(eB) = eB`, so the output of `tau_(eB)` is invariant:
`tau_a(x)(gh) = sum_u (h a)_u x(g u) = tau_a(x)(g)` when `h a = a`. And
`tau_C tau_(eB) = tau_(CeB) = id`.

Such a design always falls in case (a) of Corollary 2. `AC = I` with `A = eA` would give
`e = e A C = A C = I`, and `e != 1` because `H != 1`.

**Restriction of scalars.** The regular representation `F -> M_k(F_p)` embeds
`M_m(F[G])` in `M_(mk)(F_p[G])` as a ring. It sends `e I_m` to `e I_(mk)`, because
`e in F_p[G]`. QED

**Consequence for the Leavitt hosts.** For `G_3 = L_(F_3)(1,2)^x` and `H = <w>`, every
low-degree invariant-output design over any `F_(3^k)^m` is a matrix corner-fullness equation
for `e = 2(1 + [w])` over `F_3[G_3]`. That is the matrix form of
`ternary-leavitt-swap-idempotent-is-full`. Large alphabets add construction room at matrix
size, not a new mechanism. Over any `F_(2^k)` and any even-order `H`, low-degree
invariant-output designs are dead.

## 4. Example 4 (the degree bound is needed)

Take `F = F_8`, `m = 1`, `tau(x)(g) = x(g)^3` and `sigma(y)(g) = y(g)^5`. On `F_8`,
`x^15 = x`, so `sigma tau = id`, and both are bijective automata with memory `{1}`. Here
`deg sigma * deg tau = 15 >= 8`.

The linear parts are `0`, over `F_8` and also over `F_2` in coordinates `F_8 = F_2^3`,
where `x^3 = x Frob(x)` and `x^5 = x Frob^2(x)` are quadratic. So `C A = 0 != I`. The
reduction `x^q = x` is exactly what carries higher decoder terms into degree one.

Over `F_2` alphabets the bound `deg sigma * deg tau < 2` forces both maps to be linear.
Theorem 1 is silent on every genuinely nonlinear binary design, which is where
`invariant-output-rules-need-odd-invariant-monomials` and the table-group filters apply.

## 5. What survives

- Over `F_q`, a strict pair with `deg sigma * deg tau < q` is either a matrix Kaplansky pair
  over `F_p[G]` (for invariant output, matrix corner fullness of `e`), or reduces to a
  strict unipotent automaton `id + N`.
- A nonlinear design that is not a disguised linear one must have
  `deg sigma * deg tau >= q`. Its decoder identity must use the reduction `x^q = x`.
- Whether strict unipotent automata exist is open:
  `unipotent-automata-over-finite-fields-are-surjective`. If they never do, every low-degree
  strict automaton comes from a matrix one-sided pair
  (`low-degree-strict-automata-force-matrix-kaplansky-failure`).

## 6. Attempts on the unipotent class

- **Sofic hosts.** Every automaton is surjective there (`sofic-groups-are-surjunctive`), so
  the question lives on nonsofic hosts only.
- **Measure preservation.** An injective automaton preserving uniform Bernoulli measure is
  surjective (`injective-measure-preserving-ca-is-surjective`). Unipotence does not visibly
  force `tau'_* mu = mu`: the site marginal of `x(g) + N(x)(g)` is uniform when `N(x)(g)` is
  independent of `x(g)`, but `N` may read `x(g)` itself. Dies as stated.
- **Scaling torus.** For `q > 2`, `x -> lambda x` with `lambda in F_q^x` conjugates `tau'` to
  `id + sum_j lambda^(j-1) N_j`, where `N_j` is the homogeneous degree-`j` part. Every member
  of the family is injective, but a finite field has no limit `lambda -> 0`, so the family
  gives no contraction. Dies.
- **Iterative solving.** Solving `y = x + N(x)` by `x = y - N(x)` has no contraction in a
  discrete alphabet, and a Garden-of-Eden pattern is not excluded. Dies.
- **Graded counting on windows.** It needs finite models, so it recovers only the sofic case.
