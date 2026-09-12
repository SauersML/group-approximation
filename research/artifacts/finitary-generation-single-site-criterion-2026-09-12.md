# Finitary generation and the single-site criterion for surjunctivity

Lane `w3-inf-a`, 2026-09-12. Supports `strict-automata-give-injective-ca-with-skewed-site-marginals`,
`every-injective-ca-has-uniform-single-site-output-law` and
`injective-ca-images-have-full-single-site-entropy`.

The lane was asked for an entropy-type invariant that sees exact generation. The invariant studied here is
the smallest single-site entropy of an injective automaton image. Its generating partitions have finite
radius. Section 2 proves that a strict automaton makes it drop. Section 3 places it between maximal
Bernoulli Rokhlin entropy and Gottschalk's conjecture, and records where it stops.

## 1. Conventions

- `G` is a countable group, `A` a finite alphabet with `q = |A| >= 2`, and `mu_A` the uniform product
  measure on `A^G`.
- An automaton is `tau(x)(g) = f((x(g m))_(m in M))` with `M` finite. It commutes with the shift
  `(h.x)(g) = x(h^-1 g)`.
- The pattern of `y` on `g Omega` is the function `omega -> y(g omega)` in `A^Omega`.
- The single-site output law of an automaton `kappa: A^G -> B^G` is the law of `kappa(x)(e)` under `mu_A`.
  By equivariance and shift invariance of `mu_A` it is the law at every site.

Standard facts used:

- **(F1)** If `tau` is injective and not surjective, there are a finite `Omega` and `p in A^Omega` such that
  the pattern of `tau(x)` on `g Omega` is never `p`, for every `x` and `g`. The image is closed and proper,
  so it misses a cylinder at `e`, and equivariance moves the cylinder to every `g`.
- **(F2)** An injective automaton `tau` has an automaton `sigma` with `sigma o tau = id`. The inverse on
  the image is continuous and equivariant, so it reads a finite window; extend its local rule arbitrarily.
- **(F3)** Every pattern in `S = {pattern of tau(x) on Omega : x in A^G}` has positive probability under
  `mu_A`, because its preimage is a nonempty open set.

## 2. Theorem 1: a strict automaton skews a single-site law

**Theorem 1.** Let `tau` be injective and not surjective on `A^G`, with `Omega`, `p` as in (F1). Put
`D = Omega Omega^-1` and `rho = q^(-|D|)`. There is `c > 0`, depending only on `tau` and `Omega`, such
that for every integer `k > (log 2)/(rho c)` some injective automaton `kappa` on `(A^(k+1))^G` into itself
has single-site output law of entropy `< (k+1) log q`. In particular that law is not uniform.

*Step 1: greedy recoding of blocks.* Let `nu` be the law of `Y`, the pattern of `tau(x)` on `Omega` under
`mu_A`. By (F1) and (F3) its support is `S`, with `|S| <= q^|Omega| - 1`, and every atom has positive
mass. Fix `omega_0 in Omega`. The classes `C_a = {u in A^Omega : u(omega_0) = a}` have
`N = q^(|Omega|-1)` elements each. List `S` by nonincreasing probability `s_1, s_2, ...` and fill
`C_(a_1)`, then `C_(a_2)`, and so on, injectively. This defines an injection `beta: S -> A^Omega`. Let
`lambda` be the law of `beta(Y)(omega_0)`. Then `lambda` is not uniform:

- if `|S| < N`, all mass lies in one class;
- if `N <= |S| <= (q-1)N`, the class `C_(a_q)` is empty;
- otherwise `C_(a_q)` holds at most `N - 1` atoms, each of mass at most `nu(s_N)`, so its mass is
  `< N nu(s_N) <= lambda(a_1)`.

Put `c = log q - H(lambda) > 0`.

*Step 2: anchors.* Fix distinct symbols `0, 1 in A`. Call `g` an anchor of `z in A^G` when `z(g) = 1`
and `z(g d) = 0` for all `d in D \ {e}`. For anchors `g != h`, `g^-1 h` is not in `D`: otherwise `z(h)`
would be both `1` and `0`. So the blocks `g Omega` of distinct anchors are disjoint, since
`g omega = h omega'` gives `g^-1 h = omega omega'^-1 in D`.

*Step 3: the automaton.* Write `x = (x_0, x_1, ..., x_k)` and `y_j = tau(x_j)`. Put
`kappa(x)(g) = (x_0(g), y'_1(g), ..., y'_k(g))`, where:

- if `g = h omega` for an anchor `h` of `x_0`, with `h` and `omega` unique by Step 2, then
  `y'_j(g) = beta(pattern of y_j on h Omega)(omega)`;
- otherwise `y'_j(g) = y_j(g)`.

`kappa` reads `x_0` on `g Omega^-1 D` and `x_j` on `g Omega^-1 Omega M`, so it is an automaton.

*Step 4: injectivity.* Recover `x` from `z = kappa(x)` in four finite-window steps, which together give an
automaton left inverse:

1. track `0` of `z` is `x_0`;
2. its anchors locate the blocks;
3. inside a block `y_j` is `beta^-1` of the block pattern of `z_j`, and outside, `y_j = z_j`;
4. `x_j = sigma(y_j)` by (F2).

*Step 5: entropy.* Let `I` be the indicator that `e omega_0^-1` is an anchor of `x_0`, so
`P(I = 1) = rho`. Under the product measure the tracks are independent, and `I` depends on `x_0` only.
Given `I = 1`, the site `e` is the `omega_0`-point of the block of `e omega_0^-1`, so the `y'_j(e)` are
independent with law `lambda`, by shift invariance. Therefore

    H(kappa(x)(e)) <= H(x_0(e)) + H(I) + H(y'(e) | I)
                   <= log q + log 2 + (1 - rho) k log q + rho k H(lambda)
                    = (k+1) log q + log 2 - rho k c,

which is `< (k+1) log q` once `k > (log 2)/(rho c)`. QED

**Remarks.**

- `kappa` is an injective endomorphism of `(A^(k+1))^G` whose image process has non-uniform site law, so
  `kappa` is itself strict. That agrees with `bijective-ca-preserve-uniform-bernoulli-measure`.
- The partition of `(A^(k+1))^G` by `kappa(x)(e)` generates, because its names give `kappa(x)` and Step 4
  recovers `x`. Its entropy is `< log |A^(k+1)|`. This is a Bernoulli Rokhlin-entropy deficit carried by a
  finite-radius generator with explicit constants. `strict-automaton-lowers-bernoulli-rokhlin-entropy`
  reaches a deficit through measurable markers instead.
