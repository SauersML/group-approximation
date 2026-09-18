---
rg: 2
id: thompson-f-exact-shift-covariant-models-force-amenability-proof
kind: route
title: Shift the two base relations up the infinite presentation, split off the regular summand by Radon-Nikodym, and intersect tensor supports
target: thompson-f-exact-shift-covariant-models-force-amenability
requires:
  - thompson-f-character-simplex
  - thompson-f-hyperlinear-iff-relator-system-hs-unstable
---

**Imports (trust surface).**
1. *Infinite presentation.* This is the import recorded in `thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f-proof`.
   J. T. Moore, arXiv:0905.1118v7, `main.tex` l.102–108, verbatim: "The standard presentation of $F$ is
   infinite, with generators $x_i$ $(i \in \Nbb)$ satisfying $x_i^{-1} x_n x_i = x_{n+1}$ for all
   $i < n$. It is well known, however, that $F$ admits the finite presentation \[ \Seq{A,B \ |\
   [AB^{-1},A^{-1}BA] = [AB^{-1},A^{-2}BA^2]= \mathrm{id}} \] (see \cite{CFP})." Here `A = x_0` and `B = x_1`.
2. *Proper quotients.* Every proper quotient of `F` is abelian. This is the import recorded in
   `thompson-f-is-lea-only-if-amenable-proof`: Burillo–Lodha–Reeves, arXiv:1509.04586, `lm.tex` l.104,
   verbatim, "every proper quotient of $F$ is abelian \cite{cfp}".
3. *Characters.* `thompson-f-character-simplex`: every character of `F` is
   `t tau_reg + (1-t) chi_ab`, where `chi_ab` factors through `F -> Z^2`.
4. *Classical operator-algebra facts, not re-read.*
   - (O1) Radon–Nikodym for positive functionals (Dixmier, *C\*-algebras*, 2.5.1). If `psi <= phi` are
     positive functionals on a C\*-algebra with GNS data `(pi_phi, H_phi, xi)`, then
     `psi(x) = <pi_phi(x) T xi, xi>` for some `T in pi_phi(A)'` with `0 <= T <= 1`.
   - (O2) Injectivity of a von Neumann algebra does not depend on its faithful normal representation.
   - (O3) A discrete group `Gamma` is amenable iff `L(Gamma)` is injective (Brown–Ozawa,
     *C\*-algebras and finite-dimensional approximations*, Thm 2.6.8).
   - (O4) Every von Neumann subalgebra `N` of a finite von Neumann algebra `(M, tau)` is the range of a
     `tau`-preserving conditional expectation `E_N : M -> N`.
   - (O5) Connes: every injective separable `II_1` factor is isomorphic to `R`.

Throughout, `||x||_2 = tau(x^* x)^(1/2)`. Every trace-preserving `*`-endomorphism is a `||.||_2`-isometry,
and multiplying by unitaries preserves `||.||_2`.

## Step 1. Reduction (item 1)

Put `s_0 = a` and `s_n = sigma^n(a)` for `n >= 1`. Write `R(i, j)` for the relation `s_i^* s_j s_i = s_(j+1)`.
Hypotheses (A) and (B) are `R(0,1)` and `R(0,2)`. Since `sigma(s_k) = s_(k+1)` for every `k >= 0`, applying
`sigma^i` to `R(0,m)` gives `R(i, i+m)`.

*Claim: `R(0,j)` holds for all `j >= 1`.* Induct on `j`. The cases `j = 1, 2` are the hypotheses. Let
`j >= 2` and assume `R(0,j-1)` and `R(0,j)`. Applying `sigma` to `R(0,j-1)` gives
`s_(j+1) = s_1^* s_j s_1`. Conjugating by `s_0` and inserting `s_0 s_0^* = 1`:

```text
s_0^* s_(j+1) s_0 = (s_0^* s_1 s_0)^* (s_0^* s_j s_0) (s_0^* s_1 s_0)
                  = s_2^* s_(j+1) s_2                      [R(0,1), R(0,j)]
                  = sigma^2(s_0^* s_(j-1) s_0) = sigma^2(s_j) = s_(j+2).   [R(0,j-1)]
```

This is `R(0,j+1)`. Hence `R(i,j)` holds for all `i < j`, and by import 1 the assignment `x_n -> s_n`
defines a homomorphism `pi : F -> U(M)`. It has `pi(x_0) = a` and `pi(x_1) = sigma(a)`.

If `a` and `sigma(a)` commute, the image is abelian, and `pi` is not injective because `x_0` and `x_1`
do not commute in `F`. If they do not commute, `F / ker pi` is nonabelian, so `ker pi = 1` by import 2.

*The model in `L(F)`.* The shift `phi(x_i) = x_(i+1)` maps each relation `R(i,n)` of import 1 to
`R(i+1,n+1)`, so it is an endomorphism. Its image contains `x_1` and `x_2`, which do not commute, so it is
injective by import 2. So `phi_*(lambda(g)) = lambda(phi(g))` defines a unital
trace-preserving normal `*`-endomorphism of `L(F)`, because `tau(lambda(phi g)) = [g = e]`. Relations (A)
and (B) for `a = lambda(x_0)` are the defining relations `x_0^-1 x_1 x_0 = x_2` and `x_0^-1 x_2 x_0 = x_3`.

## Step 2. The regular summand (item 2)

Let `pi` be injective and `N = pi(F)''`. The trace `tau` restricts to a faithful normal trace on `N`, and
`phi = tau o pi` is a character of `F`. By import 3, `phi = t tau_reg + (1-t) chi_ab`.

*`t > 0`.* If `t = 0`, then `phi(c) = 1` for every `c in F'`, since `chi_ab` is trivial on `F'`. Then
`||pi(c) - 1||_2^2 = 2 - 2 Re tau(pi(c)) = 0`, so `pi(F') = 1`. That contradicts injectivity, because
`F' != 1`.

*Splitting.* The GNS representation of `phi` is `N` acting on `L^2(N, tau)` with cyclic vector `1^`,
because `tau` is faithful on `N` and `pi(F)` spans a weakly dense subalgebra. The difference
`phi - t tau_reg = (1-t) chi_ab` is positive definite, so `t tau_reg <= phi` as positive functionals on
`C*(F)`. By (O1) there is `T in N'` with `0 <= T <= 1` and `t tau_reg(g) = <pi(g) T 1^, 1^>`. Put
`eta = T^(1/2) 1^` and let `e in N'` be the projection onto `K`, the closed span of `pi(F) eta`. Then

```text
<pi(g) eta, eta> = <pi(g) T 1^, 1^> = t tau_reg(g),
```

so `(pi|_K, K, eta / sqrt t)` is a GNS triple for `tau_reg`. It is unitarily equivalent to the left
regular representation on `l^2 F` with cyclic vector `delta_e`, by an equivalence carrying `pi(g) e` to
`lambda(g)`.

The map `x -> x e` from `N` to `B(K)` is a normal `*`-homomorphism, since `e in N'`. Its image is
`(pi(F) e)''`, which is spatially isomorphic to `lambda(F)'' = L(F)`. Its kernel is a weakly closed
two-sided ideal of `N`, so it equals `N (1 - z)` for a central projection `z` of `N`. Hence
`L(F) ≅ N z`, a direct summand of `N ⊆ M`.

## Step 3. Amenability collapse (item 3)

*Only if.* Let `M` be injective, for example `M = R`, and let `a` be a non-commuting exact model. By
Step 1 `pi` is injective, and by Step 2 `L(F) ≅ N z` with `N = pi(F)'' ⊆ M`.
- Let `Phi : B(H) -> M` be a conditional expectation, where `M ⊆ B(H)`. Then `E_N o Phi`, with `E_N` from
  (O4), is a norm-one projection of `B(H)` onto `N`, so `N` is injective.
- Compress by `z`. For `y in B(zH)`, put `Psi(y) = E_N(Phi(y)) z`. Then `Psi` is a norm-one projection
  of `B(zH)` onto `N z`, because `E_N(Phi(n z)) = n z` for `n in N`. So `N z` is injective on `zH`.
- By (O2), `L(F)` is injective. By (O3), `F` is amenable.

*If.* Let `F` be amenable. `F` is ICC: this is standard, and it also follows from import 3, since the regular
character is extreme and not of the form `chi_ab`, so `L(F)` is a factor. So `L(F)` is an injective (O3) separable `II_1`
factor, hence `L(F) ≅ R` by (O5). Transport the model `(lambda(x_0), phi_*)` of Step 1 along this isomorphism.
It does not commute, because `x_0 x_1 != x_1 x_0`.

## Step 4. Local Bernoulli models (item 4)

Let `A = ⊗_(k>=0) M_d` with its product trace, and let `A_S` be the subalgebra on the sites in `S`. Let
`E_S` be the `tau`-preserving conditional expectation onto `A_S`; it takes the normalized partial trace
over the sites outside `S`. For finite intervals `S, T`, `E_S E_T = E_(S ∩ T)`. Hence
`A_S ∩ A_T = A_(S ∩ T)`, since `x = E_S(x) = E_S E_T(x) = E_(S∩T)(x)`. Also
`sigma^k(A_[p,q)) = A_[p+k,q+k)` and `E_[p+k,q+k) o sigma^k = sigma^k o E_[p,q)`.

*Exact case.* Let `a in A_[0,L)` be unitary with (A). Then `sigma^2(a) = a^* sigma(a) a` lies in
`A_[2,L+2) ∩ A_[0,L+1) = A_[2,L+1) = sigma^2(A_[0,L-1))`. Since `sigma` is injective, `a in A_[0,L-1)`.
Descending induction on `L` gives `a in A_[0,0) = C 1`. Only (A) is used.

*2-norm case.* Let `y = a^* sigma(a) a`, which lies in `A_[0,L+1)`, and suppose `||y - sigma^2(a)||_2 <= delta`.
`E_[0,L+1)` is the orthogonal projection of `L^2` onto `L^2(A_[0,L+1))`, so

```text
||sigma^2(a) - E_[0,L+1)(sigma^2 a)||_2 <= ||sigma^2(a) - y||_2 <= delta.
```

The element `sigma^2(a)` lives on sites `2..L+1`, so `E_[0,L+1)(sigma^2 a) = E_[2,L+1)(sigma^2 a)`, which
is `sigma^2(E_[0,L-1)(a))`. Since `sigma^2` is a 2-norm isometry, `||a - E_[0,L-1)(a)||_2 <= delta`.

*Why this does not iterate uniformly.* `b = E_[0,L-1)(a)` is a contraction, not a unitary. Substituting
`b` for `a` in (A) changes each of the four occurrences by at most `delta` in `||.||_2`, since every other
factor has operator norm at most 1. So `b` has (A)-defect at most `5 delta`. Nothing in Step 4 used
unitarity, so the argument repeats, giving
`||a - E_[0,L-k)(a)||_2 <= (1 + 5 + ... + 5^(k-1)) delta`. In detail, write `b_k = E_[0,L-k)(a)`.
Then `b_(k+1) = E_[0,L-k-1)(b_k)`, and the defect `d_k` of `b_k` satisfies
`d_(k+1) <= d_k + 4 ||b_k - b_(k+1)||_2 <= 5 d_k`. This is useless once `5^k delta >= 1`.

*Commutator bound.* Take `k = L-1`, so `b = b_(L-1) in A_[0,1)` and `||a - b||_2 <= (5^(L-1) - 1) delta / 4`.
The elements `b` and `sigma(b)` sit on the disjoint sites 0 and 1, so they commute. Since
`a sigma(a) - b sigma(b) = (a - b) sigma(a) + b sigma(a - b)`, and similarly for the reversed product,

```text
||[a, sigma(a)]||_2 = ||[a, sigma a] - [b, sigma b]||_2 <= 4 ||a - b||_2 <= (5^(L-1) - 1) delta.
```

## Step 5. Sufficient route (item 5)

Let `a in A_[0,L)` be unitary with (A)- and (B)-defects at most `delta`. Put `s_k = sigma^k(a)`, which is
supported on sites `k..k+L-1`. Everything below lies in `A_[0,L+4) = M_(d^(L+4))`, and the product trace
restricts to the normalized trace there. For `k = 0, 1, 2`, applying `sigma^k` gives

```text
||s_k^* s_(k+1) s_k - s_(k+2)||_2 <= delta,    ||s_k^* s_(k+2) s_k - s_(k+3)||_2 <= delta.
```

Let `U = s_0` and `W = s_1`, and form `x_2 = U^* W U` and `x_3 = U^* x_2 U`. Then
`||x_2 - s_2||_2 <= delta` and `||x_3 - s_3||_2 <= 2 delta`. For a relator `[g, h]` with `g, h` unitary,
`||[g,h] - 1||_2 = ||gh - hg||_2`. With `g = U W^*`, this equals `||W^* h W - U^* h U||_2`.

*First relator, `h = x_2`.*
- `W^* x_2 W` is within `delta` of `W^* s_2 W = sigma(U^* W U)`, which is within `delta` of `s_3`.
- `U^* x_2 U = x_3` is within `2 delta` of `s_3`.

So the first defect is at most `4 delta`.

*Second relator, `h = x_3`.*
- `W^* x_3 W` is within `2 delta` of `W^* s_3 W = sigma(U^* s_2 U)`, which is within `delta` of `s_4`.
- `U^* x_3 U` is within `2 delta` of `U^* s_3 U`. Also `s_3` is within `delta` of `W^* s_2 W`, so
  `U^* s_3 U` is within `delta` of `(U^* W U)^* (U^* s_2 U) (U^* W U)`. Replacing the three factors by
  `s_2, s_3, s_2` costs at most `3 delta`. Finally `s_2^* s_3 s_2` is within `delta` of `s_4`. So
  `U^* x_3 U` is within `7 delta` of `s_4`.

So the second defect is at most `10 delta`.

A sequence as in item 5 therefore gives pairs `(U_n, W_n)` in `U(d^(L_n+4))` satisfying both relators
within `10 delta_n -> 0`, with `||U_n W_n - W_n U_n||_2 >= c`. This violates statement 3 of
`thompson-f-hyperlinear-iff-relator-system-hs-unstable`, so `F` is hyperlinear.

A direct argument also works. The ultraproduct pair satisfies the relators exactly, so it defines a
homomorphism `F -> prod_omega M_(k_n)` with non-commuting image, and it is injective by import 2.

## Scope and what is not claimed

- Steps 1 to 3 hold for any trace-preserving endomorphism, not just the Bernoulli shift.
- Step 4 is specific to the one-sided tensor shift, and to finite support.
- Nothing here decides whether the Bernoulli ultrapower `(R^omega, sigma^omega)` carries a non-commuting
  exact model. By Step 5 that would prove `thompson-f-is-hyperlinear`.
- It is also not shown that every hyperlinear model of `F` can be put in shift-covariant Bernoulli form.
  So a negative answer would kill only this class, not prove `thompson-f-is-not-hyperlinear`.
