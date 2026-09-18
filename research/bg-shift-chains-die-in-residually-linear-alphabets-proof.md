---
rg: 2
id: bg-shift-chains-die-in-residually-linear-alphabets-proof
kind: route
title: Pass to quotients, then kill periodic chains by descending primes, solvable chains by perfectness and linear chains by Jordan decomposition
target: bg-shift-chains-die-in-residually-linear-alphabets
requires:
  - nonsingular-magnus-extremes-separable-piece-sofic
---

Date: 2026-09-17. Written proof.

A *forward BG chain* in `Q` is `(x_j)_(j >= 0)` with
`x_(j+1)^(-1) x_j x_(j+1) = x_j^2` for all `j >= 0`.

## Step 0. Rotations and quotients

1. If `(x_j)` is a chain, so is `(x_(j+k))_(j >= 0)` for each `k >= 0`.
2. If `f : Q -> Q'` is a homomorphism, `(f(x_j))` is a chain in `Q'`.
3. If `x_j = 1` for some `j >= 1`, then `x_(j-1) = x_(j-1)^2`, so
   `x_(j-1) = 1`; by induction `x_0 = ... = x_j = 1`.

Let `C` be a class of groups in which every chain is trivial, and let `Q` be
residually `C`. If `x_j != 1`, some `f : Q -> Q'`, `Q' in C`, has
`f(x_j) != 1`, but `f(x)` is a chain in `Q'`, hence trivial. So chains in `Q`
are trivial. The union of several such classes also has this property, and so
does "residually (union)". It therefore suffices to prove triviality for
periodic groups, solvable groups and linear groups.

## Step 1. Periodic groups

Section 9 of [[nonsingular-magnus-extremes-separable-piece-sofic-proof]]
("Proposition (BG kills every torsion alphabet)") proves: if every `x_j`,
`j >= j_0`, has finite order and the relation holds for `j >= j_0`, then all
`x_j = 1`. We use this with `j_0 = 0`, and later for a chain whose terms are
known to have finite order without `Q` being periodic.

Recap: `m_j = ord(x_j)` is odd because `x_j ~ x_j^2`; conjugation by
`x_(j+1)` induces `y -> y^2` on `<x_j>`, of order `ord_(m_j)(2)`, which
therefore divides `m_(j+1)`. A prime `p | m_j` gives a prime
`p' | ord_p(2) | m_(j+1)` with `p' < p`. An infinite descending sequence of
primes is impossible.

## Step 2. Solvable groups

With `[g,h] = g^(-1) h^(-1) g h`,

    [x_j, x_(j+1)] = x_j^(-1) (x_(j+1)^(-1) x_j x_(j+1)) = x_j^(-1) x_j^2 = x_j.

So `M = <x_j : j >= 0>` satisfies `M = [M,M]`. A solvable perfect group is
trivial (`M = M^(k)` for all `k`). Subgroups of solvable groups are solvable,
so `M = 1`.

## Step 3. Linear groups

Let `Q <= GL_d(K)`, `K` a field, and let `Kbar` be an algebraic closure.

**3a. Eigenvalues are roots of unity.** Let `S` be the set of eigenvalues of
`x_j` in `Kbar` (all nonzero). `x_j^2` is conjugate to `x_j`, so `x_j^2` has
eigenvalue set `S`. The eigenvalues of `x_j^2` are the squares of those of
`x_j` (triangularize over `Kbar`). So `lambda -> lambda^2` maps the finite set
`S` onto `S`, hence is a bijection of `S`. Some power `2^k` of it, with
`k = |S|!`, is the identity, so `lambda^(2^k - 1) = 1` for all `lambda in S`.

**3b. Characteristic p > 0.** Write the multiplicative Jordan decomposition
`x_j = s_j u_j` over `Kbar`, where `s_j` is semisimple, `u_j` is unipotent and
they commute. By 3a, `s_j` is diagonalizable with root-of-unity eigenvalues, so
it has finite order. `u_j - 1` is nilpotent, so `u_j^(p^e) = 1` for
`p^e >= d`. So `x_j` has finite order. This holds for every `j`, and Step 1
gives `x = 1`.

**3c. Characteristic 0.** Again `x_j = s_j u_j`. Put `y = x_(j+1)`. Conjugation
by `y` is an automorphism, so `y^(-1) s_j y` is semisimple, `y^(-1) u_j y` is
unipotent, and they commute. Their product is `x_j^2 = s_j^2 u_j^2`, whose
Jordan decomposition is `(s_j^2, u_j^2)`. By uniqueness of the decomposition,

    y^(-1) u_j y = u_j^2.

Let `N_j = log u_j = sum_(i=1)^(d-1) (-1)^(i+1) (u_j - 1)^i / i`, which is a
nilpotent matrix with `exp(N_j) = u_j`. The logarithm is a polynomial map on
unipotent matrices and commutes with conjugation, and `log(u^2) = 2 log(u)` for
unipotent `u` (both sides are nilpotent and exponentiate to `u^2`, and `exp` is
injective on nilpotent matrices in characteristic `0`). Hence

    Ad(y^(-1)) N_j := y^(-1) N_j y = 2 N_j.

The linear operator `X -> y^(-1) X y` on `M_d(Kbar)` is `(y^(-1))^T ⊗ y` in
suitable coordinates. Its eigenvalues are the products `mu_a^(-1) mu_b` of
eigenvalues of `y`. By 3a applied to `y = x_(j+1)`, these are roots of unity.
If `N_j != 0`, then `2` is an eigenvalue, so `2` is a root of unity in a field
of characteristic `0`, which is false. So `N_j = 0`, `u_j = 1`, and `x_j = s_j`
has finite order. This holds for every `j`, and Step 1 gives `x = 1`.

## Step 4. Consequences

* Residually finite groups are residually periodic.
* Compact groups: by Peter--Weyl, finite-dimensional unitary representations
  separate points, so a compact group is residually linear over `C`.
* **Shift dictionary.** For BG, `W_0 = a_1^(-1) a_0 a_1 a_0^(-2)`. A
  configuration `x : Z -> Q` satisfies `W_0(x_j, x_(j+1)) = 1`, that is
  `x_(j+1)^(-1) x_j x_(j+1) = x_j^2`, for all `j`. So `(x_j)_(j >= j_0)` is a
  forward chain for every `j_0`, and all `x_j = 1` when `Q` is in `R`. Thus
  `rho(a) = x = 1`.

## Calibration

* `BS(1,2) = Z[1/2] rtimes Z <= GL_2(Q)` contains the finite chain
  `x_0 = 1 in Z[1/2]`, `x_1 = ` the generator of `Z`, with `x_0` unipotent of
  infinite order. This is consistent with the theorem: Step 3c at `j = 0`
  needs 3a for `y = x_1`, which needs `x_1 ~ x_1^2`, that is, a term `x_2`. And
  `x_1 = diag(2,1)` is not conjugate to its square. So the proof uses the chain
  beyond the term being killed, and finite chains in linear groups need not be
  trivial. The theorem is about infinite forward chains only.
* The Baumslag--Gersten kernel `N = <a_j (j in Z) | a_(j+1)^(-1) a_j a_(j+1) = a_j^2>`
  is itself a nontrivial group containing a chain. By the theorem, `N` is not
  residually linear, residually solvable or residually periodic, which matches
  the known fact that every finite image of BG kills `a`.
