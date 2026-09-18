---
rg: 2
id: u3-q-in-kronecker-integral-units-needs-a-torus-proof
kind: route
title: Unique unipotent roots bound the centre, torsion quotients kill it, and without a torus the centre is unipotent
target: u3-q-in-kronecker-integral-units-needs-a-torus
requires: []
---

Lane proof, not independently reviewed. Notation as in the target. Write
`x^a = e_12(a)`, `y^b = e_23(b)`, `z^c = e_13(c)`, so `[x^a, y^b] = z^(ab)`, and
`H_N = <x^(1/N), y^(1/N)> ≅ H_3(Z)`.

**Part 1.** Let `u` have level `k` and matrix `u_0 in GL_r(Z)`, unipotent and not
`1`. Put `N_0 = log u_0`, a nonzero nilpotent rational matrix. For `q in Q`,
`exp(q N_0)` is the unique unipotent matrix whose `n`-th power is `exp(qn N_0)`.
- Suppose `v in GL_Kr` is unipotent with `v^n = u`. At any level `k' >= k` where
  `v` lives, `u` has matrix `I_m ⊗ u_0`. Its unique unipotent `n`-th root is
  `I_m ⊗ exp(N_0/n)`, so this is the matrix of `v`, and it is integral exactly when
  `exp(N_0/n)` is.
- More generally, `exp(q log u)` lies in `GL_Kr` iff `exp(q N_0) in GL_r(Z)`.

So `P = {q : exp(q N_0) in GL_r(Z)}` is a subgroup of `Q` containing `Z`, because
`exp(qN_0) exp(q'N_0) = exp((q+q')N_0)`.
- Pick `(i, j)` with `(N_0)_(ij) != 0`. Then `f(q) = exp(q N_0)_(ij) - delta_ij` is
  a polynomial with `f(0) = 0` and linear coefficient `(N_0)_(ij) != 0`, and
  `f(q) in Z` for every `q in P`.
- If `1/n in P` for infinitely many `n`, the integers `f(1/n)` tend to `0`. So
  `f(1/n) = 0` for infinitely many `n`, hence `f = 0`, a contradiction.

A subgroup of `Q` containing `1` and only finitely many `1/n` is `(1/N)Z`: if a
reduced fraction `a/b` is in it, so is `1/b`. ∎

**Part 2.** Let `U = U_3(Q)` and suppose `U/K` is torsion.
- Given `c in Q`, choose `n >= 1` with `x^n in K`: `x` has finite order modulo `K`.
- Then `[x^n, y^(c/n)] = z^c` lies in `K`, since `K` is normal.
- So `z^Q <= K`, and `U/K` is a quotient of `U/z^Q = Q^2`, which is abelian. ∎

**Part 3.** Suppose every `psi(g)` has only roots of unity as eigenvalues. Each
`H_N` is finitely generated, so `psi(H_N)` lies in some finite stage
`GL_(r_k)(Z)`. Take `N_j = j!` with levels `k_1 <= k_2 <= ...`, and let `G_j` be
the Zariski closure of `psi(H_(N_j))` in `GL_(r_(k_j))(C)`, with identity
component `G_j°` and `pi_j: H_(N_j) -> G_j / G_j°`, a finite nilpotent group.

**(a) Tori vanish.** `G_j` is nilpotent, so `G_j° = T × W`, with `T` a central
torus, `W` unipotent, and projection `p: G_j° -> T` a homomorphism.
- `Gamma = psi(H_(N_j)) ∩ G_j°` has finite index in `psi(H_(N_j))`, so it is
  finitely generated and Zariski dense in `G_j°`.
- For `g in Gamma`, `p(g)` is the semisimple part of `g`. Its eigenvalues are
  roots of unity of degree at most `r = r_(k_j)`, so their orders are bounded by
  some `e(r)`.
- So `p(Gamma)` is a finitely generated abelian group of bounded exponent, hence
  finite. It is also dense in the connected group `T`, so `T = 1`, and `G_j°` is
  unipotent.

**(b) Compatibility.** For `j < j'`, the map `A -> I ⊗ A` is a closed embedding of
algebraic groups. It sends `G_j` onto the Zariski closure of `psi(H_(N_j))` at
level `k_(j')`, and `G_j°` into `G_(j')°`. So `ker pi_j <= ker pi_(j')`.
- The union `K = ∪_j ker pi_j` is an increasing union of subgroups, each normal in
  `H_(N_j)`, so `K` is normal in `U_3(Q) = ∪_j H_(N_j)`.
- `U_3(Q)/K` is torsion, because each `pi_j` has finite image.

**(c) Conclusion.** By part 2, `z^c in K` for every `c in Q`. So for each `c`
there is a `j` with `psi(z^c) in G_j°`, which is unipotent by (a). Hence `psi(z)`
is unipotent, and `psi(z)` is not `1` because `psi` is injective. Its roots
`psi(z^(1/n))` are unipotent for all `n`, and they lie in `GL_Kr`. This
contradicts part 1. ∎

**The rational model.** An integral Kronecker-compatible form of
`lambda ⊗ rho` would be an injective homomorphism `U_3(Q) -> GL_Kr` in which
`z^c` acts by `1 ⊗ e_13(c)`, which is unipotent for all `c`. This already
contradicts part 1, without parts 2 and 3.
