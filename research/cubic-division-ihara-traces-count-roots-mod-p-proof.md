---
rg: 2
id: cubic-division-ihara-traces-count-roots-mod-p-proof
kind: route
title: Fixed points of a unit on lines and vectors mod p are read off its reduced characteristic polynomial; Dedekind--Kummer and Chebotarev do the rest
target: cubic-division-ihara-traces-count-roots-mod-p
requires: [cubic-division-congruence-sc-descends-to-thin-subgroups, free-group-ihara-bass-outlier-trace-criterion]
---

**Part 1.**  `Q(w)` is a commutative subalgebra of the division algebra `D`, so it is a field.
The degree of a subfield of a central division algebra of degree 3 divides 3.  If
`Q(w) = Q`, then `w^3 = Nrd(w) = 1` with `w in Q`, so `w = 1`.  So for `w != 1`, `[Q(w) : Q] = 3`.
The reduced characteristic polynomial is monic of degree 3 and kills `w`, so it is the minimal
polynomial and is irreducible.  Its coefficients are `Trd(w)`, `Nrd(w) Trd(w^-1) = Trd(w^-1)` and
`Nrd(w) = 1`.  They are integers because `w` and `w^-1` lie in `O_D`.  An irreducible cubic has no
rational root, so `Delta(w) = f_w(1) != 0`.  Finally `f_w(1) = det(1 - w)` in any splitting.

**Reduction.**  For `p` not dividing `disc(D)`, `O_D (x) Z_p = M_3(Z_p)`, and under this
isomorphism `Nrd = det` and `Trd = tr`.  So the characteristic polynomial of `w mod p` in
`SL_3(F_p)` is `f_w mod p`.

**Part 2.**  A line `F_p v` is fixed by `g = w mod p` iff `v` is an eigenvector with eigenvalue in
`F_p`.  Summing over eigenvalues, `#Fix_(P^2)(g) = sum_lambda #P(ker(g - lambda)) =
sum_lambda (p^(d_lambda) - 1)/(p - 1)`, and `d_lambda >= 1` iff `f_w(lambda) = 0 mod p`.  The character of
`l^2(P^2(F_p))` is `#Fix`.  The trivial summand has character 1, so `chi_(rho_p) = #Fix - 1`.
`rho_p` is irreducible of dimension `p^2 + p`, by the 2-transitivity of `SL_3(F_p)` on `P^2(F_p)`.
It is pulled back along `H -> SL_3(F_p)`, which is onto for `p` not in `P_H`.
- If `p` does not divide `disc(f_w)`, then `f_w mod p` is separable, each root has `d_lambda = 1`,
  and `#Fix = r_p(w)`.
- For the Artin representation: `disc(f_w) = [O_(E_w) : Z[w]]^2 disc(E_w)`.  So `p` is unramified in
  `E_w` and does not divide the index.  By Dedekind--Kummer the primes of `E_w` above `p` of residue
  degree 1 correspond to the roots of `f_w` mod `p`, and that number is the number of roots fixed by
  `Frob_p`.  That is the permutation character of `Gal` on the three roots, so
  `r_p(w) - 1 = tr rho_(E_w)(Frob_p)`.  The identity `L(s, rho_(E_w)) = zeta_(E_w)(s)/zeta(s)` is
  Artin induction from `Gal(L/E_w)`.

**Part 3.**  `#Fix_(F_p^3 minus 0)(g) = |ker(g - 1)| - 1 = p^(d_1) - 1`, so `chi_(sigma_p) = p^(d_1) - 2`.
- `d_1 >= 1` iff `det(1 - g) = 0` iff `p | Delta(w)`.
- If `d_1 >= 2`, the eigenvalue 1 has multiplicity at least 2 and `det g = 1` forces the third
  eigenvalue to be 1.  Then `g - 1` is nilpotent of rank at most 1, i.e. `g` is a transvection or 1.
  The converse is clear.  `d_1 = 3` iff `g = 1`.
- **Decomposition.**  The scalars `F_p^x` act on `F_p^3 minus 0`, commuting with `G = SL_3(F_p)`.
  The `chi`-isotypic part consists of the functions with `f(tv) = chi(t) f(v)`, which is
  `Ind_P^G(chi o alpha)`.  Here `P` is the stabiliser of the line `F_p e_1` and `alpha(g)` is the
  scalar by which `g` acts on `e_1`.  For `chi = 1` this is `l^2(P^2(F_p))`.
- **Counting.**  Write `p^(d_1) - 2 = -1 + (p-1)[d_1 >= 1] + (p^2-p)[d_1 >= 2] + (p^3-p^2)[d_1 = 3]`.
  Checking `d_1 = 0, 1, 2, 3` gives `-1, p-2, p^2-2, p^3-2`.  Summing over `CR_n` gives the formula
  for `T_(sigma_p)(n)`.  The count of cyclically reduced words is
  `|CR_n| = 3^n + 1 + (1 + (-1)^n)`.

**Part 4.**  Apply the trace criterion with `k = 2` and `d = p^2 + p` (resp. `p^3 - 2`):
`E(n) = T(n) - d (1 + (-1)^n)`.
- (a) Part 4(a) of the criterion gives `|E(n)| <= 2d (sqrt 3 + delta)^n`.  Adding back
  `d (1 + (-1)^n) <= 2d` gives the stated bound.  For the converse, `E(n_p) <= T(n_p)` for even
  `n_p`, so the hypothesis gives `E(n_p) <= p^C (sqrt 3 + delta_p)^(n_p)`.  Part 4(b) of the
  criterion applies because `log d_p = O(log p)`.
- (b) Here `(p-1) N_p(n) + (p^2-p) U_p(n) + (p^3-p^2) I_p(n) - 3^n = E(n) + 2 + (-1)^n + (p^3 - 2)(1 + (-1)^n)`.
  The absolute value is at most `|E(n)| + 2p^3`, which gives the forward bound.  For the converse,
  at even `n` the added constant is positive.  So `E(n_p)` is at most the left side, and part 4(b)
  of the criterion applies.

**Part 5.**  The discriminants `disc(f_w)`, `w in CR_n`, are finitely many nonzero integers (part 1).
For `p` coprime to all of them and not in `P_H`, part 2 gives the Frobenius-trace formula.  Let `L`
be the compositum of the Galois closures of the `E_w`.
- **Chebotarev** (Neukirch, Algebraic Number Theory, Ch. VII, §13; import, not re-read) says that
  `Frob_p` equidistributes in `Gal(L/Q)` over primes in natural density.
- **Mean.**  The mean of the class function `tr rho_(E_w)` is `<rho_(E_w), 1> = 0`, since Galois acts
  transitively on the roots.
- **Mean square.**  For the real characters `tr rho_E`, the mean of the product is
  `<rho_E, rho_(E')> = dim Hom(rho_E, rho_(E'))`.
  - If `E` is an `S_3` field, `rho_E` is irreducible with kernel `Gal(L/L_E)`, where `L_E` is the
    Galois closure.  `L_E` contains exactly the three conjugates of `E`.  So `rho_E = rho_(E')` iff
    `E = E'` up to isomorphism, with `dim Hom = 1`.
  - If `E` is cyclic, `rho_E = chi + chi-bar` for the cubic characters cutting out `E`, so
    `dim Hom = 2` when `E' = E` and 0 otherwise.
  - Mixed types give 0.

  Summing over pairs of words gives `V_n = sum_E m_E c_n(E)^2`.
- **Lower bound.**  `E_w` depends only on the `H`-conjugacy class of `w` and is unchanged by
  `w -> w^-1`.  The `n` cyclic rotations of a primitive cyclically reduced word are distinct, so
  every class of such words contributes at least `n^2` to `V_n`.  There are
  `(1 + o(1)) 3^n / n` classes.
