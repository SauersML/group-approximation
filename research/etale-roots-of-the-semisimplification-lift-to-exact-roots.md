---
rg: 2
id: etale-roots-of-the-semisimplification-lift-to-exact-roots
kind: claim
title: Over a complete discrete valuation ring a reduced root at which the Fox-derivative operator is invertible lifts to an exact root, so a tuple over an algebraically closed field of characteristic zero has exact amplified roots whenever its semisimplification has an etale amplified root
distinct_from:
  congruence-constants-have-exact-nonsingular-roots: that is the case where the reduced constants and the reduced root are 1, so the operator is m times the identity; this allows any reduced constants and root, and in characteristic 0 degenerates a tuple to its semisimplification.
  amplified-algebraic-roots-in-characteristic-zero: that is the premise for every tuple; this reduces exact roots of a tuple to an invertibility condition at its semisimplification, which is not known for every semisimple tuple.
---

**ESTABLISHED** through
`etale-roots-of-the-semisimplification-lift-to-exact-roots-proof` (successive
approximation, a one-parameter degeneration, and the weak Nullstellensatz;
unreviewed, no novelty claimed).

**Setup.**
- `A` is a complete discrete valuation ring with uniformizer `pi` and residue
  field `kappa`, and `Gamma_j = 1 + pi^j M_N(A)`.
- `w = y_1 ... y_l` in `F_k * <x>` has exponent sum `m` in `x`.
- For `T` in `GL_N(kappa)` and `c` in `GL_N(kappa)^k`, `S_i` is the value of
  `y_{i+1} ... y_l` at `(T ; c)`. Define `D_{T,c} : M_N(kappa) --> M_N(kappa)` by
  `D_{T,c}(Y) = sum over y_i = x of S_i^{-1} Y S_i - sum over y_i = x^{-1} of S_{i-1}^{-1} Y S_{i-1}`.

This is the adjoint action of the Fox derivative of `w` in `x`, and
`D_{1,1} = m id`. A root `T` of `w(T ; c) = 1` is *etale* if `D_{T,c}` is
invertible.

**Theorem E.** Let `c` be in `GL_N(A)^k` and `T_0` in `GL_N(A)`, with
`w(T_0 ; c)` in `Gamma_1` and `D_{T_0 mod pi, c mod pi}` invertible. Then there
is exactly one `T` in `T_0 Gamma_1` with `w(T ; c) = 1`.

**Corollary F (characteristic 0).** Let `L` be algebraically closed of
characteristic `0`, let `a` be in `GL_n(L)^k`, and fix a flag of
`a`-invariant subspaces, for instance a composition series. In an adapted
basis every `a_i` is block upper triangular; let `a^ss` be the block diagonal
part. If for some `r >= 1` the equation `w(T ; a^ss (x) 1_r) = 1` has an etale
root in `GL_{nr}(L)`, then `w(T ; a (x) 1_r) = 1` has a root in `GL_{nr}(L)`.

**Examples.**
1. *Unipotent tuples.* The flag is full, `a^ss = 1`, `T_0 = 1` and `D = m id`.
   This gives Corollary C of `congruence-constants-have-exact-nonsingular-roots`
   without p-adic fields.
2. *Triangular tuples.* Let `d` be the diagonal part and `T_0` a diagonal root
   of `w(T_0 ; d) = 1`. Then `D` multiplies the matrix unit `E_pq` by
   `s_pq = sum over y_i = x of psi_pq(S_i) - sum over y_i = x^{-1} of psi_pq(S_{i-1})`,
   where `psi_pq(S) = S_qq / S_pp`. Also `s_pp = m`. So an exact root exists
   whenever `s_pq != 0` for all `p != q`.
3. *Invertibility is sufficient, not necessary.* Take `a = diag(2, 1)`,
   `b = 1 + E_12` and `w = x^2 a x^{-1} a^{-1} b`.
   - At `a^ss = (diag(2, 1), 1)`, the diagonal root `T_0 = 1` has
     `s_12 = 1 + 1 - 2 = 0`.
   - No upper triangular `T` is a root for `(a, b)`.
   - Yet `T = [[5/2, -4/3], [9/2, -2]]` is an exact root over `Q`.

**Exact gap left.** Corollary F moves the characteristic-0 premise, for exact
roots, to semisimple tuples: does every semisimple tuple have an etale root
after amplification? Unitary tuples have roots by Gerstenhaber--Rothaus
(`kervaire-laudenbach-holds-for-hyperlinear`), but whether some root is etale
is not known here. The approximate, rank-metric premise is not reduced by
this argument.
