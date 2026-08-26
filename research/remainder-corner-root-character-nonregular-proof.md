---
rg: 2
id: remainder-corner-root-character-nonregular-proof
kind: route
title: Finite-dimensional fibers kill a nonzero ideal on each root subgroup; countably many ideals; Euclid on exponent vectors
target: remainder-corner-root-character-is-persistently-nonregular
requires:
  - kt-remainder-corner-characters-are-infinite-index-induced
  - model-characters-of-compressed-pairs-are-compression-invariant
---

**(1) The fiber kernel.**  `sigma_omega` is a finite-dimensional unitary
representation of `N_omega`, and `e_ij(I_omega) ~= (I_omega, +)` is an
infinite elementary abelian `p`-group inside `N_omega`.  An abelian group of
exponent `p` in `U(n)` is diagonalizable with entries in `mu_p`, hence
finite; so `sigma_omega` is trivial on `e_ij(A_omega)` for an additive
subgroup `A_omega <= I_omega` of finite index, in particular `A_omega != 0`.
Since `chi_omega` is a class function on `Gamma` vanishing off `N_omega` with
`chi_omega(n) = tr sigma_omega(n)/dim`, the set
`ker sigma_omega = {n : chi_omega(n) = 1}` is normal in `Gamma`.  Conjugating
by the signed permutation matrices of `EL_r` puts `e_kj(+-A_omega)` into it
for every `k != j`, and the commutator identity
`[e_ik(h), e_kj(a)] = e_ij(ha)` (`r >= 3`) then puts `e_ij(R_+ A_omega)` into
it.  So `J_omega = R_+ A_omega` is a nonzero ideal, contained in `I_omega`
(hence proper, containing no nonzero constant), with `chi_omega = 1` on
`e_ij(J_omega)`; its spectral measure `nu_omega` is therefore supported on
`J_omega^perp = {theta : theta|_(J_omega) = 0}`.

`R_+` is a countable Noetherian ring, so it has countably many ideals.  From
`nu = int nu_omega dmu` and `nu_omega(J_omega^perp) = 1` a.e. we get
`nu(union_J J^perp) = 1` over the countable set of nonzero proper ideals,
hence `nu(J^perp) > 0` for some such `J`.

`J^perp` is Haar-null on the nonzero coordinates: pick `0 != f in J`; `f` is
non-constant; for `k = 1, ..., n` the conditions `theta(x_1^k f) = 0` are
linear forms in the coordinates `theta_v`, `v != 0` (every monomial of
`x_1^k f` is non-constant), linearly independent because the polynomials
`x_1^k f` are, so their joint solution set has Haar measure `q^(-n)`; letting
`n -> infinity` gives measure `0`.

**(2)** If `nu` were `(law of theta_0) (x) Haar` on the nonzero coordinates,
then `nu(J^perp) = 0`, contradicting (1).  Since `psi = hat nu` determines
`nu`, and `psi'` is the Fourier transform of exactly that product measure
(`psi'(f)` depends only on the constant coefficient of `f`), `psi != psi'`,
and the two agree on constants by definition, so they differ at a
non-constant `f`.  On the tempered corner `chi` vanishes off the center, so
`psi(f) = 0 = psi'(f)` for non-constant `f` there.

**(3)** `psi o phi_A = psi` by
`model-characters-of-compressed-pairs-are-compression-invariant` (the corner
model is a model), and `psi' o phi_A = psi'` because a monomial substitution
fixes constant terms.  Hence `f in D` iff `phi_A(f) in D`.

**(4) Monomial lemma.**  Let `M = {v in N^d : x^v in J}`, an up-closed
subset of `N^d`, and put `T_ij = 1 + E_ij`, so `T_ij v = v + v_j e_i`.
Invariance `phi_(T_ij)^(-1)(J) = J` reads `v in M iff T_ij v in M`.  In
particular if `v in M` and `v_i >= v_j >= 1` then `v - v_j e_i in N^d` and
`T_ij(v - v_j e_i) = v`, so `v - v_j e_i in M`: `M` is closed under Euclidean
steps on any pair of coordinates.  Take `v in M`, `v != 0`, with `v_i >= 1`.
Up-closure gives `v + e_j in M` for `j != i`; Euclidean steps on `(i, j)`
starting from `(v_i, 1)` reduce the `i`-th coordinate to `0`, giving a
vector in `M` with `i`-th coordinate `0` and `j`-th coordinate `1`; then
adding `e_i` and one step on `(j, i)` from `(1, 1)` gives a vector with
`j`-th coordinate `0` and `i`-th coordinate `1`.  Repeating with the other
coordinates (each time reducing a coordinate `>= 1` against a coordinate
equal to `1`) produces `e_i in M`, then `e_i + e_k in M` and one Euclidean
step gives `e_k in M` for every `k`.  So `M` contains every `e_k`, hence by
up-closure every nonzero `v`; `J` contains the augmentation ideal, whose
colength is `1`.

For the kernel: `ker pi_chi` is normal in `Gamma` and, since `psi o phi_A =
psi`, satisfies `phi_A^(-1)(ker) = ker`; its sandwich ideal
`J = {f : e_ij(f) in ker}` inherits `phi_A^(-1)(J) = J`, and the lemma
applies.  The projective kernel `{g : pi(g) scalar}` is handled identically
with `|psi|` in place of `psi`.  In criterion form the kernel lies in the
finite core (`model-characters-of-compressed-pairs-are-compression-invariant` (2)),
so `J = 0`.
