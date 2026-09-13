---
rg: 2
id: group-corner-decoders-split-into-coset-and-matrix-readouts-proof
kind: route
title: Answer projections sit under the readouts of shared subgroups, and the Weyl representation identifies a Heisenberg corner with a full matrix algebra
target: group-corner-decoders-split-into-coset-and-matrix-readouts
requires:
  - group-corner-exact-compilers-force-source-affine-safety
  - coset-refinement-forces-rectangular-central-splitting
  - hidden-labels-import-cross-context-commutation
  - matrix-conj-forces-unsafe-support
---

Notation as in `group-corner-decoders-split-into-coset-and-matrix-readouts`.

## Two lemmas

**Lemma A (faithfulness).** For `x = sum_g x_g g in C[Gamma] p_omega`,
`tau_omega(x^* x) = n tau_Gamma(x^* x) = n sum_g |x_g|^2`. So an identity
between elements of `C[Gamma] p_omega` that holds in the GNS representation of
`tau_omega` holds in `C[Gamma] p_omega`, hence in every representation.

**Lemma B (intersections).** Fix a transversal `T` of `Gamma/<J>`. The
elements `g p_omega`, `g in T`, span `C[Gamma] p_omega`, and they are
orthonormal for `tau_omega`: `tau_omega((g p_omega)^* h p_omega)` is
`omega(g^(-1) h)` if `g^(-1) h in <J>` and `0` otherwise. As
`J^k p_omega = omega(J^k) p_omega`, for a subgroup `S` the span
`C[S] p_omega` is spanned by the basis vectors with `g in T cap S<J>`.
Intersecting spans of subsets of one basis gives

```text
C[S_1] p_omega cap C[S_2] p_omega = C[S_1<J> cap S_2<J>] p_omega.        (P1)
```

## Proof of (CD0)

Let `A` be finite abelian. The `e_chi`, `chi in A^`, are orthogonal
projections with sum `p_omega`. If `a in A cap <J>` then `a e_chi = chi(a) e_chi`
and `a p_omega = omega(a) p_omega`, so `e_chi = 0` unless `chi in X_A(omega)`.
By (CS1), `tau_omega(e_chi) = |A cap <J>|/|A| > 0` for `chi in X_A(omega)`.
So `C[A] p_omega` is the direct sum of the lines `C e_chi`,
`chi in X_A(omega)`, all nonzero, and a self-adjoint unitary in it has the
form (CD0) with unique signs.

## Proof of (CD1)

Fix `c != c'` and put `H = H_(cc')`, a finite abelian group. For
`psi in X_H(omega)` let `f_psi = (1/|H|) sum_(h in H) conj(psi(h)) h p_omega`.

**Answer projections sit under shared readouts.** Let `chi in K_c`. Since
`chi = omega` on `A_c cap <J>`, the extension `chi~(a J^k) = chi(a) omega(J^k)`
is well defined, and `h e_chi = chi~(h) e_chi` for `h in A_c<J>`. So
`f_psi e_chi = e_chi` if `psi = chi~|_H` and `0` otherwise. Distinct `f_psi`
are orthogonal, and all these elements lie in the commutative algebra
`C[A_c<J>] p_omega`. Hence

```text
e_chi e_(chi') = e_chi f_psi f_(psi') e_(chi') = 0
whenever psi = chi~|_H != chi'~|_H = psi'.                                 (P2)
```

**Item 1.** Perfection says `sum_(phi notin C_c) Q_(c,phi) = 0`, where
`Q_(c,phi) = sum_(D_c(chi) = phi) e_chi` by (CD0). Every `e_chi` with
`chi in K_c` is nonzero, so `D_c(chi) in C_c`.

**Item 2.** Choose base points `chi_c^0`, `chi_(c')^0`, so that
`K_c = chi_c^0 Ann(A_c cap <J>)`. For `alpha in Ann(A_c cap <J>)` let
`alpha°(a J^k) = alpha(a)`, a homomorphism on `A_c<J>`, so that
`(chi_c^0 alpha)~ = chi_c^0~ alpha°`. Then `R_(cc')` is the set of
`(alpha, alpha')` with

```text
alpha°|_H conj(alpha'°|_H) = conj(chi_c^0~|_H) chi_(c')^0~|_H,
```

the preimage of one point under a homomorphism into `H^`. It is nonempty:
otherwise (P2) gives `p_omega = (sum_chi e_chi)(sum_(chi') e_(chi')) = 0`,
contradicting `tau_omega(p_omega) = 1`. So `R_(cc')` is a coset of a subgroup
of `K_c x K_(c')`.

For acceptance, let `v in V_c cap V_(c')`. By abelian readouts and (P1),
`x_v in C[A_c] p_omega cap C[A_(c')] p_omega = C[H] p_omega`. As in (CD0),
`x_v = sum_psi s_v(psi) f_psi` with signs `s_v(psi)`, so
`x_v e_chi = s_v(chi~|_H) e_chi`. By (CD0) also
`x_v e_chi = (-1)^(D_c(chi)_v) e_chi`, and `e_chi != 0`. So
`(-1)^(D_c(chi)_v) = s_v(chi~|_H)`, and likewise for `c'`. For
`(chi, chi') in R_(cc')` the two restrictions to `H` agree, so
`D_c(chi)_v = D_(c')(chi')_v`. Thus `(beta_c x beta_(c'))(R_(cc'))` lies in the
accepting set of `G_B` on `(c,c')`, pairs agreeing on `V_c cap V_(c')`.
With item 1 this is a coset refinement; transposition symmetry is built into
(CD1a).

**Item 3.** For each `c` the `e_chi`, `chi in K_c`, form a PVM with sum
`p_omega`, and (P2) is relation (CS) of
`coset-systems-are-torsor-isomorphism-games` for `R`. The universal property
of `A(R)` gives `Psi : A(R) -> p_omega C*(Gamma) p_omega` with
`Psi(p_c^chi) = e_chi`. It sends `P_c^a = sum_(beta_c(chi) = a) p_c^chi` to
`Q_(c,a)`, the joint spectral projection of `(x_v)_(v in V_c)` at `a`, by
(CD0). So `tau_omega o Psi` is a tracial state of `A(R)` whose pullback to
`A(G_B)` is the source trace of the decoder, and (RCS) and (HL) apply to it.

## Proof of (CD2)

Let `X e_j = e_(j+1)` and `Z e_j = zeta^j e_j` on `C^d`, with
`zeta = exp(2 pi i/d)`. Then `Z^b X^(a') = zeta^(b a') X^(a') Z^b`, so
`pi(a,b,k) = zeta^k X^a Z^b` satisfies

```text
pi(a,b,k) pi(a',b',k') = zeta^(k+k'+b a') X^(a+a') Z^(b+b') = pi((a,b,k)(a',b',k')),
```

and `pi` is a unitary representation of `H_d` with `pi(J) = zeta`. So
`pi(p_omega) = (1/d) sum_k zeta^(-k) zeta^k = 1`, and `pi` restricts to a unital
*-homomorphism `C[H_d] p_omega -> M_d(C)`. The `d^2` matrices `X^a Z^b` satisfy
`Tr((X^a Z^b)^* X^(a') Z^(b')) = d delta_(aa') delta_(bb')`, so they are linearly
independent and `pi` is onto. By Lemma B, `dim C[H_d] p_omega = |H_d|/d = d^2`,
so `pi` is an isomorphism. `M_d(C)` has exactly one tracial state, so `pi`
carries `tau_omega` to `tr_d`. A perfect model `(x_v)` in `M_d(C)` pulls back
to self-adjoint unitaries `pi^(-1)(x_v)` satisfying the same identities.

## Proof of (CD3)

In the model test of `hidden-labels-import-cross-context-commutation`, in the
basis `e_00, e_01, e_10`, `X_u = diag(1,1,-1)`, `X_w = diag(1,-1,1)`, `X_y`
swaps `e_00` and `e_01`, and `X_z` swaps `e_00` and `e_10`. Every context
commutes with allowed spectrum; the symmetries generate `M_3(C)`, so
`W*(P_c, P_(c'), P_(c''))` is a factor; and `[X_u, X_z]` and `[X_w, X_y]` are
nonzero. By (CD2) with `d = 3` this model is an exact decoder into
`C[H_3] p_omega`. Corollary 1 of that claim says its trace factors through no
coset refinement. An abelian-readout decoder inducing the same source trace
would, by item 3 of (CD1), give such a factorization. The second bullet of
(CD3) is (CD2).

## Proof of (CD4)

Let the decoder of `B_0` land in `C[Gamma_0] p_(omega_0)`, with `J_0` of order
`n_0`, and the model of `F` in `C[Gamma_1] p_(omega_1)` for a finite group
`Gamma_1` (for instance `H_d` via (CD2)), with `J_1` of order `n_1`. In
`G = Gamma_0 x Gamma_1` put `Z = <J_0> x <J_1>`, `omega = omega_0 (x) omega_1`
and `K = ker omega`.
- The image of `omega` is a finite subgroup of the circle, so `Z/K` is cyclic
  and `omega` induces a faithful character `omega~` of it. Let `J` generate
  `Z/K <= Gamma := G/K`; its order is exactly `|Z/K|`.
- With `p_K = (1/|K|) sum_(k in K) k`, the quotient map gives
  `C[G] p_K ~= C[Gamma]`, with `tau_G(x p_K) = tau_Gamma(x~)/|K|`. As `omega`
  is trivial on `K`, `p_omega <= p_K`, and `p_omega` maps to `p_(omega~)`.
  So `C[G] p_omega ~= C[Gamma] p_(omega~)`, and the normalized traces agree.
- `p_omega = p_(omega_0) p_(omega_1)`, and
  `C[G] p_omega = C[Gamma_0] p_(omega_0) (x) C[Gamma_1] p_(omega_1)`. The
  elements `x_v p_(omega_1)` and `y_w p_(omega_0)` satisfy the identities of
  `B_0 disjoint-union F`, since each context lies in one part.
- If `x_v in C[A_c] p_(omega_0)`, then `x_v p_(omega_1)` lies in
  `C[A_c x 1] p_omega`, and the image of `A_c x 1` in `Gamma` is finite
  abelian. So abelian readouts are preserved.

Restricting a decoder of the union to the variables of `B_0` gives the
converse.

For the magic-square block, let `Gamma_1` be the central product of two
dihedral groups of order 8, generated by involutions `A, B, D, E` and central
`J` of order 2, with `AE = J EA`, `BD = J DB` and every other pair commuting.
It has order 32, and the two-qubit Pauli representation is faithful with
`J = -1`. Put `C = AB`, `F = DE`, `G = AD`, `H = BE`, `I = GH`. By
(UTC2)--(UTC4) of `matrix-conj-forces-unsafe-support`, rows and columns
commute with the required products, so each row and column generates with
`J` a finite abelian subgroup, read with the identity decoder. The AND context
`(A,B,Y)` reads from `A_c = <A,B,J>`: `K_c` is the four sign pairs `(a,b)`,
`D_c(a,b) = (a, b, ab)` in bits, and `x_Y = p_omega - 2 e_(1,1)`, which is
(UTC5).

## Proof of (CD5)

For a finite central `Z` and a character `omega` of `Z`, put
`p_omega = (1/|Z|) sum_z conj(omega(z)) z`. This is a central projection with
`tau_Gamma(p_omega) = 1/|Z|`. For `a in Gamma`,
`|Z| tau_Gamma(a p_omega) = omega(a)` if `a in Z` and `0` otherwise. The
proofs of (CS1) and (CS2) go through verbatim with `A cap Z` in place of
`A cap <J>`, and they never use faithfulness of `omega`.

Now let `p_Omega = sum_(omega in Omega) p_omega`, a sum of orthogonal central
projections. Each `tau_omega = |Z| tau_Gamma(p_omega . p_omega)` is a tracial
state of `p_Omega C*(Gamma) p_Omega`, with `tau_omega(p_Omega) = 1`. An affine
decoder exact on every trace of this corner is exact on `tau_omega`, and the
(CS2) argument gives the affine-safe support `D_c(X_(A_c)(omega))`.
