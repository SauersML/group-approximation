---
rg: 2
id: simple-mf-group-with-full-compression-defect-proof
kind: route
title: Represent an amenable lamplighter cell in the commutator unitary group of the universal UHF algebra, pass to the simple quotient and a countable simple hull, and read off MF from UHF
target: simple-mf-group-with-full-compression-defect
requires:
  - schafhauser-amenable-cstar-embeds-in-universal-uhf
  - chand-robert-du0-simple-mod-center
artifacts:
  - experiments/simple-mf-defect-2026-09-17/check_cell.py
---

Notation is that of the target.  `Q` is the universal UHF algebra,
`Q = closure of the union of Q_m`, with `Q_m = M_(m!)` and unital
inclusions.  `T` denotes the scalar unitaries.  Imported:

- (SB) `schafhauser-amenable-cstar-embeds-in-universal-uhf`: for
  countable amenable `G` there is a trace-preserving, hence unital,
  embedding `C*_r(G) -> Q`;
- (CR) `chand-robert-du0-simple-mod-center`: for
  simple unital `A`, the abstract group `DU_0(A)/Z(DU_0(A))` is simple.

Every other input is proved in place or is textbook.

## Step 1. The amenable cell group `P`

Let `Omega = Z x {1,2}` and let `FAlt(Omega)` be the group of even
finitary permutations.  Define `u(n,1) = (n+1,1)`, `u(n,2) = (n-1,2)` and
`sigma(n,i) = (n,3-i)`.  Put `P = FAlt(Omega) <u, sigma>`, which is
countable.  `FAlt(Omega)` is normal in `P`.

**Relation (P1).** `sigma u sigma^-1 = u^-1`, so `[sigma, u] = u^-2`.  Thus
`<u, sigma>` is infinite dihedral and `P` is (locally finite)-by-(virtually
cyclic).  In particular `P` is elementary amenable, hence amenable.

**The cell.**  Take `c = (-4,-3,-2)` and `l = (0,1,2)`, both 3-cycles on
copy 1, and the compressor `w = u^2`.  Put `L = < w^k l w^-k : k >= 0 >`.

- `w L w^-1 <= L` by construction.
- `w^k l w^-k` is the 3-cycle `(2k, 2k+1, 2k+2)` on copy 1.  For `k >= 0`
  its support is disjoint from that of `c`, so `c` lies in `C_P(L)`.
- `w c w^-1 = (-2,-1,0)`.  It shares exactly one point with `l`, so
  `delta = [w c w^-1, l]` is a nontrivial even permutation supported in
  `F_5 = {-2,...,2} x {1}`.

**Everything lies in `[P,P]`.**  `FAlt(Omega)` is the union of the groups
`Alt(F)` over finite sets `F` with `|F| >= 5`.  Each `Alt(F)` is perfect, so
`FAlt(Omega) = [FAlt(Omega), FAlt(Omega)] <= [P,P]`.  By (P1),
`w = u^2 = [sigma,u]^-1` lies in `[P,P]`.  So `c`, `l`, `w`, `L` and
`delta` all lie in `P_0 = [P,P]`.  `L` lies in the finitary alternating
group of `N x {1}`, so it is locally finite.

The artifact `check_cell.py` verifies (P1) on a window, the disjointness
and commutation for `k = 0..199`, the nontriviality and evenness of
`delta`, and that `delta` is not central in `Alt(F_5)`.  The proof above
does not depend on the computer.

## Step 2. An exact unitary representation in `DU_0(Q)`

By (SB) there is a unital injective `*`-homomorphism
`iota : C*_r(P) -> Q`.  Put `rho(g) = iota(lambda_g)`.  Then
`rho : P -> U(Q)` is an injective group homomorphism.  Injectivity holds
because `lambda` is injective on `P` and `iota` is injective.

**`U(Q) = U_0(Q)`.**  Let `v` be a unitary of `Q`.  Choose `m` and `y` in
`Q_m` with `||v - y|| < 1/2`.  Then `y` is invertible, and its polar part
`y|y|^-1` is a unitary `v'` in `Q_m` with `||v - v'|| < 1`.  The spectrum
of `v^* v'` omits `-1`, so `v^* v' = exp(ih)` for some self-adjoint `h`, by
the continuous logarithm.  Also `v' = exp(ik)` with `k = k^*` in
`M_(m!)`.  Both `exp(ith)` and `exp(itk)` are paths to `1`.  So
`U(Q) = U_0(Q)`, and `D(U(Q)) = DU_0(Q)`.

Hence `rho(P_0) = rho([P,P]) <= [U(Q), U(Q)] = DU_0(Q)`.

## Step 3. The center of `DU_0(Q)` is scalar

Let `z` be in `Z(DU_0(Q))`.  For each `m`,

```text
D(U(M_(m!))) = SU(m!) <= DU_0(Q).
```

For `d >= 2`, `SU(d)` acts irreducibly on `C^d`: it is transitive on the
unit sphere.  Its linear span is an algebra, since `SU(d)` is closed under
products.  An irreducible algebra is all of `M_d` by Burnside's theorem.
So `z` commutes with `M_(m!)` for every `m >= 2`.  It therefore commutes
with a dense subalgebra of `Q`, so it lies in the center of the simple
unital algebra `Q`, which is `C 1`.  So `z` is in `T 1`, and

```text
Z(DU_0(Q)) = DU_0(Q) cap T1.
```

## Step 4. The simple quotient `G_1`

Put `G_1 = DU_0(Q) / (DU_0(Q) cap T1)` and let `pi` be the quotient map.
By (CR) and Step 3, `G_1` is simple.  Put `U = pi rho(w)`,
`C = pi rho(c)`, `Lambda = pi rho(l)` and
`L_1 = pi rho(L) = < U^k Lambda U^-k : k >= 0 >`.

- The relations `U L_1 U^-1 <= L_1` and `C in C_(G_1)(L_1)` are images of
  relations in `P`.
- `[U C U^-1, Lambda] = pi rho(delta)`.

Suppose `pi rho(delta) = 1`.  Then `rho(delta)` is a scalar, so it commutes
with `rho(Alt(F_5))`.  Since `rho` is injective, `delta` would be central
in `Alt(F_5)`, which is centerless.  This is a contradiction.  So the cell
survives in `G_1`.

## Step 5. A countable simple hull `S`

Let `H_0 = pi rho(P_0)`, a countable group.  Given a countable `H_n`, do the
following for each pair `(x, y)` in `H_n` with `x != 1`.  Simplicity of
`G_1` gives finitely many `g_1, ..., g_r` in `G_1` and signs `e_i` with

```text
y = prod_i g_i x^(e_i) g_i^-1 .
```

Fix one such choice.  Let `H_(n+1)` be generated by `H_n` and all the
chosen `g_i`.  This is again countable.  Put `S = union of the H_n`.

Take `x != 1` and `y` in `S`.  Both lie in some `H_n`, so `y` is a product
of conjugates of `x^(+-1)` by elements of `H_(n+1) <= S`.  Hence `S` is
simple.

The elements `U`, `C` and `Lambda` lie in `H_0 <= S`.  The group
`L_1 <= S`, together with the relations of Step 4, is a cell in `S` with
`[U C U^-1, Lambda] != 1`.  So `D_S(L_1)` is a nontrivial normal subgroup of
the simple group `S`, and hence `D_S(L_1) = S`.  The group `H_0` is
isomorphic to the elementary amenable group `P_0`.  Indeed, if
`rho(g) = iota(lambda_g)` is a scalar, then `lambda_g` is a scalar by
injectivity of `iota`, and evaluating at `delta_e` forces `g = e`.  So
`H_0` contains the cell.
This proves items 1, 2 and 4 of the target, with `(u, c, l)` of the
target equal to `(U, C, Lambda)`.

## Step 6. `S` is MF

**Tensor trick.**  Let `Qbar` be the conjugate algebra, which is again UHF,
and let `A = Q (x) Qbar`, which is UHF.  The map

```text
theta : U(Q) -> U(A),   x |-> x (x) xbar
```

is a homomorphism, and it is trivial on `T1` because
`lambda x (x) conj(lambda) xbar = |lambda|^2 x (x) xbar`.  Its kernel is
exactly `T1`.  Suppose `x (x) xbar = 1 (x) 1`.  Choose a state `phi` on
`Qbar` with `phi(xbar) != 0` and apply the slice map `id (x) phi`.  This
gives `phi(xbar) x = 1`, so `x` is a scalar.  Hence `theta` induces an
injective homomorphism `G_1 -> U(A)`, and `S` embeds in `U(A)`.

**AF algebras are norm-corona algebras.**  Write `A = closure of the union
of A_n`, with `A_n = M_(k_n)` finite-dimensional, unital and increasing.
Finite-dimensional C\*-algebras are injective, so by Arveson extension there
are unital completely positive contractions `E_n : A -> A_n` with `E_n = id`
on `A_n`.  Define

```text
Phi : A -> prod_n A_n / directSum_n A_n ,   Phi(a) = [ (E_n(a))_n ] .
```

`Phi` is linear, `*`-preserving and contractive.  Take `a, b` in some
`A_m`.  Then `E_n(ab) = ab = E_n(a) E_n(b)` for `n >= m`.  So `Phi` is
multiplicative on the dense subalgebra `union A_m`, and by continuity it is
multiplicative everywhere.  Moreover `||Phi(a)|| = limsup_n ||E_n(a)|| =
||a||` on `union A_m`, so `Phi` is isometric.  Hence `Phi` is a unital
injective `*`-homomorphism, and it restricts to an injective group
homomorphism `U(A) -> U(prod_n M_(k_n) / directSum_n M_(k_n))`.

Composing gives an embedding of `S` into the norm-corona unitary group, so
`S` is MF.  In particular `Rad_MF(S) = 1`, which is item 3.

**Hyperlinearity (remark).**  The unique trace of `A` generates the
hyperfinite II_1 factor `R`, so `S <= U(A) <= U(R)` is hyperlinear.

## What is not claimed

- `S` is not shown to be finitely generated, finitely presented, sofic or
  torsion-free.
- `S` is not Kazhdan: Kazhdan groups are finitely generated.  So there is no
  tension with the manuscript criterion.
- The MF models of `S` must, by
  `compression-exact-models-kill-defect-generated-groups` (C) applied to a
  finite marking, violate exact normalization of the core algebra by the
  compressor at every large scale.  This is a consequence and is not used.
