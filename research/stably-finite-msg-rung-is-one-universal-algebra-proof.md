---
rg: 2
id: stably-finite-msg-rung-is-one-universal-algebra-proof
kind: route
title: Embed the stably finite targets into one product, read spectra there, and rerun the manuscript proper-isometry computation with the Kesten eigenprojection
target: stably-finite-msg-rung-is-one-universal-algebra
requires:
  - kesten-spectral-gap-replaces-kazhdan-projection-per-model
  - model-spectral-gap-quantifier-ladder
---

Notation is that of the target.  Three inputs are imported.
- Item 1 of `kesten-spectral-gap-replaces-kazhdan-projection-per-model`:
  in every Hilbert-space representation `pi` of `G`,
  `ker(1-pi(h_S))=Fix pi(L)`.  This is strict convexity, since `S`
  generates `L` and `e in S`.
- Item 1 of `model-spectral-gap-quantifier-ladder`: `(MSG)` on `L` in
  `C*_max(G)` holds if and only if `L` has `(T)`.
- The spectral fact that a unital `*`-homomorphism `phi` satisfies
  `sp(phi(a)) subset sp(a)`, with equality when `phi` is injective.

Two standard facts about finiteness are used; both are proved here.
- (F1) A unital C-star subalgebra of a finite (resp. stably finite)
  algebra is finite (resp. stably finite).  An isometry in `M_n(B)` is
  one in `M_n(A)`.
- (F2) The `l^infty` product `prod_i A_i` of finite (resp. stably finite)
  unital algebras is finite (resp. stably finite).  `M_n(prod A_i)`
  equals `prod M_n(A_i)`, and `v^*v=1` there means `v_i^*v_i=1` for
  every `i`, hence `v_iv_i^*=1` for every `i`, hence `vv^*=1`.

## Item 1

For `x in C[G]` put `||x||_SF = sup ||rho(x)||`, over all homomorphisms
`rho:G->U(A)` with `A` unital and stably finite.  The family is nonempty,
since the trivial character is such a target.  Each term is a C-star
seminorm bounded by `||x||_max`.  So `||.||_SF` is a C-star seminorm, and
it extends continuously to `C*_max(G)`.  Let `J` be its kernel and
`C*_SF(G)=C*_max(G)/J`, normed by `||.||_SF`.

*Reduction to a countable family.*  `C*_max(G)` is separable because `G`
is countable.  Fix a countable dense subset `D`.  For each `x in D` and
each `k>=1`, choose a target `rho_(x,k)` with
`||rho_(x,k)(x)|| >= ||x||_SF - 1/k`.  Let `R` be the resulting countable
family.  The seminorms `sup_(rho in R)||rho(.)||` and `||.||_SF` are both
`1`-Lipschitz for `||.||_max` and agree on `D`, so they agree everywhere.
Hence `C*_SF(G) -> prod_(rho in R) A_rho` is isometric.  By (F2) and
(F1), `C*_SF(G)` is stably finite.

*Factorization.*  Every stably finite target `rho` satisfies
`||rho(x)|| <= ||x||_SF`.  So `rho` factors as
`rho = rho_bar o q_SF`, with `q_SF:C*_max(G)->C*_SF(G)` the quotient map
and `rho_bar` a unital `*`-homomorphism.

*Equivalences.*  Write `y_SF=q_SF(h_S)`.
- (a) implies (b): the canonical map `G->U(C*_SF(G))` is itself a stably
  finite target.
- (b) implies (c): if `1` is not an accumulation point of `sp(y_SF)`,
  there is `c>0` with `sp(y_SF) cap (1-c,1)` empty.  For every target,
  `sp(rho(h_S)) = sp(rho_bar(y_SF))` is contained in `sp(y_SF)`.
- (c) implies (a): this is immediate.

The same argument with "finite" in place of "stably finite" proves the
`FIN` and `C*_fin(G)` version, using the finite halves of (F1) and (F2).

## Item 2

If `C*_max(G)` is stably finite, then the identity of `C*_max(G)` is a
stably finite target, so `||x||_max <= ||x||_SF <= ||x||_max`, and
`C*_SF(G)=C*_max(G)`.  By item 1, `SF(G,L)` is `(MSG)` on `L` in
`C*_max(G)`.  By the ladder, that holds if and only if `L` has `(T)`.  For
`FIN`, replace "stably finite" by "finite".

Residually finite-dimensional separable algebras are MF, and MF algebras
are stably finite.  These are the two facts quoted in the last sentence of
the proof of `prop:max-infinite` in `non_mf_groups_exist.tex`, with
citation `[BK]`.  This covers the examples in the target:
- `C*_max(F_2)` is residually finite-dimensional (Choi);
- `C*_max(BS(1,2))=C*_r(BS(1,2))`, by amenability, and it has a faithful
  tracial state.

## Item 3

Take `A`, `rho`, `(MSG)`, `P`, `t`, `u=rho(t)` and `q=uPu^*` as stated.
Represent `A` faithfully on `H`.  By item 1 of the per-model lemma, `P`
lies in `C*(rho(h_S)) subset A` and is the orthogonal projection onto
`Fix rho(L)`.  Since `u` is unitary, `q` is the projection onto
`u Fix rho(L) = Fix rho(tLt^-1)`.  Since `tLt^-1 <= L`, we get
`Fix rho(L) subset Fix rho(tLt^-1)`, so `P<=q`, `Pq=qP=P`, and `uP=qu`.

With `s=Pu^*+(1-q)`:
- `(1-q)uP = uP - quP = uP - uPu^*uP = 0`;
- `Pu^*(1-q) = ((1-q)uP)^* = 0`;
- `uP(1-q) = uP - uPq = 0`;
- `(1-q)Pu^* = (uP(1-q))^* = 0`.

Hence
```text
s^*s = (uP+(1-q))(Pu^*+(1-q)) = uPu^* + (1-q) = 1,
ss^* = (Pu^*+(1-q))(uP+(1-q)) = P + (1-q) = 1-(q-P).
```
This is the computation of `prop:max-infinite`, with the Kazhdan
projection replaced by `P`.  So `s` is an isometry, and it is proper
exactly when `q!=P`.

Suppose `q=P`.  Let `sigma` be any representation of `A` on `K`.  Since
`1` is not an accumulation point of `sp(rho(h_S))`, the function
`chi_{1}` is continuous on that spectrum.  So `sigma(P)=chi_{1}(sigma
rho(h_S))`, and `sp(sigma rho(h_S)) subset sp(rho(h_S))`.  This is the
projection onto `ker(1-sigma rho(h_S))`.  By strict convexity (item 1 of
the per-model lemma, applied to the representation `sigma rho` of `G`),
that kernel is `Fix sigma rho(L)`.  Likewise `sigma(q)` is the projection
onto `Fix sigma rho(tLt^-1)`.  So `q=P` gives
`Fix sigma rho(L) = Fix sigma rho(tLt^-1)`.

From `uPu^*=P` we get `u^kPu^-k=P` for every `k in Z`.  Hence
`sigma rho(t)` leaves `Fix sigma rho(L)` invariant.  For `k>=0`,
```text
Fix sigma rho(t^-k L t^k) = sigma rho(t)^-k Fix sigma rho(L) = Fix sigma rho(L).
```
Since `t^-k L t^k` increases with `k`, a vector is fixed by `L^infty_t`
exactly when it is fixed by every `t^-k L t^k`.  This gives the displayed
equalities.  No property `(T)` was used: the only spectral input is
`(MSG)` for `rho` itself.

## Item 4

Let `L'=tLt^-1`, a proper subgroup of `L`.  Let `lambda` be the
quasi-regular representation of `G` on `l^2(G/L')`, and let `xi` be the
point mass at the base coset `L'`.  Then `xi` is fixed by `L'`.  It is not
fixed by `L`, since any `l in L\L'` sends `L'` to `lL' != L'`.  So

```text
Fix lambda(L)  !=  Fix lambda(L').                                   (W)
```

This is the witness used in the proof of `prop:max-infinite`.

*`FIN` part.*  Suppose `A_q=A_q(G,L,t)` were finite.  The corestriction
`rho:G->U(A_q)` of `lambda` is then a finite target, so `FIN(G,L)` gives
`(MSG)` for `rho`.  Apply item 3 with `sigma` the identity representation
of `A_q` on `l^2(G/L')`.  By (W) the equality branch fails, so `A_q`
contains the proper isometry `s`, contradicting finiteness.

*`SF` part.*  Suppose `A_q` were stably finite.  Then it is a stably
finite target, so `SF(G,L)` gives `(MSG)` for `rho`, and the same argument
produces a proper isometry in `A_q`.  That contradicts stable finiteness,
which includes finiteness.

*Maximal algebra.*  Suppose `C*_max(G)` were finite (resp. stably
finite).  Then the canonical map `G->U(C*_max(G))` is a finite (resp.
stably finite) target, so the rung gives `(MSG)` in `C*_max(G)`.  Item 3
with `sigma` the extension of `lambda` to `C*_max(G)` and (W) gives a
proper isometry in `C*_max(G)`, a contradiction.

This is argued in `C*_max(G)` directly.  It cannot be deduced from the
statement about `A_q`, because a quotient of a finite algebra can be
infinite.

*General form.*  Let `pi` be a representation of `G` that factors as
`sigma o rho` with `rho` a finite target.  Under `FIN(G,L)`, item 3
applied to `rho` gives either a proper isometry in the finite algebra,
which is impossible, or `Fix pi(L)=Fix pi(tLt^-1)`.

## Application to the Leavitt group

For the ring-compression cell of `non_mf_groups_exist.tex`, the
manuscript records strictness verbatim: "the compression is strict, since
`e(sat)=0` while `e.1=e!=0` puts `e_12(1)` in `L\uLu^-1`".  With
`E=EL_20(L_(F_2)(1,2))`, every stably finite target of `E`, composed with
`Delta->E`, is a stably finite target of `Delta`.  The image of `h_S` for
a lifted generating set is the corresponding Markov element of `L`, with
multiplicities.  So `SF(Delta, lift of L)` gives `SF(E,L)`, for the
Markov element of the image multiset of `S`.

Item 4 then gives the two non-stable-finiteness conclusions stated in the
target.  Only item 1 of the per-model lemma and the displayed quasi-regular
witness are used, so no property `(T)` enters.
