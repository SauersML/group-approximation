---
rg: 2
id: unconfined-quasi-regular-infiniteness-proof
kind: route
title: Move a column vector along a Neumann-uncovered affine family to unconfine Stab(e_n), read the regular character off diagonal coefficients, and push isometries through the resulting surjection onto the reduced algebra
target: unconfined-quasi-regular-algebras-lack-algebraic-infiniteness
requires:
  - stably-finite-msg-rung-is-one-universal-algebra
  - kesten-spectral-gap-replaces-kazhdan-projection-per-model
---

Notation is that of the target.  Column vectors in `R^n` have entries in
`R`, and `E` acts by left multiplication.  `e_ij(r)=I+rE_ij`.  The
imports are item 3 of `stably-finite-msg-rung-is-one-universal-algebra`,
which is used for item 4, and item 1 of
`kesten-spectral-gap-replaces-kazhdan-projection-per-model` (strict
convexity: `ker(1-pi(h_S))=Fix pi(L)`).  Everything else is proved here.

## Item 1

**Lemma 1.1 (no finite-dimensional principal right ideals).**  If `c` is
in `R` and `c!=0`, then `cR` is infinite-dimensional over `F_2`.

*Proof.*  `cR` is a right ideal, so right multiplication `rho(a):x->xa`
preserves it, and `rho(a)rho(b)=rho(ba)`.  From `t_0s_0=1` and
`t_1s_1=1`, `rho(s_0)rho(t_0)=rho(s_1)rho(t_1)=id`.  So `rho(t_0)` and
`rho(t_1)` are injective on `R`, hence on `cR`.  Suppose `cR` is
finite-dimensional.  Then `rho(t_1)` is bijective on `cR`.  From
`t_1s_0=0`, `rho(s_0)rho(t_1)=rho(t_1s_0)=0`, so `rho(s_0)=0` on `cR`.
Then `id=rho(s_0)rho(t_0)=0` on `cR`, so `cR=0` and `c=c.1=0`.  QED.

For a column `c` in `R^n` with `c!=0`, `cR` is again infinite-dimensional:
its projection onto a nonzero coordinate `c_k` is `c_kR`.

**Lemma 1.2 (Neumann's covering lemma over `F_2`, proved).**  Let `W` be
an `F_2`-vector space and `H_1,...,H_m` subspaces of infinite
codimension.  Then `W` is not a union of `m` sets, each empty or a coset
`w_i+H_i`.

*Proof.*  Choose `k` with `2^k>m`.  For each `i`, choose `k` vectors of `W`
that are linearly independent modulo `H_i`; this is possible since
`W/H_i` is infinite-dimensional.  Let `U` be their span, of dimension
`d`, finite.  Each `(w_i+H_i) cap U` is empty or a coset of `H_i cap U`.
The codimension of `H_i cap U` in `U` is
`dim((U+H_i)/H_i)>=k`, so the coset has at most `2^(d-k)` elements.  The
union of these cosets inside `U` has at most `m 2^(d-k)<2^d=|U|`
elements, so it does not cover `U`.  QED.

**Proposition 1.3.**  `Q=Stab_E(e_n)` is unconfined in `E=EL_n(R)` for
every `n>=2`.

*Proof.*  Let `F` inside `E\{1}` be finite.  For `r=(r_1,...,r_(n-1))`
in `W=R^(n-1)`, put `y(r)=e_1n(r_1)...e_(n-1,n)(r_(n-1))` in `E` and
`v(r)=y(r)e_n`.  The factor `e_in(r_i)` fixes `e_j` for `j!=n` and sends
`e_n` to `e_n+e_i r_i`, so `v(r)=e_n+sum_(i<n) e_i r_i`.  Also
`y(r)Qy(r)^-1=Stab_E(v(r))`.

Fix `f` in `F` and put `A=f-I`, which is nonzero with columns
`A_1,...,A_n`.  Then `f` fixes `v(r)` if and only if `T_A(r)=-A_n`, where
`T_A(r)=sum_(i<n) A_i r_i`.  `T_A` is `F_2`-linear.
- If some `A_j` with `j<n` is nonzero, the image of `T_A` contains `A_jR`.
  That is infinite-dimensional by Lemma 1.1, so `ker T_A` has infinite
  codimension.  The solution set is empty or a coset of `ker T_A`.
- If `A_j=0` for all `j<n`, then `A_n!=0` and `T_A=0`, so the solution set
  is empty.

By Lemma 1.2 there is `r` outside all `|F|` solution sets.  Then no `f`
in `F` fixes `v(r)`, that is, `F cap y(r)Qy(r)^-1` is empty.  QED.

**Heredity.**  If `H<=Q` and every conjugate of `H` meets `F`, then every
conjugate of `Q` meets `F`.  So subgroups of unconfined subgroups are
unconfined.  Confinement is conjugation-invariant.  For `n>=4`,
`L=EL_3(R)` on coordinates `1,2,3` fixes `e_n`, so `L<=Q`, and `L` and
`M=uLu^-1` are unconfined.  The same holds for every subgroup of `E`
that fixes some vector of the orbit `Ee_n`.

## Item 2

Let `G` be countable and `H` unconfined, `X=G/H`, `pi=lambda_X`, and
`B=C*_pi(G)`.  For `x=yH`, `Stab(x)=yHy^-1` and
`<pi(g)delta_x,delta_x>=1_(Stab(x))(g)`.  Enumerate finite sets `F_1`,
`F_2`, ... increasing to `G\{1}`.  By unconfinement, choose `x_m` with
`F_m cap Stab(x_m)` empty.  The vector states `omega_m` of `delta_(x_m)` on
`B` satisfy `omega_m(pi(g))->delta_(g,e)` for every `g`.  Let `omega` be a
weak-star cluster point, which is a state of `B` with
`omega(pi(g))=delta_(g,e)`.

In the GNS triple `(sigma,K,xi)` of `omega`, the unitary representation
`g->sigma(pi(g))` is cyclic for `xi` with coefficient `delta_e`.  By
uniqueness of the GNS representation of the positive definite function
`delta_e`, it is unitarily equivalent to `lambda_G`.  Hence
`||lambda(a)||=||sigma(pi(a))||<=||pi(a)||` for `a` in `C[G]`.  This is the
weak containment, and `Phi=sigma` (up to that equivalence) is a unital
surjection `B->C*_lambda(G)` with `Phi(pi(g))=lambda(g)`.

- If `pi(a)=0`, then `lambda(a)=0`, and so `a=0`, since
  `lambda(a)delta_e=a`.
- Let `tau` be the faithful canonical trace of `C*_lambda(G)`, with
  `tau_q=tau o Phi` and `tau_q^(k)=tau^(k) o Phi^(k)` on matrices.  For
  `a` in `M_k(C[G])` with `pi(a)!=0`,
  `tau_q(pi(a)*pi(a))=tau(lambda(a)*lambda(a))>0` because `lambda(a)!=0`.
  So `tau_q` is faithful on `M_k(pi(C[G]))`.

## Item 3

Let `rho` be any unitary representation with `lambda_G` weakly contained
in `rho`, and let `A=C*_rho(G)`, `Phi:A->C*_lambda(G)` and `J=ker Phi`.
The two bullets of item 2 hold verbatim with `rho` in place of `pi`, by
the same computation.

- **(a)** `C*_lambda(G)` is stably finite because `tau` is a faithful
  trace, and `tau^(k)(1-VV*)=tau^(k)(1-V*V)=0` for an isometry `V`.  If `s`
  in `M_k(A)` is an isometry, then `Phi(s)` is an isometry, hence unitary.
  So `Phi(1-ss*)=0` and `1-ss*` lies in `M_k(J)`, with
  `tau_q(1-ss*)=0`.
- **(b)** Let `p` be a nonzero projection in `M_l(rho(C[G]))` with
  `p ~ p'<=1-ss*`.  Then `tau_q(p)=tau_q(p')<=tau_q(1-ss*)=0`.  This
  contradicts faithfulness of `tau_q` on `M_l(rho(C[G]))`.  In particular,
  if `s` itself has entries in `rho(C[G])`, then `1-ss*` is such a `p`,
  so `s` is unitary.
- **(c)** Suppose `A` is not stably finite, and pick `s` with
  `d=1-ss*!=0`.  By (a), `d` is a nonzero projection in `M_k(J)`.
  Conversely, suppose `p` is a nonzero projection in `M_k(J)`.
  `M_k(rho(C[G]))` is dense, so choose `a` with `||rho(a)-p||<1/4`, and
  replace `a` by `(a+a*)/2`.  Put `b=a`.  Then
  `||lambda(b)||=||Phi(rho(b)-p)||<1/4`.  By self-adjoint perturbation,
  `sp(rho(b))` lies within `1/4` of `sp(p)`, which is contained in
  `{0,1}` and contains `1`.  This is GQE.

  If GQE holds for `b`, then `chi_(1/2,infty)(rho(b))` is a projection by
  continuous functional calculus, since the spectrum has a gap at `1/2`.
  It is nonzero, and `Phi` sends it to `chi_(1/2,infty)(lambda(b))=0`, so
  it lies in `M_k(J)`.
- **`C*_max`.**  The same holds for `A=C*_max(G)` with `Phi=lambda`, with
  no hypothesis on `H`.

## Item 4

By `lem:ring-compression-cell`, `uLu^-1=M<=L`, so `u` is in the
compression monoid `C_E(L)`.  The compression is strict, as quoted in
`stably-finite-msg-rung-is-one-universal-algebra`.  Assume `MSG_L(pi)`.
Then `P=chi_(1)(pi(h_S))` lies in `A_q` by continuous functional
calculus.  Item 3 of `stably-finite-msg-rung-is-one-universal-algebra`
(imported: "either `A` contains the proper isometry `s`, or in every
representation `sigma` of `A`, `Fix sigma rho(L) = Fix sigma rho(t L t^-1)`")
applies with `rho=pi`, `A=A_q`, `t=u` and `sigma` the identity
representation on `l^2(E/M)`.

The vector `delta_M` is fixed by `M=uLu^-1`.  It is not fixed by `L`,
since `l delta_M=delta_M` means `l` is in `M`, and `L` is not contained
in `M`.  So the fixed spaces differ, and `s` is a proper isometry of
`A_q`.  This gives `MSG_L(pi) ==> A_q not finite`.  "Not finite implies
not stably finite" is trivial.  The last implication is item 3(c), since
`lambda_E` is weakly contained in `pi` by items 1 and 2.

**Schreier form of `MSG_L(pi)`.**  Restricted to `L`, `pi` is the direct
sum over `L`-orbits on `E/M`.  These orbits correspond to the double
cosets `LyM`, and the orbit of `yM` is `L/(L cap yMy^-1)`.  The spectrum of
`pi(h_S)` is the closure of the union of the orbit spectra.  So `1` is
isolated if and only if there is `c>0` such that no orbit spectrum meets
`(1-c,1)`.

Because `e` lies in `S` and `S` generates `L`, strict convexity applies
(item 1 of `kesten-spectral-gap-replaces-kazhdan-projection-per-model`).
So the eigenvalue `1` on an orbit is carried exactly by the
`L`-invariant vectors: the constants on a finite orbit, and nothing on an
infinite one.  Hence `MSG_L(pi)` is a uniform spectral gap of the
Schreier operators of `L` on the orbits `L/(L cap yMy^-1)`.  The gap is
on the complement of the constants for finite orbits, and on all of
`l^2` for infinite orbits.

**Consistency with `(T)`.**  If `L` has `(T)`, then `MSG_L` holds in every
representation, and item 4 recovers `prop:max-infinite` inside `A_q`.
The group `L` is infinite and Kazhdan, hence non-amenable, so
`sp(lambda(h_S))` lies in `[-1,1-c_0]` for some `c_0>0`.  `MSG_L(pi)`
gives `sp(pi(h_S))` inside `[-1,1-c] u {1}`.  Both spectra are unchanged
when `S` is replaced by `uSu^-1`, since conjugation by `lambda(u)` or
`pi(u)` is unitary.  Put `c'=min(c,c_0)`.  Let `f` be a real polynomial
with `f(1)=1` and `|f|<=1/4` on `[-1,1-c']`, and let `b` be `f` applied to
`h_(uSu^-1)`.  This `b` is a GQE element, and
`chi(pi(b))` is the projection `q` onto `Fix pi(M)`, which contains
`delta_M`.  Both `P` and `q` lie in `J_q`, as item 3(a) requires.  The
Kazhdan source is thus the special case of GQE in which `b` is a
polynomial in one Markov operator.

## Item 5

**Construction.**  Let `A=cone(00)`, `B=cone(01)` and `C=cone(1)` in the
Cantor set `{0,1}^N`, and let `A'=cone(000)`.  Let `g` in `V` swap `00w`
and `01w` and fix `C`, so `gA'=cone(010)`.  Let `h_A:A->A'` be a
prefix replacement, and put `h_B=g h_A g^-1:B->gA'`.  Let `h_C` map `C`
onto `C'`, the complement of `A' u gA'`, by any finite prefix-replacement
homeomorphism; both are finite unions of cones.  Then `h=h_A u h_B u h_C`
is in `V`.

**The conjugate.**
- On `A'`, `hgh^-1 = h_B g h_A^-1 = g h_A g^-1 g h_A^-1 = g`.
- On `gA'`, symmetrically, `hgh^-1 = g`.
- On `C'`, `hgh^-1 = h_C h_C^-1 = id`.

So `g'=hgh^-1` equals `g` on `Y=A' u gA'` and is the identity off `Y`.

**The projections.**  Let `X` be a `V`-orbit, dense, and `pi=pi_X`.  Put
`P=(1-pi(g))/2` and `P'=(1-pi(g'))/2=pi(h)Ppi(h)*`.  On `l^2(X cap Y)`
we have `g'=g`, and on `l^2(X\Y)` we have `g'=1`.  Hence
`(1-pi(g))(1-pi(g'))/4=P'`, that is, `P'<=P`.  Also `P-P'` equals
`(1-pi(g))/2` on `l^2(X\Y)`, which is nonzero because `X` meets the open
set `A\A'`.

**The isometry.**  Put `w=pi(h)P+(1-P)`.  Since `pi(h)P=P'pi(h)` and
`P'<=P`, the cross terms `(1-P)pi(h)P` and `pi(h)P(1-P)` vanish.  So
`w*w=P+(1-P)=1` and `ww*=P'+1-P`, which is not `1`.  Thus `w` is a proper
isometry in `pi(C[V])`, and by item 3(b), `lambda_V` is not weakly
contained in `pi_X`.

**Confinement.**  Directly: `g'` and `gg'` have disjoint supports `Y` and
`(A u B)\Y`, so every point of `X` is fixed by one of them.  Both act
nontrivially on `X`, so `{g', gg'}` confines every point stabiliser.  The
unconfinement hypothesis of item 3(b) therefore cannot be dropped.
