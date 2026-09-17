---
rg: 2
id: kesten-spectral-gap-replaces-kazhdan-projection-proof
kind: route
title: Take the eigenprojection of one Markov element at 1, rerun the transport and normal-subgroup proofs, and calibrate on a free-group rotation block
target: kesten-spectral-gap-replaces-kazhdan-projection-per-model
requires: []
---

Notation is that of the target.  `y=rho(h_S)` is self-adjoint with
`||y||<=1`.  Spectra are computed in `A`, and by spectral permanence also
in any C-star subalgebra containing `y`.

## Step 1: fixed vectors are the eigenspace at 1

Represent `A` faithfully on a Hilbert space.  If `xi` is fixed by
`rho(L)`, then `y xi=xi`.  Conversely let `y xi=xi`.  Then

```text
||xi||^2 = Re<y xi,xi> = (1/|S|) sum_s Re<rho(s)xi,xi>
```

and every term satisfies `Re<rho(s)xi,xi> <= ||xi||^2`.  So equality holds
termwise, and `rho(s)xi=xi` for every `s in S`.  Since `S` generates `L`,
`xi in Fix rho(L)`.

Assume `(MSG)`.  If `1 notin sp(y)`, put `P=0`.  Otherwise `1` is an isolated
point of `sp(y)`, so the indicator `chi_{1}` is continuous on `sp(y)` and
`P=chi_{1}(y) in C*(y) subset C*(rho(L))`.  In the faithful representation
`P` is the spectral projection of `y` at the eigenvalue `1`, which is the
projection onto `ker(1-y)=Fix rho(L)`.  Hence `rho(l)P=P` for `l in L`.

For the approximation, choose a continuous `f` on `[-1,1]` with `f(1)=1`
and `f=0` on `sp(y)\{1}`.  This is possible because `sp(y)\{1}` is compact
and misses `1`.  Given `c>0`, Weierstrass gives a polynomial `p` with
`sup_[-1,1]|p-f|<c`.  Put `a=p(h_S) in C[L]`, the polynomial in the
convolution algebra.  Then `rho(a)=p(y)`, so `||rho(a)-P||=||p(y)-f(y)||<c`.
Also `eps(a)=p(eps(h_S))=p(1)`, so `|eps(a)-1|<c`.  This proves item 1.

## Step 2: (T) implies (MSG)

Let `(S,kappa)` be a Kazhdan pair.  `Fix rho(L)^perp` is `rho(L)`-invariant
and contains no nonzero invariant vector.  So every unit vector `xi` in it
has `max_s ||rho(s)xi-xi|| >= kappa`.  For such `xi`,

```text
<(1-y)xi,xi> = (1/|S|) sum_s (1-Re<rho(s)xi,xi>)
             = (1/(2|S|)) sum_s ||rho(s)xi-xi||^2 >= kappa^2/(2|S|).
```

Since `y` commutes with the projection onto `Fix rho(L)` and equals `1`
there, `sp(y) subset {1} union [-1,1-kappa^2/(2|S|)]`.  The image of `e_L`
is also the projection onto `Fix rho(L)`, so it equals `P`.  This proves
item 2.

## Step 3: the manuscript proofs with P in place of the Kazhdan projection

**Transport.**  Read the proof of `thm:transport` in `non_mf_groups_exist.tex`
with `P` from Step 1 for `rho=sigma~:G->U(B)`.  It uses the Kazhdan
projection in exactly four places.

- *Norm approximation by group-algebra elements with coefficient sum near
  one.*  This is Step 1.
- *`sigma~(l)P=P`.*  This is Step 1.
- *Lifting `P` to projections `P_n`.*  This holds for any projection in `B`.
- *The order lemma `U^*PU<=P` for `U=sigma~(u)`.*  The printed proof of
  `lem:kazhdan-projection-order` uses only that `P` is the projection onto
  `Fix sigma~(L)` in a faithful representation.  Step 1 supplies this.

Stable finiteness of `B` (`lem:stable-finite`) is independent of `(T)`.
The remaining lines of the proof are unchanged.

**Normal subgroups.**  In the proof of `thm:normal-kazhdan`, let `Theta` be
nontrivial on `K`.  Take `p=chi_{1}(Theta(h_S))`, with `S` generating `K`,
using `(MSG)` for `Theta`.  By Step 1, `p` is the projection onto
`Fix Theta(K)`.  The printed argument then gives `Theta(g)p Theta(g)^*=p`,
and `q=1-p!=0` because `p=1` would make `Theta` trivial on `K`.  The corner
model `W_n` is formed as printed.

Replace the last paragraph by the following.  `q` is a continuous
function of `y=Theta(h_S)`, so in the corner `qQq` the element `qy` has
spectrum in `sp(y)\{1}`.  That set lies in `[-1,1-k]` for some `k>0`, by
`(MSG)` and compactness.  Hence `(1-k)q-qy>=0` in the corner, which is
identified with `Q_r`.  With `tau` the limit trace of `Q_r`,

```text
tau(W(h_S)) = tau(qy) <= 1-k.
```

The hypothesis of the theorem gives `tr W_n(s)->1` for every `s in S`, so
`tau(W(h_S))=1`, a contradiction.  The maximal group C-star algebra is not
used.  This proves item 3.

## Step 4: calibration in F_2

Let `D_k=diag(exp(2 pi i j/k))_(j<k)` and choose integers `k_n->infinity`
and `d_n` with `k_n/d_n->0`.  Choose unitaries `W_n(a),W_n(b) in U(d_n)`
with `tr W_n(w)->0` for every nontrivial reduced word `w`.  Haar-random
pairs do this almost surely by Voiculescu's asymptotic freeness, so a
deterministic sequence exists.  Put

```text
V_n(a)=W_n(a)+D_(k_n),     V_n(b)=W_n(b)+D_(k_n)     on C^(d_n) + C^(k_n).
```

This is an exact representation of `F_2` in every coordinate.  Its
normalized traces are

```text
(d_n tr W_n(w) + k_n tr D_(k_n)^(expsum(w)))/(d_n+k_n) -> delta_e(w).
```

On the second block, `V_n(h_S)=(1+2D_(k_n)+2D_(k_n)^*)/5`.  Its eigenvalues
`(1+4cos(2 pi j/k_n))/5` become dense in `[-3/5,1]` with mesh tending to
`0`.

In the norm corona, `lambda in sp([x_n])` for self-adjoint bounded `(x_n)`
if and only if `liminf_n dist(lambda,sp(x_n))=0`.  Indeed, invertibility of
`[x_n-lambda]` means that `x_n-lambda` is eventually invertible with
bounded inverses.  Hence `sp(Theta(h_S)) contains [-3/5,1]`.  Conversely,
in any representation `h_S` has numerical range in
`1/5+(4/5)[-1,1]=[-3/5,1]`, so equality holds.

For `sigma~`, the block `D_k tensor conj(D_k)` has eigenvalues
`exp(2 pi i (j-j')/k)`, which is the same set as for `D_k`.  So the same
computation gives `sp(sigma~(h_S))=[-3/5,1]`.  In both cases `1` is an
accumulation point.  The bad block has normalized rank `k_n/(d_n+k_n)->0`,
or its square in the adjoint.  This proves item 4.

## Step 5: adjoint splitting of delta_e-profile models

Let `xi_n=I/sqrt(d_n)`, a unit vector of `(M_(d_n)(C),<x,y>=Tr(y^*x))`.
For every `g`, `Ad V_n(g) xi_n = V_n(g)V_n(g)^*/sqrt(d_n) = xi_n` exactly.
Fix a free ultrafilter and put `omega([x_n])=lim <x_n xi_n,xi_n>`.  This is
well defined on `B`, because null sequences contribute zero, and it is a
state with `omega(sigma~(g))=1`.  For a unitary `v` with `omega(v)=1`,

```text
omega((v-1)^*(v-1)) = 2-2Re omega(v) = 0,
```

so by Cauchy--Schwarz `omega(xv)=omega(x)` for all `x`.  Hence `omega` is
multiplicative on the algebra generated by `sigma~(G)`, and by continuity
it is a character of `A_L`.  Let `I_omega=ker omega`.

The normalized trace of `Ad V_n(g)=V_n(g) tensor conj(V_n(g))` on
`C^(d_n^2)` is `|tr V_n(g)|^2`, which tends to `delta_e(g)`.  So the limit
trace `tau` of `B` satisfies `tau(sigma~(g))=delta_e(g)`.  `A_L` is a
quotient of `C*_max(L)`, and `tau` pulls back to the canonical trace of
`C*_max(L)`, whose GNS representation is `lambda_L`.  Therefore
`pi_tau(A_L)=C*_r(L)`, and `ker pi_tau=J_tau={x: tau(x^*x)=0}`, a closed
two-sided ideal because `tau` is tracial.

Kesten: since `L` is nonamenable and `h_S` is a symmetric probability
measure whose support generates `L`, `rho_S=||lambda_L(h_S)||<1`.  Choose
continuous `f:[-1,1]->[0,1]` with `f=0` on `[-1,rho_S]` and `f(1)=1`, and
put `e=f(y)`.  Then `pi_tau(e)=f(lambda_L(h_S))=0`, so `tau(e)=0` and
`e in J_tau`.  Also `omega(e)=f(omega(y))=f(1)=1`, so `e notin I_omega`.
Since `I_omega` has codimension one, `I_omega+J_tau=A_L`.  Write `1=i+j`
with `i in I_omega` and `j in J_tau`.  For `x,z in A_L`, the element
`xj+zi` is congruent to `x` modulo `I_omega` and to `z` modulo `J_tau`.
So `a->(omega(a),pi_tau(a))` maps `A_L` onto `C+C*_r(L)`.

If this map is injective, it is a *-isomorphism.  Then
`sp(y)=sp(omega(y)) union sp(lambda_L(h_S)) subset {1} union [-rho_S,rho_S]`,
and `(MSG)` holds for `sigma~` on `L`.  This proves item 5.

For every continuous `g` vanishing on `[-1,rho_S]`,
`tau(g(y))=<g(lambda_L(h_S))Omega,Omega>=0`.  This is the vanishing-trace
statement in the target's impact paragraph.
