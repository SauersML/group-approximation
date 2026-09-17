---
rg: 2
id: model-spectral-gap-quantifier-ladder-proof
kind: route
title: Induce an almost-invariant L-representation to G and read its spectrum in the universal representation; amplify a delta_e model to absorb any model as a null block
target: model-spectral-gap-quantifier-ladder
requires:
  - kesten-spectral-gap-replaces-kazhdan-projection-per-model
---

Notation is that of the target.  The only input from the required claim is
its item 2, which gives the implication `(T) => (MSG)` for every
representation.  The obstruction direction uses no prerequisite.

## Proof of item 1

*Spectra shrink under homomorphisms.*  If `phi:A->B` is a unital
`*`-homomorphism, then `sp(phi(a)) subset sp(a)`.  Faithful
representations preserve spectra.

*(b) implies (a).*  Every unitary representation `pi` of `G` extends to a
unital `*`-homomorphism `C*(G)->B(H)` that sends `rho_u(h_S)` to
`pi(h_S)`.  Hence `sp(pi(h_S)) subset sp(rho_u(h_S))`.  If `1` were an
accumulation point of `sp(pi(h_S))`, it would be one of `sp(rho_u(h_S))`.

*(a) implies (b).*  Take `pi` to be a faithful representation of `C*(G)`
restricted to `G`.  The spectrum is unchanged.

*(c) implies (b).*  This is item 2 of the per-model lemma.  It is quoted
only to complete the equivalence.  The obstruction uses (b) implies (c).

*Induction.*  Let `sigma:L->U(K)` be a unitary representation.  Let
`H_ind` be the space of maps `f:G->K` with `f(gl)=sigma(l)^(-1) f(g)`
and `sum_(gL in G/L) ||f(g)||^2<infinity`, with `(Ind(g)f)(x)=f(g^(-1)x)`.
Let `H_0` be the subspace of sections supported on the coset `L`.  For
`l in L` and `f in H_0`, `Ind(l)f` is supported on `lL=L`.  Moreover
`(Ind(l)f)(e)=f(l^(-1))=sigma(l)f(e)`, so `f -> f(e)` is a unitary
`H_0 -> K` intertwining `Ind|_L` on `H_0` with `sigma`.  Since `H_0` is
invariant under the unitary group `Ind(L)`, it is reducing for `Ind(L)`,
and therefore for the self-adjoint operator `Ind(h_S)`.  Hence

```text
sp(sigma(h_S)) subset sp(Ind(h_S)) subset sp(rho_u(h_S)).
```

*(b) implies (c).*  Choose `c>0` with `sp(rho_u(h_S)) ∩ (1-c,1)` empty.
Let `sigma` be an `L`-representation with no nonzero invariant vector.
Since `S` is symmetric, `sigma(h_S)` is a self-adjoint contraction.  If
`sigma(h_S)xi=xi`, then `<sigma(s)xi,xi>=||xi||^2` for each `s`, by
equality in the average of `Re<sigma(s)xi,xi> <= ||xi||^2`.  So `xi` is
`S`-invariant, hence `L`-invariant, hence `0`.  Thus `1` is not an
eigenvalue.  An isolated point of the spectrum of a self-adjoint operator
is an eigenvalue, so `1` is not isolated in `sp(sigma(h_S))`.  By the
display, `sp(sigma(h_S))` misses `(1-c,1)`, so `1` is not in
`sp(sigma(h_S))`, and `sp(sigma(h_S)) subset [-1,1-c]`.  For a unit
vector `xi`,

```text
sum_(s in S) ||sigma(s)xi-xi||^2 = 2|S| (1-<sigma(h_S)xi,xi>) >= 2|S|c .
```

So `max_s ||sigma(s)xi-xi|| >= sqrt(2c)`.  Every representation of `L`
without invariant vectors has no `(S,sqrt(2c))`-invariant unit vectors.
This is property `(T)` with Kazhdan pair `(S,sqrt(2c))`.

*Failure without (T).*  If `L` does not have `(T)`, then for each
`k` there is `sigma_k` with no invariant vectors and a unit `xi_k` with
`<sigma_k(h_S)xi_k,xi_k> > 1-1/k`.  Hence `sp(sigma_k(h_S))` meets
`(1-1/k,1]`.  As shown above, `1` is either absent from this spectrum or
not isolated in it.  In either case `sp(sigma_k(h_S))` meets
`(1-1/k,1)`.  By the display, so does `sp(rho_u(h_S))` for every `k`.
So `1` is an accumulation point.

## Proof of items 3 and 4

*Item 3.*  Let `A` be a unital MF algebra and `rho:G->U(A)`.  Replace
`A` by the separable unital subalgebra `C*(rho(G))`, which is again MF.
By Blackadar--Kirchberg it embeds, possibly non-unitally, into a norm
matrix corona `C=prod M_(n_j)/(+) M_(n_j)`.  The image of `1` is a
projection `p`, which lifts to projections `P_j` of rank `r_j`.  Then
`pCp` is the norm corona `prod M_(r_j)/(+) M_(r_j)`, and `rho` is a
homomorphism into its unitary group.  When `Rad_MF(G)=G`, every such
homomorphism is trivial, so `rho` is trivial and `sp(rho(h_S))={1}`.
Since `G` is infinite, a `delta_e`-profile model `(V_n)` has
`tr V_n(g)->0` for `g!=e`.  So `V_n(g)` stays far from `I` in norm, and
its corona homomorphism is nontrivial.  Hence a `delta_e`-profile model
exists only if `Rad_MF(G)!=G`, and the transport hypothesis is vacuous at
the endpoint.  The converse direction, that the hypothesis gives the
endpoint, is only as strong as the manuscript's downstream collapse from
the transport theorem.  This note does not re-audit that step.

*Item 4.*  Let `V'_n` have size `a_n` and `W_n` have size `b_n`.  Choose
`k_n` with `k_n a_n >= n b_n`, and put `V''_n=V'_n tensor I_(k_n)`.  The
normalized trace of `V''_n(g)` equals that of `V'_n(g)`, and every
relator error of `V''_n (+) W_n` is the maximum of the two block errors.
The normalized trace of the direct sum is

```text
(k_n a_n tr V'_n(g) + b_n tr W_n(g)) / (k_n a_n + b_n)  ->  delta_e(g).
```

For block-diagonal `V=V''(+)W`, the adjoint action `X -> V X V^*` on
Hilbert--Schmidt matrices preserves the four block subspaces.  Each is
Hilbert--Schmidt orthogonal to the others.  The lower-right block is
exactly `Ad W_n`.  Its exact projection `p` commutes with every lifted
adjoint operator.  Hence `p` gives a reducing corner of the adjoint corona
algebra, and that corner is the adjoint corona of `(W_n)`.  For
self-adjoint `y` commuting with a projection `p`, the spectrum of `pyp`
in `pBp` is contained in `sp_B(y)`.  So accumulation of `sp` at `1` for
`Ad W` forces accumulation for the direct sum.
