---
rg: 2
id: toeplitz-schur-packet-center-dies-proof
kind: route
title: The packet's e_1-scaled coordinates are finitary root elements, whose infinite simple group dies in residually finite targets
target: toeplitz-schur-packet-center-dies-in-residually-finite-models
requires:
  - toeplitz-defect-dies-in-every-finite-quotient-of-el3
  - schur-child-crosses-toeplitz-compressor
---

**Matrix units.**  Since `yx=1`, `f=1+xy` is idempotent in characteristic
two, and `fx=x+xyx=0`, `yf=y+yxy=0`.  Put `e_ab=x^a f y^b`.  For
`b<=c`, `y^b x^c=x^(c-b)`; for `b>c`, `y^b x^c=y^(b-c)`.  Hence
`f y^b x^c f=delta_bc f` and `e_ab e_cd=delta_bc e_ad`.  In the unilateral
shift model (`x e_n=e_(n+1)`, `y e_n=e_(n-1)`, `y e_0=0`) the element `e_ab`
is the rank-one matrix unit sending `e_b` to `e_a`, so the `e_ab` are
nonzero and linearly independent, and `I=TfT` is their span: every word in
`x,y` reduces to some `x^i y^j`, while `y^j f=0` for `j>=1` and `f x^k=0`
for `k>=1`, so `x^i y^j f x^k y^l` is `e_il` when `j=k=0` and `0`
otherwise.  Thus `I` is the nonunital ring of finitary `N x N` matrices over
`F_2`.  The shift model is faithful on all of `T`: `x^i y^j` sends `e_n` to
`e_(n+i-j)` for `n>=j` and kills `e_n` for `n<j`, so for a fixed difference
`i-j` the kernels distinguish the normal-form monomials and they are
linearly independent.

**Claim 1.**  Map `M_r(T)` to operators on `(F_2[N])^r`.  The root elements
`x_ij(e_ab)`, `i!=j`, are exactly the transvections `1+E_((i,a),(j,b))`
between different blocks of the basis `{1,...,r} x N`.  For `i=j`,
`[1+E_((i,a),(k,c)), 1+E_((k,c),(i,b))]=1+E_((i,a),(i,b))` with `k!=i`, so
all elementary transvections are generated, and the group they generate
is the directed union of `SL_n(F_2)` over finite coordinate windows, i.e.
`SL_fin(F_2)`.  The operator representation of `M_r(T)` is faithful on the
subring `M_r(F_2 1 + I)` (it is faithful on `I` by independence of the
matrix units), so `L` is isomorphic to its image.  Each `SL_n(F_2)`, `n>=3`,
is simple, and a normal subgroup of the directed union meeting one
`SL_n(F_2)` nontrivially contains all larger ones; hence `SL_fin(F_2)` is
infinite and simple.  This is the argument of Section 3 of
`research/artifacts/el3-rank-model-toeplitz-assembly-2026-09-12.md`, recorded
for `r=3` in `toeplitz-defect-dies-in-every-finite-quotient-of-el3`; nothing
in it uses `r=3`.

**Claim 2.**  In the matrix `(1)` of
`schur-child-crosses-toeplitz-compressor-proof`, `g(0,q,z)` is lower
unitriangular with all off-diagonal entries in the `q`- and `z`-columns
multiplied by `e_1=xfy=e_11 in I`, and `B_0=0`.  A unitriangular matrix with
off-diagonal entries in `I` is a product of root elements `x_ij(u)`,
`u in I` (clear columns in order; each `u` is a finite `F_2`-sum of matrix
units and `x_ij(u+v)=x_ij(u)x_ij(v)`).  Hence `iota(g(0,q,z)) in L`, which
gives `iota(Q),iota(Z)<=L`.

**Claim 3.**  Let `pi` land in a residually finite group `R`.  Then
`pi(L)` is a quotient of an infinite simple group, hence trivial or
isomorphic to `L`.  A subgroup of a residually finite group is residually
finite, and a residually finite simple group is finite.  So `pi(L)=1`,
proving `(TPC1)`.  Representations factoring through
`EL_r(F_2[z,z^(-1)])` are covered because `SL_r(F_2[z,z^(-1)])` is linear
over a finitely generated ring, hence residually finite (Mal'cev).

**Mass.**  If `pi(iota(J))=1`, the spectral projection `(1-pi(iota J))/2`
is zero, so the marked sector `H_-` and every forbidden carrier inside it
are zero; therefore `q=0` and `pi(z)=0` for every projection `z` in the
`J=-1` part of the packet algebra.
