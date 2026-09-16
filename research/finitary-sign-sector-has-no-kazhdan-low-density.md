---
rg: 2
id: finitary-sign-sector-has-no-kazhdan-low-density
kind: claim
title: A finitary sign sector carries no Kazhdan low-commutator density in any microstate sequence
distinct_from:
  canonical-marked-corner-kazhdan-density-vanishes: that proves vanishing only for canonical marked microstates with the mark outside Lambda; this bounds the low-commutator density of every microstate sequence of every character by the squared locally-finite-invariant mass, and kills sign-sector supported directions with no trace hypothesis.
  commutant-density-forces-bounded-type-mass: that is an exact finite-dimensional isotypic identity for the whole old group; this is a fixed-cutoff microstate estimate that uses only one infinite locally finite kernel inside the Kazhdan group and vanishes on the finitary sign sector even when bounded-type mass is positive.
  canonical-packet-traces-do-not-place-old-commutant-density: that dilutes old density by putting the packet on an independent tensor factor over residual quotients; this treats the Toeplitz placement where the packet centre is a finitary transvection killed by every finite quotient, and replaces that dilution by a central compression of the character.
  one-bounded-type-coefficient-separates-unbounded-exits: that separates bounded-type mass from unbounded exits by one coefficient residual; this proves that forbidden mass under a finitary sign is orthogonal to all locally-finite-invariant mass in every character, so no coefficient cell can promote it to low-commutator density.
---

**ESTABLISHED.**

**Setting.** Let `G` be a countable group containing a property-`(T)`
subgroup `Lambda`, with finite inverse-closed Kazhdan generating set `S` and
spectral cutoff `kappa>0` from `property-t-hs-adjoint-low-spectrum-budget`.
Suppose

```text
F_1 <= F_2 <= ... <= Lambda   finite,       L_inf = union_m F_m,
delta(F_m) = least degree of a nontrivial irreducible of F_m -> infinity.
                                                             (FSS0)
```

Let `phi_n:G->U(d_n)` be inverse-normalized normalized-HS microstates
(asymptotically multiplicative on every fixed finite set) with
`tr o phi_n -> tau` pointwise, and let `Z_n` be projections in `M_(d_n)`
with `tr(Z_n phi_n(g)) -> omega(g)` for every `g` (always true after passing
to a subsequence).  On `H_n=M_(d_n)(C)`, with `<X,Y>=tr(X^*Y)` and adjoint
trace `tr_ad=Tr_(H_n)/d_n^2`, put

```text
A_n = I-(1/|S|) sum_(s in S) Ad(phi_n(s)),
P_n = 1_[0,b](A_n),                 0<b<kappa fixed,
R_Z X = X Z,         L_Z X = Z X,
P_F = |F|^-1 sum_(k in F) k   in C[F].
```

Because `P_(F_(m+1)) <= P_(F_m)` in every unitary representation, the
decreasing limits

```text
tau(e_inf)=lim_m tau(P_(F_m)),        omega(e_inf)=lim_m omega(P_(F_m))
```

exist; `e_inf` is the projection onto the `L_inf`-invariant vectors of the
GNS representation of `tau`.

**FSS1 (total budget).** For every `m`,

```text
limsup_n tr_ad(1_[0,b](A_n)) <= tau(P_(F_m))^2 + delta(F_m)^-2,
limsup_n tr_ad(1_[0,b](A_n)) <= tau(e_inf)^2.                (FSS1)
```

**FSS2 (one-sided sector budget).** For every `m`,

```text
limsup_n ||R_(Z_n) P_n||_2^2 = limsup_n ||L_(Z_n) P_n||_2^2
  <= tau(P_(F_m)) omega(P_(F_m)) + omega(1-P_(F_m))/delta(F_m)^2,
limsup_n ||R_(Z_n) P_n||_2^2 <= tau(e_inf) omega(e_inf).     (FSS2)
```

Here `||.||_2` is the Hilbert--Schmidt norm on `B(H_n)` normalized by
`tr_ad`.

**FSS3 (subspaces and energetic form).** For projections `W_n<=P_n` and
arbitrary projections `R_n` on `H_n`,

```text
sqrt(tr_ad(W_n)) <= ||R_(Z_n)P_n||_2 + ||(I-R_(Z_n))W_n||_2,
tr_ad(R_n) <= tr_ad(R_n A_n)/b
             + (||R_(Z_n)P_n||_2 + ||(I-R_(Z_n))R_n||_2)^2,  (FSS3)
```

and the same with `L_(Z_n)` in place of `R_(Z_n)`.

**FSS4 (finitary sign sector).** Let `J in L_inf` and suppose

```text
||Z_n(1+phi_n(J))||_2 -> 0.                                  (FSS4a)
```

Then `omega(P_(F_m))=0` whenever `J in F_m`, and

```text
limsup_n ||R_(Z_n)P_n||_2^2 <= omega(1)/delta(F_m)^2 -> 0.   (FSS4b)
```

Hence every sequence of projections `W_n<=P_n` which is approximately left-
or right-supported on the sector (`||(I-R_(Z_n))W_n||_2->0` or the
`L_(Z_n)` analogue) has `tr_ad(W_n)->0`, and every such `R_n` with
`tr_ad(R_n A_n)->0` has `tr_ad(R_n)->0`.  If `J^2=1`, the spectral
projection `Z_n=1_(Re<0)(phi_n(J))` and every subprojection of it satisfy
`(FSS4a)`, since `||Z_n(1+phi_n(J))||_2 <= ||phi_n(J)^2-1||_2/sqrt(2)`.

**FSS5 (Toeplitz instance).** Let `T=F_2<x,y | yx=1>` in its
unilateral-shift model, with finitary ideal `F`, isomorphic to `M_inf(F_2)`
and spanned by `e_ij=x^i(1+xy)y^j`, and suppose `EL_r(T)<=Lambda` with
`r>=3`.  Then

```text
L_inf = GL_fin(N x [r], F_2) = ker(EL_r(T) -> GL_r(T/F)),
F_m   = GL(N_(<m) x [r], F_2),  isomorphic to GL_(rm)(F_2),     (FSS5)
```

satisfy `(FSS0)`.  `L_inf` is an infinite simple normal subgroup of
`EL_r(T)`, killed by every finite-dimensional unitary representation and by
every finite quotient.  The packet embedding `iota` of
`schur-child-crosses-toeplitz-compressor` sends the centre-and-`Q` part
`<Q,Z>` of the packet, in particular the packet sign `J`, into `F_2`.
Therefore, for every group `G` containing such a `Lambda`, every microstate
sequence of `G` and every fixed `0<b<kappa`, the adjoint Reynolds range of
`predicate-rank-jump-forces-adjoint-reynolds-gap` (which lives in `End(H_-)`
for the sector `iota(J)=-1`) has adjoint density in the old low-commutator
space tending to zero.  More generally so does every low-commutator subspace
supported on that sector.  No coefficient-covariance cell, whatever it
does, can put a sector-supported Schur Reynolds carrier into the old
low-commutator space with positive density.

**FSS6 (central compression).** Suppose `G` is generated by *comparable
letters*: elements `u` with `u L_inf u^-1 <= L_inf` or
`u^-1 L_inf u <= L_inf`.  Then `e_inf` is central in `M=pi_tau(G)''`.  If
`tau` is hyperlinear and `theta=tau(e_inf)<1`, then

```text
tau'(g) = tau(g(1-e_inf))/(1-theta)                          (FSS6)
```

is a hyperlinear character of `G` with `tau'(e_inf)=0`.  Every
`y in C[G]` with `y=y(1-J)/2` for some `J in L_inf` satisfies `y e_inf=0` and
`tau'(y)=tau(y)/(1-theta)`, and `tau(y)>0` forces `theta<1`.  If `J_H` is a
central involution of `G`, this compression commutes with cutting to the
corner `J_H=-1`.

The parity compressor `H(alpha,chi)` of
`toeplitz-parity-compressor-candidate` satisfies the hypothesis:

- `Lambda=EL_4(T) x C_2` normalizes `L_inf`;
- `J_H` is central;
- `q` centralizes `L_inf`, because `chi(L_inf)=0`;
- `t L_inf t^-1=beta(L_inf)<=L_inf`, because entrywise `sigma^2` sends
  `e_ij` to `e_(i+2,j+2)`.

So does every modification made by enlarging the matrix size, adjoining the
packet through `iota`, or adding further letters, as long as every added
letter is comparable on `L_inf`.

**FSS7 (the density target is only vacuously true in this placement).** Let
`G` satisfy the hypotheses of FSS5 and FSS6.  Let `y in C[Lambda]` be a
nonzero projection with `y=y(1-iota(J))/2`, for example a forbidden selector
projection inside the packet sign sector.  The following are equivalent:

1. there is `c>0` such that every microstate sequence of `G` with vanishing
   relator defect and `tr(phi_n(y))->q>0` admits projections
   `W_n<=1_[0,b](A_n)` with `liminf tr_ad(W_n)>=c q^2`;
2. no hyperlinear character `tau` of `G` has `tau(y)>0`.

Any quantitative form of `(PCD1)` in
`parity-compressor-old-commutant-has-positive-density`, with any constants
`c>0,C`, implies (1).  Statement (2) implies that `G` is not hyperlinear
(take the canonical trace: `tau_can(y)=||y||_(ell^2)^2>0`).

So in this placement `(PCD1)` is true only vacuously.  Whenever
positive-mass microstates exist at all, the compressed microstates of
`(FSS6)` have positive forbidden mass and vanishing low-commutator density.
On a sequence where `(PCD1)` does hold, FSS1 forces `tau(e_inf)>=sqrt(c)q`,
yet by FSS4 none of that invariant mass meets the forbidden sector.  The
same equivalence holds for marked microstates, with `y` replaced by
`y(1-J_H)/2`.

**Scope.**

- Nothing here asserts that `H(alpha,chi)`, or any packet modification of it,
  has a hyperlinear character with positive forbidden mass.  FSS7 says only
  that positive density can never be the mechanism.
- The residual-quotient countermodels in the Attempts of the target all use
  finite quotients or finite-dimensional representations in which a packet
  survives.  In the `iota` placement these carry zero packet-sign mass,
  because finite quotients kill `L_inf`.  FSS6 is the replacement
  countermodel.
- Escapes not covered:
  - packet signs outside `L_inf`, for example identifying the packet centre
    with `J_H` or with the external `C_2`, or scaling `Z` by a non-finitary
    coefficient such as `xy`.  There FSS4 and the orthogonality `y e_inf=0`
    can fail;
  - cutoffs `b>=kappa`;
  - added letters `u` with `u L_inf u^-1` incomparable to `L_inf`.  There
    FSS1--FSS5 still hold, but `e_inf` need not be central.
- For canonical `tau`, `tau(e_inf)=lim_m 1/|F_m|=0`.  So FSS1 recovers
  `(CMK1)` of `canonical-marked-corner-kazhdan-density-vanishes` for every
  `G` containing `EL_r(T)`, marked or not.
