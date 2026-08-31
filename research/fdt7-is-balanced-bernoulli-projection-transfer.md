---
rg: 2
id: fdt7-is-balanced-bernoulli-projection-transfer
kind: claim
title: FDT7 is exactly a balanced Bernoulli projection transfer
distinct_from:
  kt-ccr-holds-on-the-fd-tempered-adjoint-sector: that closes the FD-tempered cyclic sector and isolates the pointed op-norm-one estimate FDT7; this gives a reversible projection linearization and an exact non-FD-tempered counterprofile.
  kt-pointed-clifford-energy-one-compressor-no-go: that shows one-compressor scalar energy occurs in finite permutation models; this treats the full unitary commutator, preserves every actor defect under linearization, and identifies the exact Bernoulli quasi-regular module.
  kazhdan-almost-invariant-corner-near-invariant-projection: that rounds a nearly invariant projection under a genuine Kazhdan representation; this shows the FDT7 projection is already exact and balanced, while the actor representation is the unrounded object.
  collision-and-phase-free-cartan-observables-force-joint-lamp-targets: that assumes a rank-one Cartan and extracts permutations; this needs only one trace-half projection and explains why its matrix-ultraproduct origin remains decisive.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**ESTABLISHED EQUIVALENCE AND NO-GO; FDT7 OPEN.**  Let `v in U(d)` and
`U in U(d)`.  Define

~~~text
J(v)=[[0,v],[v^*,0]],       P(v)=(I+J(v))/2,
U_tilde=diag(U,U).                                      (BBP1)
~~~

Then `J(v)` is a trace-zero self-adjoint involution, `P(v)` is a
projection of normalized trace `1/2`, and the following identities are
exact:

~~~text
||[U_tilde,J(v)]||_(2,2d)=||[U,v]||_(2,d),
||U_tilde P(v) U_tilde^*-P(v)||_(2,2d)
  =(1/2)||[U,v]||_(2,d).                                (BBP2)
~~~

Doubling an actor microstate by `U->diag(U,U)` preserves every normalized
Hilbert--Schmidt relator defect and every normalized trace.  Consequently
FDT7 for op-norm-one unitaries is equivalent, up to the fixed factor `2`,
to the following balanced-projection statement:

~~~text
p_n=p_n^2=p_n^*,       tr(p_n)=1/2,
max_(s in S)||pi_n(s)p_n pi_n(s)^*-p_n||_2 ->0
imply
||pi_n(gamma)p_n pi_n(gamma)^*-p_n||_2 ->0.             (BBP3)
~~~

The converse uses `v_n=2p_n-I`.  Thus polar decomposition,
Powers--Størmer inequalities, spectral cutting, and passage from a contraction
to a projection cannot add missing structure: the witness may already be an
exact macroscopic half-projection.

There is an exact tracial counterprofile to every argument using only those
features.  On the Bernoulli space

~~~text
Omega={+1,-1}^(G/Lambda)
~~~

let `z_x` be the sign at `x` and put
`N=L^infinity(Omega) crossed_product G`.  For the base coset
`o=Lambda`, set `v=z_o` and `p=(1+v)/2`.  Then

~~~text
tr(p)=1/2,
u_lambda p u_lambda^*=p                    for lambda in Lambda,
||u_gamma p u_gamma^*-p||_2^2=1/2          for gamma notin Lambda. (BBP4)
~~~

All actor relations, projection relations, property-(T) hypotheses, and
tracial identities are exact.  The orbit signs `z_(g o)` are orthonormal,
so their cyclic conjugation representation is exactly the quasi-regular
representation on `ell^2(G/Lambda)`.  By
`kt-ccr-holds-on-the-fd-tempered-adjoint-sector`, this module is not
FD-tempered for the Kun--Thom pair.

The exact matrix boundary has a group-theoretic name.  Put

~~~text
W=(direct_sum_(G/Lambda) C_2) semidirect G,              (BBP4b)
~~~

where `G` permutes the coset coordinates.  Fourier transform on the
abelian base identifies `N` with `L(W)`.  Consequently the Bernoulli
profile has a trace-preserving matrix-ultraproduct realization exactly when
`W` is hyperlinear.  If `W` is hyperlinear, restricting such an embedding
to `G` and taking the base-coordinate projection gives a literal
counterexample to FDT7 and (CCR).  No result used in this route promotes the
available actor microstates of `G` to a hyperlinear model of this
generalized coset wreath product.

Thus the Bernoulli model does not presently refute FDT7.  It proves that no
argument valid in all finite tracial von Neumann algebras, no Jones-index
calculation detached from matrix approximability, and no property-(T)
fixed-vector inequality alone can prove `(BBP3)`.  The unresolved
matrix-specific question is precisely the hyperlinearity of `W` (or an
equivalent embedding of this Bernoulli crossed product), not a polar or
spectral estimate.

Projectivizing the witness loses information even before that boundary.
For Pauli involutions `X,Z`,

~~~text
XZ=-ZX,       ||[X,Z]||_2=2,
[Ad(X),Ad(Z)]=0,
[X tensor conjugate(X), Z tensor conjugate(Z)]=0.        (BBP5)
~~~

Thus tensoring `v` with its inverse/conjugate or replacing it by
`Ad(v)` can erase a maximal scalar-phase commutator.  Such a tensor trick
cannot prove FDT7 without an independent phase-sensitive observable.

Finally, a Ulam procedure which exactified the actor on the two-point algebra
`C^*(2p-I)` would be sufficient but is already the missing theorem.  If it
produced a genuine finite-dimensional `rho:G->U(D)` and a
`rho(Lambda)`-central projection `q` with

~~~text
||q-p||_2 + ||rho(gamma)-pi(gamma)||_2 ->0,              (BBP6)
~~~

then finite-dimensional image collapse would make `q`
`rho(Gamma)`-central, and

~~~text
||pi(gamma)p pi(gamma)^*-p||_2
 <=2||p-q||_2+2||pi(gamma)-rho(gamma)||_2 ->0.           (BBP7)
~~~

So stabilizing the adjoint action only on the C-star algebra generated by the
witness is not a weaker shortcut once covariance with `gamma` is retained;
it directly implies FDT7.  The full route remains OPEN.

DERIVATION
balanced-bernoulli-projection-transfer-proof
