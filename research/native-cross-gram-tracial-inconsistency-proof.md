---
rg: 2
id: native-cross-gram-tracial-inconsistency-proof
kind: route
title: Pass the cross-Gram conclusion to an exact tracial representation and run the affine rank floor there
target: native-cross-gram-conclusions-fail-in-every-tracial-model
requires:
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

Notation as in the target.  `(N,tau)` is a finite von Neumann algebra with a
faithful normal tracial state, and `||x||_2=tau(x^*x)^(1/2)`.

## Step 0. The three lemmas hold verbatim in finite von Neumann algebras

Each lemma is stated for matrices with normalized trace.  Its proof is a
trace computation with constants that do not depend on the dimension, so it
transfers.

- **`(TCG)`** uses only these facts:
  - the commutator identities `B^*GB-G=B^*(GB-BG)` (and similar), with
    `||xy||_2<=||x|| ||y||_2`;
  - the spectral theorem for the positive contraction `H=G^*G`;
  - the layer-cake/averaging choice of a threshold `t in [m/4,m/2]`.

  All of these are available for elements of `N`, and spectral projections
  of `H` lie in `N`.  In an **exact** representation every transport error
  `epsilon_(i,s)` is zero, so `(TCG5)` gives an exactly reducing
  `P=1_[t,1](H)` with `tau(P)>=m/2`.
- **Pauli lock.**  Let `X,Z` be anticommuting involutions generating a
  finite Pauli group `F`.  Then `E(V)=|F|^(-1) sum_(g in F) gVg^*` is the
  trace-preserving conditional expectation onto `{X,Z}'`, and
  `||V-E(V)||_2<=||[V,X]||_2+||[V,Z]||_2`.  If both commutators are zero,
  then `V` already lies in `{X,Z}'`.  Only the exact case is used below.
- **`(TSG1)`, `(TSG3)`, `(TSG6)`.**
  - For projections `E,E'`: `|tau(E)-tau(E')|<=||E-E'||_1<=||E-E'||_2`, and
    `||R-R'||_2=2||E-E'||_2` for `R=1-2E`, `R'=1-2E'`.
  - `tau` is unitarily invariant.
  - The negative spectral projection of `C_q tensor V` in
    `M_r(C) tensor M`, with product trace, is
    `F_q tensor (1+V)/2 + (1-F_q) tensor (1-V)/2`, of trace
    `q theta+(1-q)(1-theta)`.

  None of this depends on `M` being a matrix algebra.  The packet corner of
  an exact finite-group representation has the form `M_r(C) tensor M` with
  `M` the relative commutant corner.  This is the same decomposition as
  `(FJC2)` of `fixed-packet-julia-calculus-is-tracially-functorial`.

## Step 1. (XCG) is contradictory for every exact pi

Let `pi : Delta -> U(N)` be exact and suppose that `(XCG)` holds.

- The mass `m=||S_1^*S_2||_2^2>=gamma tau(P_source)>0`.
- All transport errors vanish, since the rows are group identities and the
  packets are exact.  By Step 0 `(TCG)` gives an exactly reducing common
  source corner `P` with `tau(P)>=m/2>0`.
- By hypothesis both mixed commutators of the relative polar gauge vanish on
  `P`.  The exact Pauli lock puts the relative polar unitary in the common
  reservoir commutant.  So the two multiplicity involutions `V_1,V_2` of the
  two selector rows are unitarily conjugate in the reservoir, and
  `epsilon_g=0`.
- The two rows are exact on `P`.  Each conjugates a source reflection of
  normalized negative fraction `r_i` to `C_(q_i) tensor V_i`, so
  `delta_1=delta_2=0`.
- `(TSG6)` on the normalized corner `P N P` reads
  `delta_1+(2/3)delta_2+(1/2)epsilon_g>=1/3`.  The left side is `0`, which
  is a contradiction.

These are exactly the recorded steps of
`el20-canonical-opnorm-cross-gram-gives-full-mf-radical` (and of
`arbitrary-profile-cross-gram-implies-shared-gauge-compiler`), with every
`o(1)` replaced by `0`.  If those routes are sound, Step 1 is sound: every
step is one of the three lemmas, and the lemmas hold in `N` by Step 0.

**Quantitative form.**  With `delta_i=0` and positive mass, `(TSG6)` forces
`epsilon_g>=2/3`.  So in every exact tracial model with positive overlap
mass, the relative gauges of the two native rows stay at a fixed HS distance
from any common conjugacy class.  The lock clause is false, not just
unproved.

**Regular instance.**  `lambda : Delta -> U(L(Delta))` is exact, and
`tau(lambda(g))=delta_e(g)`.  Finite packets have Plancherel multiplicities
`dim(rho)^2/|F|` because `tau` restricted to `C[F]` is the regular trace.
The involution `z` has `-1` projection `(1-lambda(z))/2` of trace `1/2`.
Hence `lambda` satisfies every hypothesis `(CAP0)`, `(DCP2)` and full
carrier of `binary-leavitt-el20-canonical-opnorm-native-cross-gram`, with
zero defects, and `(XCG)` fails for it.  Two cases remain:

- if the canonical mass `tau(S_1^*S_2S_2^*S_1)` is `0`, the scalar clause
  fails;
- otherwise the lock clause fails with `epsilon_g>=2/3`.

## Step 2. Ultraproduct transfer

Let `W_n : Delta -> U(d_n)` satisfy, for every fixed relator word `w`,
`||W_n(w)-1||_2 -> 0`.  This is implied by operator-norm asymptoticity.  Fix
a free ultrafilter `omega`.  Let

```text
N_omega = prod_omega (M_(d_n), tr_n)
```

be the tracial ultraproduct, a finite von Neumann algebra with faithful
normal trace `tau_omega=lim_omega tr_n`.  Then `pi(g)=[W_n(g)]` is an exact
homomorphism into `U(N_omega)`.  Suppose that along `W_n` (after any
positive-density reblocking by an approximately reducing projection `Q_n`
with `tr Q_n>=c`) the approximate conclusion holds:

- `tr_n(S_1^*S_2S_2^*S_1)>=gamma tr_n(P_source)-o(1)`,
- `tr_n(P_source)>=c`,
- the mixed commutators of the relative polar gauges `U_n` tend to `0` in
  normalized HS norm on the overlap corners `P_n`.

These facts pass to the limit.

- Sequences of projections, partial isometries and unitaries, bounded in
  operator norm, define elements of the same kind in `N_omega`.
- `Q=[Q_n]` is a projection of trace `>=c`.  It commutes with `pi(Delta)`
  because the reblocking commutators tend to `0` in `||.||_2`.  So
  `pi_Q=Q pi(.)` is an exact representation on `(QN_omegaQ, tau/tau(Q))`.
- Exactified finite packets `rho_n` of `W_n` differ from `W_n|F` by `o(1)` in
  `||.||_2`.  Hence `[rho_n]=pi|F`, and packet projections converge.
- The native transports `S_i` are fixed words in packet projections and
  group elements, so `[S_i(W_n)]=S_i(pi)`, and traces of fixed products
  converge.
- `P=[P_n]` and `U=[U_n]` satisfy the ultralimit identities.  The mixed
  commutators are exactly zero, and `tau_omega(S_1^*S_2S_2^*S_1) >= gamma
  tau_omega(P_source) >= gamma c > 0`.
- The relative polar gauge relations
  `U_n P_n |S_1^*S_2| P_n = P_n S_1^*S_2 P_n + o(1)` pass to the limit.

Thus `(XCG)` holds for `pi_Q`, which contradicts Step 1.  Hence the
approximate conclusion fails along every sequence of asymptotic
representations, whatever its profile and whatever cuts are chosen.

## Step 3. Circularity

Let `Theta` be one of `(CAP1)`, `(EAP1)` or `(APG1)`, with its gauge clause.
Each asserts the approximate conclusion for **all** models in a class `M`:

- canonical operator-norm microstates;
- surviving EL20 norm-corona profiles;
- surviving St20 profiles.

By Step 2 the conclusion fails for every member of `M`.  So `Theta` holds
iff `M` is empty.

- For `(EAP1)` and `(APG1)`, `M` is empty iff `z` is in the MF radical.
- For `(CAP1)`, `M` is empty iff `Rad_MF(EL_20(R))=EL_20(R)`.  This uses
  `surviving-mf-mark-diracizes-to-canonical-opnorm-profile` for one
  direction; the converse is immediate because such `W_n` retain `z`.

So each premise is equivalent to its endpoint, and a proof of `Theta`
cannot use the compiler route to reach the endpoint: it must rule out the
models directly.  A direct estimate of the mass and the lock can hold only
on a model that does not exist, and every hypothesis of such an estimate
that is visible in `N_omega` is also satisfied by `lambda` or `pi_Q`, where
the lock fails.  QED.
