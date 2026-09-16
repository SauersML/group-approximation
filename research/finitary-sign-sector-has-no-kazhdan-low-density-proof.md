---
rg: 2
id: finitary-sign-sector-has-no-kazhdan-low-density-proof
kind: route
title: Average the Kazhdan low space over growing simple finitary heads and read the sector trace by Schur orthogonality
target: finitary-sign-sector-has-no-kazhdan-low-density
requires:
  - property-t-hs-adjoint-low-spectrum-budget
  - schur-child-crosses-toeplitz-compressor
  - toeplitz-parity-compressor-candidate
  - parity-headed-compressor-kills-mark-in-exact-matrix-models
  - toeplitz-head-tail-unital-self-embedding
---

Notation is that of the target claim.  The phrase `o(1)` means a quantity
tending to zero as `n->infinity` with every other parameter fixed.  The
finite experiment `experiments/parity-compressor-old-commutant-has-positive-density-2026-09-16/fsv_check.py`
checks Steps 3--4 exactly for `GL_3(F_2)` and `GL_4(F_2)` on their
point-plus-hyperplane permutation modules.

**Step 0 (three elementary facts).** For unitaries `U,V in M_d`,
`Ad U=U tensor conj(U)`, so with the normalized norms

```text
||Ad U-Ad V||_2 <= ||U-V||_2 ||U||_2 + ||V||_2 ||U-V||_2 = 2||U-V||_2.   (0a)
```

The operator `X |-> A X B` on `M_d` is `A tensor B^T`, hence its normalized
adjoint trace is

```text
tr_ad(X |-> A X B) = tr(A) tr(B).                                        (0b)
```

Finally `|tr_ad(Y)|<=||Y||_2` and `||YB||_2<=||Y||_2||B||_op`.       (0c)

**Step 1 (displacement on the low space).** Since `S` is inverse-closed and
the microstates are inverse-normalized, `sum_s Ad(phi_n(s))` is selfadjoint
and each `Ad(phi_n(s))` is unitary on `H_n`, so for every `X`

```text
sum_(s in S) ||(Ad(phi_n(s))-I)X||_2^2 = 2|S| <X, A_n X>.                (1a)
```

Split `P_n=P_n'+P_n''` with `P_n'=1_[0,kappa/2](A_n)` and
`P_n''=1_(kappa/2,b](A_n)`; the latter is zero if `b<=kappa/2`.  Let
`delta_n->0` be the defect of `phi_n` on the finite window of
`property-t-hs-adjoint-low-spectrum-budget`.  By `(1a)` and `(PTB1)`,

```text
||(Ad(phi_n(s))-I)P_n'||_2^2 <= 2|S| tr_ad(P_n' A_n) <= 2|S| C delta_n,
```

and by `(PTB2)` applied to `[kappa/2,b]`,
`||(Ad(phi_n(s))-I)P_n''||_2 <= 2 tr_ad(P_n'')^(1/2) <= 2 C_(kappa/2,b)^(1/2) delta_n`.
Hence `||(Ad(phi_n(s))-I)P_n||_2 <= eta_n -> 0` for every `s in S`.  For a
word `h=s_1...s_l`, telescoping gives

```text
(U_1...U_l - I)P = sum_i U_1...U_(i-1)(U_i-I)P,
```

and left multiplication by a unitary preserves the Hilbert--Schmidt norm.
Together with `(0a)` this gives

```text
||(Ad(phi_n(h))-I)P_n||_2 <= l eta_n + 2||phi_n(h)-phi_n(s_1)...phi_n(s_l)||_2 = o(1).   (1b)
```

**Step 2 (averaging over a finite head).** Fix a finite `F<=Lambda` and put
`T_n=|F|^-1 sum_(k in F) Ad(phi_n(k))`.  By `(1b)`,
`||(I-T_n)P_n||_2 <= max_(k in F)||(Ad(phi_n(k))-I)P_n||_2 = o(1)`.  For
every projection `Z` on `C^(d_n)`,

```text
||R_Z P_n||_2 <= ||R_Z T_n P_n||_2 + ||(I-T_n)P_n||_2 <= ||R_Z T_n||_2 + o(1),
```

uniformly in `Z`.  Also `||R_Z T_n||_2=||T_n^* R_Z||_2`, and by `(0a)`
together with `phi_n(k)^*=phi_n(k^-1)` we get `T_n^*=T_n` up to `o(1)` in `||.||_2`.  Thus

```text
limsup_n ||R_(Z_n)P_n||_2 <= limsup_n ||T_n R_(Z_n)||_2.                  (2a)
```

**Step 3 (trace formula).** Reindexing `h=k^-1k'` and using `(0a)` gives
`T_n^*T_n=T_n+o(1)` in `||.||_2`.  By `(0c)` and `R_Z^2=R_Z`,

```text
||T_n R_Z||_2^2 = tr_ad(R_Z T_n^* T_n R_Z) = tr_ad(T_n R_Z) + o(1).
```

The operator `Ad(phi_n(h)) R_Z` is `X |-> phi_n(h) X (phi_n(h)^* Z)`.  By
`(0b)` its adjoint trace is `tr(phi_n(h)) tr(Z phi_n(h)^*)`.  Since
`||phi_n(h)^*-phi_n(h^-1)||_2=o(1)`,

```text
lim_n ||T_n R_(Z_n)||_2^2 = |F|^-1 sum_(h in F) tau(h) omega(h^-1).        (3a)
```

**Step 4 (Schur orthogonality).** The functional `omega` is positive on
`C[F]`: `tr(Z_n phi_n(x^*x)) = tr(Z_n phi_n(x)^*phi_n(x)) + o(1) >= o(1)`.
So `omega(x)=sum_sigma Tr(rho_sigma sigma(x))` with `rho_sigma>=0`, summed
over the irreducibles `sigma` of `F` of degree `n_sigma`.  Similarly `tau|_F`
is a normalized positive definite class function, so
`tau|_F=sum_sigma (a_sigma/n_sigma) chi_sigma` with
`a_sigma=tau(p_sigma)>=0` and `sum a_sigma=1`, where `p_sigma` are the
central idempotents.  Schur orthogonality states

```text
|F|^-1 sum_(h in F) chi_sigma(h) sigma'(h^-1) = delta_(sigma,sigma') I/n_sigma.
```

Applying it to `(3a)` gives

```text
lim_n ||T_n R_(Z_n)||_2^2 = sum_sigma a_sigma omega(p_sigma)/n_sigma^2
  <= tau(P_F) omega(P_F) + omega(1-P_F)/delta(F)^2,                      (4a)
```

because the trivial idempotent is `P_F` and every nontrivial `n_sigma` is at
least `delta(F)`.  With `(2a)` this is the first line of `(FSS2)` for
`F=F_m`.

`P_(F_m)-P_(F_(m+1))` is a projection in `C[F_(m+1)]`, so `tau(P_(F_m))` and
`omega(P_(F_m))` decrease.  The GNS images of `P_(F_m)` decrease strongly to
the projection onto the `L_inf`-invariant vectors.  Since
`omega(1-P_(F_m))<=1` and `delta(F_m)->infinity`, letting `m->infinity` gives
the second line of `(FSS2)`.

Taking `Z_n=I` (so `omega=tau`) and using `||P_n||_2^2=tr_ad(P_n)` together
with `tau(1-P_F)<=1` gives `(FSS1)`.

**Step 5 (left support).** The antiunitary `theta X=X^*` on `H_n` satisfies
`theta Ad(U) theta^-1=Ad(U)`.  So it commutes with `A_n`, and hence with the
real spectral projection `P_n`.  It also satisfies
`theta R_Z theta^-1=L_Z`, because `(X^*Z)^*=ZX`.  Conjugation by an
antiunitary preserves the Hilbert--Schmidt norm, so for every `n`

```text
||L_Z P_n||_2 = ||theta R_Z P_n theta^-1||_2 = ||R_Z P_n||_2.
```

This is the equality in `(FSS2)`.

**Step 6 (FSS3).** Suppose `W<=P` is a projection.  Then
`tr_ad(W)=||W||_2^2`, and `R_Z W=R_Z P W`, so

```text
||W||_2 <= ||R_Z P W||_2 + ||(I-R_Z)W||_2 <= ||R_Z P||_2 + ||(I-R_Z)W||_2.
```

For an arbitrary projection `R`, split
`tr_ad(R)=tr_ad(R(I-P)R)+||PR||_2^2`.  The first term is at most
`tr_ad(RAR)/b`, because `I-P=1_(b,infinity)(A)<=A/b`.  For the second,

```text
||PR||_2 <= ||P R_Z R||_2 + ||P(I-R_Z)R||_2
         <= ||R_Z P||_2 + ||(I-R_Z)R||_2.
```

The left-support versions follow from Step 5.

**Step 7 (FSS4).** Let `J in F_m`.  Then `J P_(F_m)=P_(F_m)` in `C[G]`, so
`phi_n(J)phi_n(P_(F_m))=phi_n(P_(F_m))+o(1)`.  Using
`|tr(Z(1+U)B)| <= ||Z(1+U)||_2 ||B||_2` and `||phi_n(P_(F_m))||_2<=1`,

```text
tr(Z_n phi_n(P_(F_m)))
  = -tr(Z_n phi_n(J) phi_n(P_(F_m))) + tr(Z_n(1+phi_n(J))phi_n(P_(F_m)))
  = -tr(Z_n phi_n(P_(F_m))) + o(1).
```

Hence `omega(P_(F_m))=0`, and `(4a)` with `(2a)` gives `(FSS4b)`.  With
`(FSS3)`, both the subspace and the energetic consequences follow.

For the spectral projection, look at an eigenvalue `lambda` of the unitary
`U=phi_n(J)` with `Re(lambda)<0`.  Then `|lambda-1|>=sqrt(2)`, so
`|1+lambda|=|lambda^2-1|/|lambda-1|<=|lambda^2-1|/sqrt(2)`.  Every
subprojection `Y<=Z_n` satisfies `||Y(1+U)||_2=||Y Z_n(1+U)||_2<=||Z_n(1+U)||_2`,
and `||U^2-1||_2=||phi_n(J)^2-phi_n(J^2)||_2=o(1)`.

**Step 8 (FSS5).** In the unilateral-shift model of
`toeplitz-head-tail-unital-self-embedding` (shift model, classical), `T`
acts faithfully on `F_2[N]`.  The elements `e_ij=x^i(1+xy)y^j` are the
matrix units, and their span `F` is a two-sided ideal, because every element
of `T` has finitely supported rows and columns.  The argument has six parts.

(a) `L_inf<=EL_r(T)`.

- A transvection `I+E_((i,a),(j,b))` with `a!=b` is the elementary matrix
  `E_ab(e_ij)`.
- If `a=b` and `i!=j`, choose a column `c!=a` and any `k`.  The commutator
  identity `[I+E_(u,w),I+E_(w,v)]=I+E_(u,v)`, for pairwise distinct `u,v,w`,
  with `w=(k,c)` produces it.
- `GL_n(F_2)=SL_n(F_2)` is generated by transvections (classical).

So every `F_m`, and hence `L_inf`, lies in `EL_r(T)`.

(b) `L_inf` is a kernel.  An invertible matrix congruent to `I` modulo
`M_r(F)` is exactly an invertible finitary matrix over `F_2` on `N x [r]`.
So `L_inf` is the kernel of `EL_r(T)->GL_r(T/F)`, and it is normal.

(c) Simplicity.  `F_m`, isomorphic to `SL_(rm)(F_2)`, is simple for `rm>=3`
(Jordan--Dickson, classical).  An increasing union of simple groups is
simple.

(d) `delta(F_m)->infinity`.  Every nontrivial irreducible representation of
a simple group is faithful.  By Jordan's theorem (classical), a finite
subgroup of `GL_d(C)` has an abelian normal subgroup of index at most `j(d)`.
A nonabelian simple group has no nontrivial abelian normal subgroup, so it
embeds in `GL_d(C)` only if its order is at most `j(d)`.  Since
`|F_m|->infinity`, this gives `delta(F_m)->infinity`.

(e) Finite-dimensional representations kill `L_inf`.  The kernel of a
finite-dimensional unitary representation meets the simple group `L_inf`
either trivially or entirely.  It cannot be trivially, since then every
`F_m` would embed in `U(d)`, contradicting (d).  Finite quotients give
finite-dimensional representations, so they kill `L_inf` too.

(f) `iota(<Q,Z>)<=F_2`.  In the proof of
`schur-child-crosses-toeplitz-compressor` every `q`- and `z`-coordinate is
scaled by `e_1=x f y=e_11`, and `B_0=0`.  So `g(0,q,z)-I` has all entries in
`F_2 e_11`.  It is supported on head index `1`, which lies in `N_(<2)`.

Now let `rho_n` be any packet representations with
`||rho_n(J)-phi_n(iota J)||_2->0`.  The range of `R_A-R_B` in
`predicate-rank-jump-forces-adjoint-reynolds-gap`, extended by zero,
consists of operators `X=Z_n X Z_n` with `Z_n=(1-rho_n(J))/2`.  Then
`||Z_n(1+phi_n(iota J))||_2->0`, so Step 7 applies to every `W_n<=P_n`
inside that range, and to every sector-supported low-commutator subspace.

**Step 9 (FSS6).**

*Centrality.*  Let `u` be a letter with `u L_inf u^-1<=L_inf`.  The
projection `u e_inf u^-1` is the projection onto vectors invariant under
`u L_inf u^-1`, so `e_inf<=u e_inf u^-1`.  Both have trace `tau(e_inf)`, and
`tau` is faithful on `M`, so they are equal.  The reverse inclusion is
symmetric.  So `e_inf` commutes with a generating set, and `e_inf` lies in
`M`, being a strong limit of `P_(F_m)`.  Hence `e_inf` is central.

*Compression.*  The central compression is a normalized trace on
`M(1-e_inf)`.  Since `P_(F_m)e_inf=e_inf`,

```text
tau'(P_(F_m)) = (tau(P_(F_m))-theta)/(1-theta) -> 0.
```

If `y=y(1-J)/2` with `J in L_inf`, then `J e_inf=e_inf` gives
`(1-J)e_inf=0`.  So `y e_inf=0`, and `tau'(y)=tau(y)/(1-theta)`.  If
`theta=1`, then `y=y e_inf=0` in `M` and `tau(y)=0`.

*Hyperlinearity (classical ultraproduct lifting).*

- The microstates give a trace-preserving embedding of `M` into
  `prod_omega M_(d_n)`.
- The image of `1-e_inf` lifts to projections `p_n` with
  `tr(p_n)->1-theta`.
- Each unitary `pi(g)(1-e_inf)` of the corner lifts to a unitary `V_n(g)` in
  `p_n M_(d_n) p_n`.

The maps `g |-> V_n(g)` are microstates with character `tau'`.  If `J_H` is
central, `(1-J_H)/2` is a central projection commuting with `e_inf`, and the
two central compressions commute.

*Verification for `H(alpha,chi)`.*

- `(PHC2)` says `J_H` is central and `q g q^-1=J_H^(chi(g))g`.
- `chi(g,epsilon)=epsilon` vanishes on `L_inf<=EL_4(T) x 0`, so `q`
  centralizes `L_inf`.
- On `L_inf`, `(TPC1)` gives `alpha(g)=beta(g)`, which is entrywise
  `sigma^2`.
- By `(THT1)`, `sigma(e_ij)=e_(i+1,j+1)`, because
  `eps(e_ij)=eps(1+xy)=0`.  So `beta(I+M)=I+sigma^2(M)` is again finitary,
  and `t L_inf t^-1<=L_inf`.
- `Lambda` normalizes `L_inf` by Step 8(b).

**Step 10 (FSS7).**

*(1) implies (2).*  Suppose (2) fails: some hyperlinear `tau` has
`tau(y)>0`.  Step 9 gives a hyperlinear `tau'` with
`tau'(y)>=tau(y)>0` and `tau'(e_inf)=0`.  Its microstates have forbidden
mass tending to `q'=tau'(y)`, but by `(FSS1)` every `W_n<=1_[0,b](A_n)` has
`tr_ad(W_n)->0`.  So (1) fails.

*(2) implies (1).*  `G` is countable, so a diagonal subsequence of
`tr o phi_n` converges pointwise to a hyperlinear character `tau` with
`tau(y)=q`.  Under (2) no sequence with `q>0` exists, and (1) is vacuous.

*Consequences.*

- `(PCD1)` implies (1), because `c q_n^2-C sqrt(E_n)->c q^2`.
- For a nonzero projection `y`, `tau_can(y)=||y||_(ell^2)^2>0`.  So (2)
  implies that `G` is not hyperlinear.
- On a sequence satisfying `(PCD1)`, `(FSS1)` gives `tau(e_inf)>=sqrt(c)q`.
- The marked version replaces `y` by the projection `y(1-J_H)/2`, which
  still satisfies `y'=y'(1-iota J)/2`.

Classical ingredients: generation of `SL_n(F_2)` by transvections,
simplicity of `SL_n(F_2)` for `n>=3` (Jordan--Dickson), Jordan's theorem on
finite linear groups, Schur orthogonality, and ultraproduct lifting of
projections and unitaries.  None was re-fetched for this route.
