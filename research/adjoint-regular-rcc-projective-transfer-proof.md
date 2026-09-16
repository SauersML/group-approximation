---
rg: 2
id: adjoint-regular-rcc-projective-transfer-proof
kind: route
title: Tensor with canonical microstates, pass to the adjoint tuple, and double the witness with the identity
target: adjoint-regular-rcc-gives-projective-transfer
requires:
  - projective-transfer-linear-bound-equals-no-ultraproduct-leak
artifacts:
  - research/artifacts/adjoint-regular-rcc-projective-transfer-2026-09-16.md
---

Notation is that of the claim.  For unitaries `X,Y` in a tracial von
Neumann algebra,

```text
XY-YX=(XYX^*Y^*-1)YX,   so   ||XY-YX||_2=||[X,Y]-1||_2.   (AP0)
```

For `W in U(k)` put `Ad(W)=W tensor conj(W) in U(k^2)`, conjugation taken
entrywise in the standard basis.  Every tensor, direct-sum and `Ad`
construction below is applied letter by letter to an assignment, and all
three operations are multiplicative and commute with inverses.  Hence the
evaluation of a word on the new assignment is the same construction applied
to the evaluation on the old one.

**Elementary estimates.**

(AP1) `tr(Ad(W))=tr(W) conj(tr(W))=|tr(W)|^2`, so
`||Ad(W)-I||_2^2=2-2 Re tr(Ad W)=2-2|tr(W)|^2`.  This is `(AR4)`.

(AP2) `Ad([U,V])=[Ad U,Ad V]` by multiplicativity.

(AP3) For `V in U(k)`, with `x=Re tr(V) in [-1,1]`,

```text
||Ad(V)-I||_2^2=2-2|tr V|^2 <= 2-2x^2=2(1-x)(1+x)
              <= 4(1-x)=2||V-I||_2^2.
```

(AP4) The normalized Hilbert--Schmidt norm is multiplicative on tensor
products.  Hence for unitaries `V,W`,
`V tensor W-I=(V-I) tensor W+I tensor(W-I)` gives
`||V tensor W-I||_2<=||V-I||_2+||W-I||_2`.

(AP5) For `W in U(k)` and `t=tr(W)`, `tr(W direct_sum I_k)=(1+t)/2` and

```text
1-|1+t|^2/4-(1-Re t)=-(1-2Re t+|t|^2)/4=-|1-t|^2/4<=0.
```

Since `||W-I||_2^2=2-2Re t`, this is `(AR5)`.  Conversely, if
`1-|(1+t)/2|^2<=epsilon`, then
`4(1-epsilon)<=|1+t|^2=1+2Re t+|t|^2<=2+2Re t`, so

```text
||W-I||_2^2=2-2Re t<=4 epsilon.                         (AP6)
```

**Liftings.**  A tracial matrix ultraproduct is `M=prod_omega M_(k_n)` for
a free ultrafilter `omega`.  Every unitary of `M` has a representing
sequence of unitaries (polar decomposition of any bounded representative).
If `pi:A->U(M)` is a unitary representation and `rho_n(x)` are unitary
representatives of `pi(x)`, then for each word `w` the sequence
`rho_n(w)` represents `pi(w)`.  Conversely, if assignments `beta_n` satisfy
`delta(beta_n)->0`, the elements `(beta_n(x))_omega` satisfy every
defining relator exactly, so they define a representation `pi` of `A`, and
`pi(g)=(beta_n(w))_omega` for every word `w` representing `g`: two words
for `g` differ by a fixed finite product of conjugates of relators, whose
evaluation is within a fixed multiple of `delta(beta_n)` of `I`.

## (AR2) implies (AR3), for any finitely presented A

Let `pi:A->U(M)` be any unitary representation into
`M=prod_omega M_(k_n)`, and let `u in pi(C)' cap M` be unitary.  Choose
unitary representatives `rho_n(x)` of `pi(x)` and `u_n` of `u`.  Along
`omega`, `delta(rho_n)->0` because `R` is finite and `pi(r)=1`, and for
`s in S`, by `(AP0)`,

```text
||[u_n,rho_n(s)]-I||_2=||u_n rho_n(s)-rho_n(s)u_n||_2
                     -> ||u pi(s)-pi(s)u||_2=0.
```

Double the tuple and the witness:

```text
rho'_n(x)=rho_n(x) direct_sum rho_n(x),   u'_n=u_n direct_sum I.
```

Then `rho'_n(w)=rho_n(w) direct_sum rho_n(w)`, `delta(rho'_n)=delta(rho_n)`
(the normalized norm of `Y direct_sum Y` equals that of `Y`), and
`[u'_n,rho'_n(w)]=[u_n,rho_n(w)] direct_sum I` for every word `w`.  By
`(AP5)`,

```text
q(rho'_n,u'_n)<=(1/2) sum_(s in S)||[u_n,rho_n(s)]-I||_2^2 -> 0.
```

Applying `(AR2)` to these finite assignments gives
`e_h(rho'_n,u'_n)<=L(q(rho'_n,u'_n)+delta(rho'_n))->0`.  The target
commutator of the doubled pair is `[u_n,rho_n(h)] direct_sum I`, so
`(AP6)` gives

```text
||u_n rho_n(h)-rho_n(h)u_n||_2^2=||[u_n,rho_n(h)]-I||_2^2
                               <=4 e_h(rho'_n,u'_n) -> 0.
```

Thus `u` commutes with `pi(h)`.  The unitaries commuting with `u` form a
group containing `pi(C)` and `pi(h)`, hence `pi(A)` by `(AR0)`.  The finite
von Neumann algebra `pi(C)' cap M` is the linear span of its unitaries, so
`pi(C)' cap M` is contained in `pi(A)' cap M`; the reverse inclusion is
automatic.  No trace condition and no hyperlinearity were used.

## (AR3) implies (AR1)

Regular-trace representations are a special case.

## (AR1) implies (AR2)

Suppose `(AR2)` fails.  By
`projective-transfer-linear-bound-equals-no-ultraproduct-leak`
(`(PL2)` iff `(PL3)`, for the same presentation, words `S` and word `h`),
there are assignments `rho_n:X->U(d_n)` and unitaries `U_n` with

```text
delta(rho_n)->0,   q(rho_n,U_n)->0,   e_h(rho_n,U_n)>=epsilon>0   (AP7)
```

for all `n`, after passing to a subsequence.  Their trace profile is
arbitrary, so `(AR1)` cannot be applied to them directly.

**Step 1: regularize the trace.**  Since `A` is hyperlinear, there are
assignments `sigma_n:X->U(k_n)` with `delta(sigma_n)->0` and
`tr(sigma_n(w))->0` for every word `w` representing a nontrivial element
of `A`.  (Take the restriction to `X` of almost multiplicative maps
`phi_n:A->U(k_n)` with `tr(phi_n(g))->0` for `g!=1`; almost
multiplicativity makes `phi_n(1)` and `phi_n(x^-1)phi_n(x)` tend to `I`,
so every relator evaluates near `I` and every word for `g` evaluates near
`phi_n(g)`.  If `A` is residually finite one may instead use the regular
representations of separating finite quotients, which have zero defect.)
Put

```text
rho~_n(x)=rho_n(x) tensor sigma_n(x),   U~_n=U_n tensor I_(k_n).
```

For every word `w`, `rho~_n(w)=rho_n(w) tensor sigma_n(w)`, so `(AP4)`
gives `delta(rho~_n)<=delta(rho_n)+delta(sigma_n)->0`, and

```text
[U~_n,rho~_n(w)]=[U_n,rho_n(w)] tensor I,
|tr(rho~_n(w))|=|tr(rho_n(w))| |tr(sigma_n(w))|<=|tr(sigma_n(w))|.
```

Therefore all trace-square energies are unchanged,
`q(rho~_n,U~_n)=q(rho_n,U_n)` and `e_h(rho~_n,U~_n)=e_h(rho_n,U_n)`, while
`tr(rho~_n(w))->0` for each word `w` representing a nontrivial element.

**Step 2: pass to the adjoint.**  Put `beta_n(x)=Ad(rho~_n(x))` and
`T_n=Ad(U~_n)`.  Then `beta_n(w)=Ad(rho~_n(w))`, `(AP3)` gives
`delta(beta_n)<=sqrt(2) delta(rho~_n)->0`, and `(AP1)` gives
`tr(beta_n(w))=|tr(rho~_n(w))|^2->0` for every word representing a
nontrivial element.  By `(AP0)`, `(AP2)` and `(AP1)`, for every word `w`,

```text
||T_n beta_n(w)-beta_n(w)T_n||_2^2
   =||Ad([U~_n,rho~_n(w)])-I||_2^2
   =2(1-|tr([U_n,rho_n(w)])|^2).                        (AP8)
```

Hence `sum_(s in S)||T_n beta_n(s)-beta_n(s)T_n||_2^2=2q(rho_n,U_n)->0`
and `||T_n beta_n(h)-beta_n(h)T_n||_2^2=2e_h(rho_n,U_n)>=2epsilon`.  The
unknown source scalars have disappeared: the adjoint witness is an honest
approximate commutant vector.

**Step 3: the ultraproduct.**  Let `M=prod_omega M_((d_n k_n)^2)`.  The
liftings paragraph gives a representation `pi:A->U(M)` with
`pi(g)=(beta_n(w))_omega`; for `g!=1`,
`tau(pi(g))=lim_omega tr(beta_n(w))=0`, so `pi` has regular trace.
(If one's convention for matrix ultraproducts needs unbounded dimensions,
replace `sigma_n` by `sigma_n tensor I_n`; nothing above changes.)  The
unitary `T=(T_n)_omega` satisfies
`||T pi(s)-pi(s)T||_2=lim_omega||T_n beta_n(s)-beta_n(s)T_n||_2=0` for
every `s in S`, so `T in pi(C)' cap M`.  By `(AR1)`, `T` commutes with
`pi(h)`, whence `lim_omega 2e_h(rho_n,U_n)=0` by `(AP8)`, contradicting
`(AP7)`.  Therefore `(AR2)` holds.

## What was used

Only hyperlinearity of `A` (Step 1), the linearization theorem, and the
two identities `(AR4)`, `(AR5)`.  Perfectness of `C` or `A` was never used:
source phases are killed by `Ad` and the target phase by doubling with the
identity.  Property `(T)` or `(tau)` was never used.  No particular value of
`L` is produced.
