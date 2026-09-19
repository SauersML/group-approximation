---
rg: 2
id: dual-prefix-renyi2-rate-is-critical-under-rectangular-escape
kind: claim
title: Dual-prefix address coding is Renyi-2 critical under exact rectangular escape
invalidates:
  - paired-reservoir-via-renyi2-soft-covering
distinct_from:
  rectangular-escape: that constructs the exact label/multiplicity exchange; this proves the information-theoretic ceiling which prevents that exchange from having a strict soft-covering rate gap.
  binary-schur-canonical-weights-have-half-reservoir-escape: that gives stationary canonical character weights under one Schur split; this applies to every cq encoding of a finite dual-prefix address alphabet and computes the sharp Renyi-2 budget.
  paired-prefix-shears-have-bounded-joint-approximate-rank: that bounds robust algebraic rank for finite prefix phase tables; this is an entropy ceiling even when the whole address is perfectly distinguishable.
---

Let `X` be a classical register with support of cardinality `D` and let

```text
rho_XE=sum_x p_x |x><x| tensor rho_x                 (RCR1)
```

be any cq state.  For the sandwiched order-two mutual information

```text
I~_2(X:E)=inf_(sigma_E) D~_2(rho_XE || rho_X tensor sigma_E),
```

one always has

```text
I~_2(X:E)<=log D.                                     (RCR2)
```

If a classical codebook indexes all `D` addresses and permits lossless
recovery of the address--which is necessary for the covering conclusion to
identify all dual-prefix children and their return maps--then its size `M`
satisfies `M>=D`.  Consequently its unnormalized rate obeys

```text
R=log M>=log D>=I~_2(X:E),                             (RCR3)
```

so no fixed `epsilon>0` can satisfy

```text
R<=I~_2(X:E)-epsilon.                                 (RCR4)
```

The same statement in per-prefix units is obtained by taking `D=2^N` and
dividing by `N`: lossless recovery gives `R_N>=1` while
`I~_2(X:E)/N<=1`.  Allowing decoding error tending to zero does not create a
uniform gap.  Fano's inequality gives

```text
log M >= log D-h_2(q)-q log(D-1),                      (RCR5)
```

so for `D=2^N` and `q=o(1)` the rate lower bound tends to `1`, exactly the
same ceiling.

## Proof of the Renyi ceiling

Put `rho_bar=sum_x p_x rho_x` and use `sigma_E=rho_bar` in the infimum.
Since

```text
rho_bar>=p_x rho_x,
```

the max-relative entropy satisfies

```text
D_max(rho_x || rho_bar)<=-log p_x.
```

Sandwiched Renyi divergence is monotone in its order, hence

```text
D~_2(rho_x || rho_bar)<=D_max(rho_x || rho_bar)
                       <=-log p_x.                    (RCR6)
```

The block-diagonal formula for `(RCR1)` gives

```text
exp D~_2(rho_XE || rho_X tensor rho_bar)
 =sum_x p_x exp D~_2(rho_x || rho_bar)
 <=sum_x p_x/p_x
 =D.                                                   (RCR7)
```

Taking logarithms proves `(RCR2)`.  The codebook bound is the pigeonhole
principle for exact decoding, and `(RCR5)` is the standard counting/Fano
bound for a finite classical message.

## Sharp dual-prefix countermodel

At depth `N`, the exact chart

```text
Phi_N(e_(u,v))=E_(u,v),       |u|=|v|=N,               (RCR8)
```

has `D=2^N` uniform address atoms.  The finite rectangular model exchanges a
label factor for spectator multiplicity while preserving ambient dimension,
all finite packet multiplication/return tables, and their canonical moments.
It yields a dichotomy for any honest choice of the system called `E`:

1. If `E` is the actual spectator multiplicity reservoir, it is unchanged
   across the uniform address mixture.  Thus
   `rho_XE=rho_X tensor rho_E` and `I~_2(X:E)=0`; no nonnegative code rate can
   lie below it by a positive constant.
2. If the target label factor is adjoined to `E` so that `E` remembers the
   address, take the orthogonal address state

   ```text
   rho_XE=D^(-1) sum_u |u><u| tensor |u><u|.            (RCR9)
   ```

   Then `I~_2(X:E)=log D`, and the lossless codebook of the `D` labels has
   `R=log D`.  Both inequalities are equalities, not a strict rate gap.

The exact finite chain in
`whitehead-swap-copy-completion-retains-rectangular-escape` realizes this at
every fixed depth with zero typed boundary defect.  Passing to the finite
packet's regular representation supplies the canonical scalar moments; on a
chosen nontrivial central-character sector `(RCR9)` is the ordinary matrix
unit model.  Spectator amplification changes neither normalized moments nor
the information calculation.

There is also a direct incompatibility with clauses 1 and 3 of the proposed
rate compiler, independent of how its numerical rate is normalized.  The
soft-covering route uses clause 1 in the direction

```text
failure of covering => positive named boundary energy.              (RCR10)
```

The exact rectangular chain has zero named typed boundary energy.  Hence any
comparison strong enough to prove `(RCR10)` must call this model successfully
covered.  Clause 3 would then identify the old and refined packet on one
multiplicity reservoir.  But the model has source label/multiplicity profile

```text
M_D tensor I_m
```

and refined profile

```text
M_(2D) tensor I_(m/2)                                  (RCR11)
```

for divisible `m`, so it is exactly a change of reservoir rather than a
same-reservoir return.  Thus the three requested clauses cannot all hold on
the canonical dual-prefix language even if one assigns a formal rate not
interpretable as a lossless address code.  Such an assignment either breaks
the boundary/divergence comparison or loses the same-reservoir conclusion.

Therefore the canonical dual-prefix moments force at most the critical
address rate.  They cannot furnish the depth- and dimension-independent
strict inequality required by `dual-prefix-renyi2-rate-gap`.  Soft covering
can be applied only after adding a genuinely new same-reservoir
authentication datum; it cannot itself manufacture that datum from the
dual-prefix system.
