---
rg: 2
id: bcs-atom-detects-its-e5-central-root
kind: claim
title: A selected BCS atom has positive mass on its E5 central-root support
distinct_from:
  hs-steinberg-morita-trace-additivity-on-adaptive-blocks: That asks for one globally compatible additive mass on the whole bounded adaptive tree; this is the local payload-to-root support estimate at one named source idempotent.
  e5-idempotent-root-has-two-pair-extraspecial-cell: That uniformly splits mass already lying in a nontrivial central-root sector; this must put the actual BCS atom into that sector.
  marked-hs-separation-forces-spectral-density: That lower-bounds spectral density from displacement of the root word itself; this must lower-bound the root displacement/support on the particular BCS projection.
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That reconstructs a rank-metric model of the whole conditional coefficient quotient; this asks only for one overlap inequality on the finite adaptive menu.
---

**OPEN PAYLOAD-TO-ROOT INTERFACE.**  In a normalized-HS microstate of the
rank-five wordization of `finite-adaptive-selected-atom-ring-tree`, fix one
node and forbidden type and write

```text
E=Q_sigma P_i,              a=a_(sigma,i),
Z=x_13(a),
S_Z=1-P_(Z,1),                                      (BZR1)
```

where `E` is formed from the rounded shared BCS tuple and `P_(Z,1)` is the
`1`-eigenspace projection of the exactified order-`p` root word `Z`.
Prove, with constants independent of matrix dimension,

```text
tr(E S_Z)>=c_root tr(E)-C sqrt(E_pres),                (BZR2)
```

for one fixed `c_root>0`.  The same estimate is required only for the finite
menu of sources up to the chosen contradiction depth.

The algebraic transverse packet is already present.  By
`e5-idempotent-root-has-two-pair-extraspecial-cell`, the four canonical
roots with coefficient `a` form two Heisenberg pairs centered at `Z`.  Once
`E S_Z` approximately reduces that fixed packet, finite Stone--von Neumann
gives a joint spectator atom of mass

```text
p^(-2) tr(E S_Z).                                     (BZR3)
```

Thus `(BZR2)` supplies the conditioned-source mass which the bare additive
table lacks.

This claim is not a consequence of root spectral density alone.  The group
microstate is an abstract unitary representation of the Steinberg
wordization, not the canonical elementary-matrix representation of the
coefficient star algebra.  Root relations make the common root kernel a
two-sided coefficient ideal, but they do not presently reflect the
operator-valued BCS projection into the complement of that kernel.  Proving
that reflection is the local finite-menu version of the metric decoder.

The most direct multiplicative-covariance proof is now ruled out exactly.
`root-scaling-covariance-does-not-detect-bcs-atom` observes that the
relations obtained from `u_j a=plus_or_minus a` admit a one-dimensional
marked representation with the prescribed BCS joint character and with the
entire root packet trivial.  Thus conjugation of `Z` by the assignment
involutions, even together with the two transverse Heisenberg pairs, cannot
imply `(BZR2)`.  A successful estimate must use a mixed row which prevents
the coefficient `a` from entering the root kernel on the physical BCS
carrier.

There is one exact canonical-trace subcase.  By
`coprime-root-reynolds-prefix-overlap`, if
`E` is itself a character idempotent of a fixed finite two-group and `Z`
has exact odd prime order `p`, then coprimality gives

```text
tr(E S_Z)=(1-p^(-1))tr(E)+o(1).                       (BZR4)
```

This closes `(BZR2)` at the initial Pauli/BCS Reynolds seed.  It also closes
it after any genuinely literal product of independent commuting prefix-sign
cuts, because the resulting `E` is again one finite-two-group character
idempotent.  It does **not** cover the `Q_sigma` needed by the adaptive ring
decoder when that carrier is an analytic reducing hull or a decoded
coefficient corner.  Such a `Q_sigma P_i` is not a fixed group-algebra
Fourier polynomial, so canonical word moments do not determine its overlap
with the trivial `Z`-sector.  Moreover the literal-prefix alternative cannot
amplify: `companion-free-prefix-return-has-exponential-regular-capacity`
forces its canonical mass to decay as `2^(-|sigma|)`.

There is a separate algebraic typing prerequisite.  The compiler
`finite-adaptive-selected-atom-ring-tree` is presently stated over a
characteristic-zero splitting ring, whereas `(BZR1)--(BZR3)` use an
exactified root of odd prime order.  The latter is automatic only after an
explicit odd-characteristic version has been chosen: over a ring of
characteristic `p`, a nonzero coefficient `a` gives

```text
x_13(a)^p=1,
x_13(a)!=1 in E_5(R),                                  (BZR5)
```

the second assertion following from the elementary-matrix image
`1+aE_13`.  In characteristic zero the same root is generally infinite
order, so the finite Fourier projection in `(BZR1)` is not available.
The required base change and nonvanishing audit are now supplied by
`odd-characteristic-adaptive-tree-wordization`.  Thus exact root order is no
longer part of this open claim, but it must be imported through that node
rather than silently from the characteristic-zero compiler.  The only open
content here is the metric payload reflection on nonliteral carriers.

There is now a useful exact control experiment showing that **analyticity of
the carrier is not by itself the obstruction**.
`a4-role-atom-has-flat-c3-root-overlap` uses
`A4=V4 semidirect C3`.  On the three-dimensional block, every nontrivial
`V4` character atom has compression `1/3` against the trivial `C3` Fourier
projection.  The identity remains exact after multiplication by an arbitrary
projection in the `A4` commutant, so it applies to analytic reducing hulls
and decoded multiplicity corners without canonical trace moments.

What it does not do is make the auxiliary `C3` generator equal to the root
`x_13(a)`.  In the perfect model `a=0` and the latter root is `1`, whereas
the auxiliary generator remains nontrivial on the selected `A4` block.
Literal identification therefore breaks perfect completeness.  Making the
finite block collapse conditionally with `a` merely restates the missing
Steinberg payload reflection.  The remaining obstruction is consequently
not "nonliteral carrier versus finite Fourier polynomial"; it is the
**conditional identity of the detected odd root with the coefficient root
that vanishes when the payload vanishes**.

Even `(BZR2)` is not by itself the final theorem: the edgewise oriented
tables must still assign one common mass to the same parent carrier across
all outgoing types.  It separates the two remaining issues cleanly:

```text
payload-to-root detection,       then       global common orientation.
```
