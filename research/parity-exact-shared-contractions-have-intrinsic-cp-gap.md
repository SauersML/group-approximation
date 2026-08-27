---
rg: 2
id: parity-exact-shared-contractions-have-intrinsic-cp-gap
kind: claim
title: Exact shared parity contractions collapse to reflections and have a pre-character intrinsic CP gap
distinct_from:
  intrinsic-finite-green-commutator-step-has-the-correct-tangent: that identifies the intrinsic map and its derivative at a global exact code tuple; this obtains the CP spectral gap directly from exact local face PVMs, before global commutativity or characters.
  gapped-face-pinchings-give-same-hilbert-code-pvm-rounding: that projects directly to the common commutant and signs/decodes; this transfers the same face Hamiltonian gap to the coordinate CP Green operator used by the intrinsic nonlinear step.
  aggregate-cut-compression-stores-boundary-as-involution-defect: that begins with genuinely nonunitary block compressions; this shows exact shared parity re-exactification eliminates their involution defects automatically.
---

ESTABLISHED RESTRICTED COERCIVITY.  Consider a literally shared tuple of
selfadjoint contractions `X_1,...,X_L`.  Suppose every coordinate belongs
to an exact bounded parity face, and on each face the contractions commute
and their prescribed product is `I`.  Then every `X_i` is a reflection.

Indeed, if contractions `T_1...T_m=I`, then for every vector

```text
 ||xi||=||T_1...T_m xi||<=...<=||xi||.                 (PES1)
```

Equality throughout makes every factor an isometry on the successive
ranges; in finite dimension each is unitary.  A selfadjoint unitary is a
reflection.  Thus all positive defects `E_i=I-X_i^2` vanish once the local
parity faces are exact on one shared tuple; `(TCB7)` becomes exact endpoint
oddness rather than a forcing estimate.

Put

```text
 P_i=(I-Ad(X_i))/2,
 A_X=(1/L)sum_i(I+Ad(X_i))/2=I-Pbar,
 Pbar=(1/L)sum_iP_i.                                   (PES2)
```

For an exact face `c`, its coordinate adjoint involutions commute and its
whole-face pinching is

```text
 Phi_c=product_(i in c)(I-P_i),
 I-Phi_c<=sum_(i in c)P_i.                             (PES3)
```

Let `H=avg_c(I-Phi_c)`.  Assume the established redundant-overlay face gap

```text
 <V,HV> >=gamma||V-E_KV||_2^2,                         (PES4)
```

where `K` is the common commutant.  If

```text
 C_occ=max_i deg(i)*L/|faces|,
```

then bounded occurrence and `(PES3)` give

```text
 H<=C_occ Pbar,
 <V,Pbar V> >=(gamma/C_occ)||V-E_KV||_2^2.             (PES5)
```

Consequently `A_X` is a ucp selfadjoint contraction, fixes `K`, and on
`K^perp` has `L_2` norm at most

```text
 1-delta_0,       delta_0=gamma/C_occ>0.                (PES6)
```

For every fixed `K_0`, the intrinsic Green polynomial

```text
 G_(X,K_0)=sum_(t=0)^(K_0-1)A_X^t
```

therefore has cb norm at most `K_0` and error at most
`(1-delta_0)^(K_0)` off the common commutant.  This is a genuinely
pre-character proof: it uses exact local face pinchings and their
Hamiltonian gap, not a global joint character decomposition or global
commutativity.  Combined with exact commutator oddness, it supplies the
linear CP-Green contraction required by the intrinsic step on this
restricted phase.

The remaining equality interface is sharp.  Exact local faces generally
live on separate occurrence copies.  Small normalized-HS equality defect
does not transfer `(PES6)` to a chosen shared representative in operator
norm on `L_2(M)`.  For example, with `Q=I` and `Q'=I-2p`,

```text
 ||Q-Q'||_2=2sqrt(tau(p))->0,                           (PES7)
```

but on a nonzero off-diagonal block `pM(1-p)`, `Ad(Q')-Ad(Q)` has
`L_2->L_2` norm `2`.  Thus selecting equality representatives, averaging
them, or replacing one exact occurrence by another can destroy the CP-gap
hypothesis on a sparse physical corner at order one.

Accordingly, `off-base-row-gradient-coercivity` is bypassed after **both**
local exactification and literal sharing, but not before.  The residual gate
is now the equality-compatible operation that creates one shared exact-face
tuple (or removes the sparse equality corner) without using an operator-norm
perturbation argument.  The exact oddness identity, positive involution
defects, and dense cb remainder do not by themselves solve this occurrence
synchronization.

The channel-gap part of this interface is now resolved without literal
sharing.  `averaged-pinching-channels-are-row-square-lipschitz` proves that
the normalized averaged channels of local exact occurrences and shared
representatives differ on `L_2` by at most the square root of their common
operator row-square displacement.  Consequently the fixed-time face gap
survives on the retained equality-low block with error `K sqrt(||H||)`.
What remains is not transfer of the CP gap, but paying the high equality
sector and the sparse face-product damage of the shared intrinsic update.
