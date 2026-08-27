---
rg: 2
id: one-nonnormal-dressing-cannot-preserve-moving-full-gram
kind: claim
title: One nonnormal opposite-root dressing cannot preserve the moving full Gram
invalidates:
  - single-opposite-root-dressing-supplies-moving-bridge
artifacts:
  - research/moving-full-gram-transporter-torsor-proof.md
distinct_from:
  compression-preimage-whitehead-preserves-gauge: that treats the three-root Leavitt preimage Whitehead, which has the correct full Gram after changing both charts; this proves the general transporter torsor and rules out a single genuinely nonnormal relative correction before gauge typing.
  finite-extraspecial-mixed-words-cannot-ungauge-singer-transport: that allows many outer normalizer occurrences in a finite normal extension and finds their quotient gauge; this says any full-gram word, finite or not, differs from the known Whitehead by a source normalizer.
  label-only-dressing-cannot-ungauge-a-whitehead-bridge: that assumes the relative normalizers are already typed label-only; this derives normalizer membership from the full-Gram identity but makes no claim about the normalizer's multiplicity typing.
---

**ESTABLISHED TRANSPORTER TORSOR.**  Let `Q` be any projection in a group
algebra or finite matrix model, let `J` be a unitary, and put

```text
Q'=JQJ^(-1).
```

The exact unitary full-Gram transporters from `Q` to `Q'` are precisely

```text
Trans(Q,Q')={w:wQw^(-1)=Q'}
           =J Norm(Q)=Norm(Q') J,                     (OND1)
```

where `Norm(Q)={n:nQn^(-1)=Q}`.  Consequently a proposed bridge written as

```text
w=J y
```

has the correct source and range Grams if and only if `y` normalizes `Q`.
Likewise `w=y'J` works if and only if `y'` normalizes `Q'`.  A single
genuinely nonnormal opposite-root dressing therefore fails `(ESB1)` before
its reservoir gauge can be tested.

This failure occurs for the literal shortest opposite-root candidate in the
signed Hecke packet.  In the actor basis `(2,4,5,6,7,8,9)`, let

```text
d=x_28(1) in L_0,              y=x_82(1).              (OND2)
```

On the `(2,8)` block, in characteristic two,

```text
y d y^(-1)=[[0,1],[1,0]].                              (OND3)
```

Every generator in the directed presentation of `L_0` fixes `e_2`, because
none has source coordinate `2`; the matrix in `(OND3)` does not.  Hence
`yL_0y^(-1)!=L_0`, so conjugation by `y` cannot preserve the signed Reynolds
idempotent `Q=e_(L_0,lambda_0)`.  Thus neither `Jy` nor the corresponding
target-side dressing has the moving full Gram.

The result is sharp about what remains.  A successful word `w` may be built
from nonnormal opposite-root pieces, but their total relative correction

```text
n=J^(-1)w                                               (OND4)
```

must return to `Norm(Q)`.  Therefore the smallest surviving genuinely
nonnormal gadget contains at least two exits from the Hecke atom algebra and
an exact return relation.  Its returned normalizer must then have a
reservoir action cancelling the Whitehead gauge; neither normalizer
membership nor `(OND1)` supplies that typing.

No Property `(T)`, trace profile, approximation theorem, or Steinberg lift
is used.

DERIVATION
moving-full-gram-transporter-torsor-proof
