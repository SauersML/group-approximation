---
rg: 2
id: paired-same-reservoir-boundary-lemma
kind: claim
title: Paired Leavitt children either remain in one multiplicity reservoir or pay their full boundary mass
artifacts:
  - research/artifacts/affine-leavitt-normalized-hs-decoder-audit-2026-08-21.md
distinct_from:
  same-orbit-closure: that asks only for asymptotic square closure on positive paired mass; this is the fixed-depth quantitative leakage alternative needed to prove the affine boundary estimate.
  mixed-relations-force-holonomy-or-transverse-recovery: that asks for a holonomy/transverse-recovery dichotomy on one Pauli overlap; this asks for a boundary ledger through the actual rank-five affine-Leavitt root triangles.
  closed-multiplicity-cycle-kills-carrier-trace: that proves the trace endpoint after the reservoir has returned; this must identify that reservoir or charge the mass that escapes it.
---

OPEN.  Fix a depth `N` in the affine-Leavitt Steinberg presentation.  On the
positive-mass paired long-root sectors recovered from canonical-trace
normalized-HS microstates, decompose each of the first `N` binary branch
steps so that, up to a fixed-depth constant times the named relator and trace
separation error, every unit of parent mass satisfies one of:

1. its two Leavitt children and their two return maps act on the same
   source-sized paired label space and the same multiplicity reservoir; or
2. the unit leaves that reservoir and the leaked normalized mass is charged
   by a paired Steinberg multiplication-triangle defect.

The constants may depend arbitrarily on `N`, but not on matrix dimension or
on the recovered label cardinalities.  The estimate must explicitly exclude
`rectangular-escape`: increasing the child Weyl-label factor while shrinking
its multiplicity is not a closed branch and must enter the leakage term.

Once branch (1) holds, no further near-bijection theorem is needed:
`bistochastic-diagonal-return-forces-aligned-permutation` rounds the square
forward/return pair, and the robust paired `1/36` floor charges the crossed
zero relation.  If the same reservoir closes only after several binary
steps, `closed-multiplicity-cycle-kills-carrier-trace` sums the whole return
with coefficient exactly `3`, independent of depth.  Thus the mathematical
content of this claim is solely the matrix-coordinate identification of the
same finite multiplicity reservoir, or an HS-visible payment for leaving it.

A potentially weaker sufficient form uses transverse descendants instead of
label cardinalities: the mixed rank-five words must recover one and the same
fixed-density projection in both trace-independent child algebras.  Then
`tensor-independent-child-carrier-gap` supplies an immediate dimension-free
energy floor.  Producing unrelated carriers on the two sides is insufficient.

For the specific exact Pauli atlas there is an even weaker, non-generic
alternative.  Its two *distinct* canonical quarter carriers already have D8
holonomy `1/2`.  Therefore it is enough to recover the first in one child
algebra and the second in the commuting transverse child algebra;
`separate-d8-carriers-cannot-recover-in-commuting-descendants` then gives a
fixed floor.  Arbitrary unrelated carriers remain insufficient—the point is
that these two carriers and their joint canonical moments are fixed in
advance by the packet.

Pure tracial-von-Neumann reasoning cannot prove this statement, because the
left regular representation sees the nontrivial marked word.  The proof must
use finite matrix coordinates: multiplicity, finite-label recovery, or an
equivalent microstate feature that is unavailable in an arbitrary finite
tracial representation.

## The exact `Phi`/`s4` specialization

The iterated self-similarity formula has now been isolated in
`iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart`:

```text
Phi_n(r)_(u,v)=t_u r s_v,       Phi_n(s_ut_v)=E_(u,v).  (PSR1)
```

Thus the dual-prefix pairing, common central sign, and all depth-one target
matrix units are already exact.  They do not supply same-reservoir closure:
`Phi_1` can exchange label dimension for spectator multiplicity.

For `p=2`, a sufficient first-step form of this claim is consequently very
small.  Recover one positive-density corner and one source factor
`B=M_2 tensor I_m` on it, and prove that the same four returned words

```text
(I tensor X,I tensor Z,X tensor I,Z tensor I)           (PSR2)
```

both satisfy the two-qubit Pauli table up to `epsilon` and lie within
`delta` of `B`.  Then
`four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap` gives

```text
144 epsilon+96 delta>=8.                                (PSR3)
```

This is the exact common-corner endpoint; no new polynomial calculation or
additional Leavitt pairing relation remains.  What is open is solely the
finite-matrix word theorem recovering that same corner/factor from the
mixed Steinberg returns.

There is now an even smaller sufficient attack on this finite-matrix word
theorem.  Once the source `M_2` and target `M_4` matrix-unit packets have
been exactified on one projection `P`, it is enough to recover one operator
from a coarse minimal corner to a fine minimal corner with nearly full source
Gram.  By `one-coarse-to-fine-prefix-isometry-closes-the-reservoir`,

```text
||e-X^*X||_2^2 >= tr(P)/4.                             (PSR4)
```

The exact infinite Leavitt model supplies this arrow as `s_(00)t_0`, and its
partial swap is a three-elementary word.  Thus the surviving compiler target
is one off-diagonal Gram authentication, not the entire mutual bicommutant or
all four `s_4` placement estimates.

### The required same-object return word already exists

Put

```text
x=s_(00)t_0,       y=s_0t_(00),
J_x=[[1-f,x],[y,1-e]],                                  (PSR5)
```

where `e=s_0t_0` is the coarse minimal prefix corner and
`f=s_(00)t_(00)` is its fine descendant.  By `(CFI9)`, `J_x` is the fixed
ordinary three-elementary group word

```text
[[1,x],[0,1]] [[1,0],[y,1]] [[1,x],[0,1]],              (PSR6)
```

and `J_x^2=1`.  More importantly, it is already the desired algebraic
same-object return.  If

```text
ehat=diag(0,e),       fhat=diag(f,0),
```

then direct block multiplication using `yx=e` and `xy=f` gives

```text
J_x ehat J_x^*=fhat,       J_x fhat J_x^*=ehat.          (PSR7)
```

Thus no new group word is needed to cross the net `2 -> 4` refinement: the
external stabilized selector and the identical internal prefix reservoir
are tied by `(PSR6)`.

There is also an exact quantitative reduction for microstates.  Suppose the
coarse and fine packet matrix units have been exactified on the same selected
corner, let `J` be the unitary assigned to `(PSR6)`, and put

```text
X=fhat J ehat,       epsilon_J=||J ehat J^*-fhat||_2.
```

Then

```text
ehat-X^*X
 =ehat J^*(J ehat J^*-fhat)J ehat,
||ehat-X^*X||_2 <=epsilon_J.                            (PSR8)
```

Combining `(PSR8)` with the coarse/fine rank gap `(PSR4)` yields the
dimension-free same-reservoir payment

```text
tr(P) <=4 epsilon_J^2.                                  (PSR9)
```

Consequently the remaining theorem is narrower than word discovery: prove
that the named presentation relators and canonical packet recovery control
the **selector covariance** `epsilon_J` for this one existing word, or charge
the failure to boundary mass.  The involution relation `J^2 ~=1` alone does
not imply `(PSR7)`—an arbitrary involution may preserve unrelated subspaces—
so the compiler must retain the conjugation action of `(PSR6)` on the two
recovered prefix packet corners.  This is the exact point at which ordinary
word defect must be connected to the matrix-coordinate selectors.

## Attempts

- **Whole-map extraction fails.**  Exact deterministic equivariant maps into
  `V direct_sum V` satisfy every four pairing identity while shrinking
  multiplicity; this is `rectangular-escape`.
- **The canonical stabilized Whitehead repair fails.**  The tempting repair
  is to Whitehead-compress `g` into the first child, conjugate by the branch
  swap to obtain the second child, and multiply.  This does exactly produce
  `diag(g,g)` in the `Phi_1` chart, but
  `whitehead-swap-copy-completion-retains-rectangular-escape` realizes the
  entire construction on `E direct sum (E direct sum E)`.  The full target
  two-qubit tuple then has `s_4` norm `8 sqrt(2/3)` while every Whitehead and
  swap identity is exact.  Stabilization has amplified the label rather than
  returned it to the source reservoir.
- **Equal ambient dimension fails.**  The larger target Weyl factor uses the
  same matrix dimension by consuming the source multiplicity, so a dimension
  count alone sees no loss.
- **Live attack.**  Use the mixed rank-five raw/comb words to identify one
  common returned carrier.  Either their holonomy is nontrivial and pays a
  relator defect, or the carrier lies near both transverse child algebras and
  `tensor-independent-child-carrier-gap` pays a fixed amount.  Extracting the
  word-defined **same** carrier, rather than two unrelated carriers with the
  same trace, is the deferred step.
