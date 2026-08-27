---
rg: 2
id: off-base-row-gradient-coercivity
kind: claim
title: The diffuse balanced residual is coercive under its normalized adjoint-gradient step
distinct_from:
  damped-adjoint-step-bypasses-code-riesz-at-exact-base: that proves contraction only for the Jacobian frozen at an exact code tuple; this asks for the intrinsic off-base estimate needed for basin capture.
  balanced-overlay-diffuse-square-function-newton: that permits Newton or alternating projection and previously requested a cb Riesz inverse; this is the narrower first-order descent statement after that inverse is bypassed.
---

OPEN.  Let `F(X)` collect the normalized involution, equality, balanced
parity, and complete-pair residuals for a selfadjoint contraction tuple, and
let `D_X` be its algebraic derivative.  On the retained aggregate-cut block,
prove constants `eta,c,C>0`, independent of length and matrix dimension,
such that

```text
 E(X-eta D_X^*F(X))
   <=(1-c)E(X)+C E(X)^(3/2)+C epsilon_inv,              (ORG1)
```

after quotienting the simultaneous-conjugation gauge.  Here `E` is the
balanced squared residual energy and `epsilon_inv` is the positive
involution forcing floor created by block compression.

The exact-base linear term is established by
`damped-adjoint-step-bypasses-code-riesz-at-exact-base`; the dense quadratic
remainder is established by
`dense-complete-pair-remainders-are-cb-quadratic`.  What remains is to prove
the same descent algebraically before a joint character decomposition is
known, while alternating the bounded local parity/equality corrections so
that their sparse terms do not leave the common row-column basin.

This formulation neither asks for an endpoint cb code-Riesz transform nor
tries to charge physical cut boundary.  The latter contains exact
simultaneous-conjugation motion and is correctly removed by the gauge.

## Attempts

The direct Taylor expansion at an unknown tuple does not inherit `(DAS1)`:
the proof of that gap uses the joint character blocks of an exact code
representation.  Freezing the Jacobian at a hypothetical nearby exact
tuple is circular, since finding that tuple is the basin-capture theorem.
The live attack is instead an SOS expansion of
`<F(X),D_XD_X^*F(X)>` using the complete-pair average, with the bounded
parity faces re-exactified between gradient steps.  The dense quadratic
part already has the required row-column bound; the sparse re-exactification
term is the unproved part of `(ORG1)`.

There is now a complete restricted bypass after local exactification **and**
literal sharing.  `parity-exact-shared-contractions-have-intrinsic-cp-gap`
first observes that an exact product of contractions forces every factor to
be unitary, so the involution forcing vanishes.  It then transfers the
established whole-face Hamiltonian gap to the intrinsic coordinate channel
`A_X=I-L^(-1)sum_iP_i`, yielding a finite-Green contraction before global
commutativity or characters.  What prevents applying it here is precisely
equality synchronization: normalized-HS-close occurrence reflections can
have adjoint actions distance two on a sparse corner.  Thus the remaining
pre-character nonlinear estimate may be replaced by an equality-compatible
local-exactification/sharing theorem, but neither exact oddness nor the
dense cb remainder alone transports the face gap across approximate
equality.

Even exact sharing is not by itself a nonlinear basin certificate.
`parity-exact-double-pauli-is-stationary-for-intrinsic-green-step` uses the
distance-`1/2` code `(a,a,b,b)` and the literally shared tuple `(A,A,B,B)`.
Both covered parity faces and all equality data are exact, but every
intrinsic divergence is the scalar `I/2`; hence every finite-Green skew
conjugator vanishes while complete-pair energy equals `2`.  This does not
contradict the pre-character CP gap, which is a channel/linearization result
at the commuting locus.  The packet has anchor square function `I/2` and is
removed by the aggregate cut.  Therefore the still-valid target must use
the retained low-anchor-square-function hypothesis quantitatively in
addition to local exactification and sharing.

There is a positive equality-transfer theorem at the averaged-channel
level.  `row-square-equality-variance-transfers-averaged-pinching-gap` takes
the actual unequal occurrence weights, forms their shared contractions and
signs, and proves that weighted Loewner variance `<=epsilon I` changes the
whole averaged pinching channel by at most `sqrt(2epsilon)` in
`L_2->L_2` norm.  Thus the face Hamiltonian gap survives outside a low
spectral band of that width.  Exact commutant coercivity need not survive:
old zero modes may split into the low band.  The remaining operation can
therefore be narrowed to resetting/gauging this equality-created low band,
not controlling every occurrence adjoint action separately.

Even exact sharing is not by itself a nonlinear basin certificate.
`parity-exact-double-pauli-is-stationary-for-intrinsic-green-step` uses the
distance-`1/2` code `(a,a,b,b)` and the literally shared tuple `(A,A,B,B)`.
Both covered parity faces and all equality data are exact, but every
intrinsic divergence is the scalar `I/2`; hence every finite-Green skew
conjugator vanishes while complete-pair energy equals `2`.  This does not
contradict the pre-character CP gap, which is a channel/linearization result
at the commuting locus.  The packet has anchor square function `I/2` and is
removed by the aggregate cut.  Therefore the still-valid target must use
the retained low-anchor-square-function hypothesis quantitatively in
addition to local exactification and sharing; those latter hypotheses alone
do not imply `(ORG1)`.

The averaged equality channel is nevertheless stable on the common low
square-function block.
`averaged-pinching-channels-are-row-square-lipschitz` gives
`||A_Q^K-A_S^K||_(2->2)<=K sqrt(||H||_infinity)` for shared and locally
exact occurrence channels.  Thus the exact face-Hamiltonian gap transfers
at fixed time without individual adjoint-action stability or literal
sharing.  The remaining part of `(ORG1)` is the sparse parity/equality
energy created by the coordinate-dependent intrinsic conjugators, together
with the high equality sector assigned to quarantine.

That sparse part is now closed.
`fixed-parity-faces-exactify-with-loewner-row-square-control` gives an
explicit sequential pinch/sign/parity construction whose correction square
is Loewner-dominated by a fixed symmetrization of the raw local residual
square.  `sparse-face-row-square-survives-intrinsic-green-step` applies it
after a damped intrinsic step and pays only `O(sigma^2 b)`.  Normalized
equality transfer preserves the face gap, while
`shared-pinching-low-band-is-gauge-or-cheap` leaves the low band as a
vanishing energy floor rather than making a nonphysical cut.  Therefore the
sole remaining term in `(ORG1)` is the first-order dense low-sector
curl/coercivity inequality.  All sparse, equality, involution, and endpoint
cb terms have dimension-free ledgers.
