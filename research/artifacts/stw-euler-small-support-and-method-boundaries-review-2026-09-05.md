# Review of the persistent Euler invariant and distinct remaining attacks

Date: 5 September 2026. Internal review and integration record.
No external mathematical verification or publication priority is claimed.

## New results

The root computed the degree-one stabilization cokernel of the simple
AH towers. Their integral Euler maps survive the actual connecting
homomorphisms, including the point-evaluation block. A list of orders
d_1,...,d_s>=1 produces component group direct sum Z/d_alpha and
degree-one cokernel Z^s. Order-one arms independently enlarge the free
cokernel. The resulting K1-bijective examples still have stable rank
two and fail rational K-stability; all matrix sizes at least two are
K-stable. Pascal checked Euler persistence and the limit exact sequence.
Ohm separately checked the order-one construction and its structural
properties, including the degree-one surjectivity consequence of
stable rank one used for the lower stable-rank bound.

Ohm proved contraction of any stably null family whose uniform
quasitrace support dimension is strictly below 1/(dim(X)+1), over a
compact finite-dimensional metric base and simple unital finite pure
coefficients with normalized quasitraces. A small constant positive
element makes the support full; after cutoff, functional calculus
constructs an actual orthogonal reservoir. The root checked this
argument and its essential small-trace UHF support example. Fullness
and a reservoir for the original support are no longer assumptions.
Global localization or fragmentation of arbitrary families remains open.

Pascal proved that four explicit coefficient rotations obstruct one
common fixed-representation threshold path with all compressed paths
norm continuous in the Calkin algebra. Polarization reconstructs the
whole operator class, contradicting the endpoint projection path.
The root checked the exact matrices, compression formulas, and compact
defect calculation. This blocks the stated uniform Fredholm-path
method, not the unrestricted commutator theorem or W-dependent paths.

Aquinas proved exact relative projection-source extension without
real rank zero, conditional on stable rank one and K-stability of
every nonzero hereditary coefficient algebra. The root checked the
unitary orbit, full hereditary stabilizer, local sections, and
Michael-selection hypotheses. Aquinas also gave an explicit CAR
example where exact positive-cutoff restriction is not onto. The
diagonal expectation forces two incompatible limits of a would-be
lift. The root checked the source and target module formula and the
two phase sequences. This counterexample does not exclude approximate
lifting or invalidate the reviewed RR0 projection-tower construction.

## Scope and remaining work

These are five established statements: a new AH realization/cokernel
theorem, a stronger supported-kernel contraction theorem, a conditional
projection-extension theorem, and two precise method obstructions.
They do not constitute five additional solved named problems.

The named-problem count remains one internally reviewed full-solution
manuscript for LIX. General LVIII, LXI, and LXXVI remain open. The
previous full RR0 simple finite pure coefficient-field Cu regularity
theorem remains intact; the new extension attack concerns coefficients
beyond real rank zero.

## Repository checks

The Euler/calkin batch passed staged whitespace checks and native
Cairn `check --changed` and `preview` on MSI, with 49 claims and
46 routes in its dependency closure. It was committed and pushed as
`1f7545d37`. These checks validate research-graph integration, not
the mathematical proofs themselves.

The final hereditary batch passed staged whitespace checks and both
native Cairn commands on MSI, with 52 claims and 49 routes (101
nodes) in its dependency closure. All five new statements are
established as scoped claims; the general open roots remain open.
No local code execution or builds were used. Remote checks used the
existing warm environment and shared project storage and terminated
normally, with no remaining job from either batch.
