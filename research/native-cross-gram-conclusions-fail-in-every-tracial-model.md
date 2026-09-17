---
rg: 2
id: native-cross-gram-conclusions-fail-in-every-tracial-model
kind: claim
title: The native cross-Gram gauge-lock conclusion is false in every exact tracial model, so the cross-Gram premises are only vacuously provable
artifacts:
  - research/native-cross-gram-tracial-inconsistency-proof.md
distinct_from:
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that refutes one fixed exact Hecke carrier row in the canonical trace; this refutes the full representation-dependent CAP/EAP1/APG1 conclusion (arbitrary spectral cut, arbitrary polar gauge) in every finite von Neumann algebra, and transfers the refutation to every approximate model by the tracial ultraproduct.
  fixed-packet-julia-calculus-is-tracially-functorial: that shows one construction calculus is valid in regular finite algebras; this shows that the conclusion of the three native cross-Gram premises is itself contradictory there, independently of how it would be constructed.
  universal-canonical-trace-promotion-is-goal-equivalent: that audits an existential von Neumann promotion against nonhyperlinearity; this audits the MF cross-Gram premise of the EL20 no-Property-(T) route against the EL20 endpoint.
  binary-leavitt-el20-canonical-opnorm-native-cross-gram: that is the open CAP1 premise asserting overlap plus gauge lock on canonical microstates; this proves the conclusion fails on every model that exists, so the premise is equivalent to the EL20 endpoint and has no nonvacuous instance.
---

**ESTABLISHED DICHOTOMY (written proof; not Lean-verified).**  Either the
recorded compiler assembly of
`el20-canonical-opnorm-cross-gram-gives-full-mf-radical` /
`arbitrary-profile-cross-gram-implies-shared-gauge-compiler` has a step that
is not valid in finite von Neumann algebras, in which case those routes are
unsound as written, since their three lemmas are dimension-free.  Or items
1--3 below hold.  In both cases the native cross-Gram decomposition of the
EL20 no-Property-`(T)` endpoint is dead as a decomposition.

Let `Delta` be
`EL_20(R)` or `St_20(R)`, with `R=L_(F_2)(1,2)`, and let `z=x_13(s_1t_1)`
(`e_13(s_1t_1)` in `EL_20`).  Call the following conjunction, for an
**exact** homomorphism `pi : Delta -> U(N)` into a finite von Neumann algebra
`(N,tau)`, the exact native cross-Gram conclusion `(XCG)`:

- the actual native transports `S_1,S_2` (rows `1/2 -> 1/4`, `1/4 -> 1/8`,
  built from `pi(Delta)` and exact packet projections) satisfy
  `tau(S_1^*S_2S_2^*S_1) >= gamma tau(P_source) > 0`;
- on the resulting overlap corner the two mixed source-Pauli commutators of
  the relative polar gauge vanish.

Then:

1. **Tracial inconsistency.**  `(XCG)` holds for no exact `pi` into any
   finite von Neumann algebra.  In particular it fails for the left regular
   representation `lambda : Delta -> U(L(Delta))`, whose trace is `delta_e`,
   whose finite packets carry Plancherel multiplicities exactly, in which
   every relator defect is zero, and in which `z` has negative carrier of
   trace exactly `1/2`.
2. **Approximate models.**  If `W_n` is any sequence of operator-norm or
   merely normalized-HS asymptotic representations (of any profile) along
   which the approximate conclusion of `(CAP1)`,
   `(EAP1)` or `(APG1)` holds, then `(XCG)` holds for the ultraproduct
   representation in the tracial ultraproduct.  Hence the approximate
   conclusion fails along **every** sequence of models that exists.
3. **Circularity.**  Consequently each of
   `binary-leavitt-el20-canonical-opnorm-native-cross-gram`,
   `binary-leavitt-el20-arbitrary-profile-native-cross-gram` and
   `binary-leavitt-arbitrary-profile-native-cross-gram` is equivalent to the
   nonexistence of the models it quantifies over, that is, to its own MF
   endpoint.  None has a nonvacuous instance.

The proof uses only the three recorded dimension-free lemmas
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner`,
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge` and
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction`, all read
in a finite von Neumann algebra, together with the tracial ultraproduct.

## Obstruction (class killed)

The class is every direct proof of a native cross-Gram premise, meaning a
proof that establishes the overlap mass and the gauge lock on a model rather
than proving that no model exists.  This includes canonical Hecke moments
such as `tau(e_chi)=1/64`, fixed-packet exactification, commutant Poincare
gaps and normalized-HS defect estimates.

- **Invariant.**  The tracial ultraproduct `N_omega` and the regular
  algebra `L(Delta)`.  An exact representation there satisfies every
  hypothesis these methods consume.
- **Step where every member dies.**  The gauge-lock clause.  With exact rows
  (`delta_1=delta_2=0`), `(TSG6)` forces the gauge discrepancy
  `epsilon_g>=2/3` on any positive-mass common carrier.  So whenever the
  overlap mass is positive the lock is false, and in every model the
  conjunction is false.

Any correct proof of the EL20 no-Property-`(T)` endpoint must therefore
exclude the models outright, and the cross-Gram compiler is logically idle.
The only input that separates operator-norm microstates from `L(Delta)` is
not tracial, for example operator-norm integrality or quasidiagonality of the
trace.
