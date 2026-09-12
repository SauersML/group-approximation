---
rg: 2
id: quantum-pcp-constant-gap-local-hamiltonian
kind: claim
root: true
title: Constant-locality local Hamiltonian is QMA-hard at a constant relative promise gap
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
distinct_from:
  classical-pcp-gap-is-not-tracial-pvm-gap: that is a no-go about transporting classical PCP soundness onto contextual tracial PVM assignments inside this repository's microstate program; this is the external complexity-theoretic conjecture about tensor-site local Hamiltonians, with a fixed finite-dimensional Hilbert space and a state-weighted energy.
  binary-pcp-coordinate-atlas-in-hs-microstates: that compiles a classical constant-query PCP into group words with normalized-HS energy; this is a statement about quantum local Hamiltonians and makes no reference to group approximation.
---

There exist a constant `k` and a constant local dimension such that, for
explicitly described `k`-local Hamiltonians on `n` qudits with polynomially
many terms and polynomial-bit descriptions,

```text
H = (1/m) sum_(a=1)^m h_a,        0 <= h_a <= I,               (QPCP1)
```

it is QMA-hard to distinguish

```text
lambda_min(H) <= a     from     lambda_min(H) >= b,            (QPCP2)
```

where `b - a >= Omega(1)` is independent of `n` and `m`.

This is the standard constant-locality form of the quantum PCP conjecture.
It is open; Bafna--Vyas (ECCC TR26-150, 19 August 2026) open with "The
quantum analogue of the PCP theorem for QMA remains wide open".  No node in
this region asserts otherwise.

The region below records one specific attack: obtain a **combinatorial** gap
from a locality-preserving amplifier, and convert it into an ordinary energy
gap by exactifying soft violations into commuting local fault syndromes at
linear cost.  The conversion step is
`combinatorial-gap-and-rounder-give-energy-gap`. Its converse concerns the
NO-side energy floor, under a positive constant combinatorial-gap
hypothesis; it is not an equivalence to the full QMA-hardness claim.
The amplifier, YES-side energy bound, local syndrome ports, and conditional
exactifier remain separate open obligations.

**2026-09-07 audit.** The exact family
`qubit-pairs-have-half-gap-and-unbounded-rounder-cost` rules out an inference
from combinatorial gap alone even for norm-one, bounded-occurrence qubit
projectors. `nonorthogonal-pair-forbids-single-term-syndrome-ports` also
rules out singleton energy neighborhoods for that family's exact flags.
These are limitations on proof routes, not a disproof of this conjecture.
The source check in the linked artifact continues to find the conjecture
open; the polynomial-time constant-gap hardness reduction is not supplied.

The continued audit characterizes exact recovery by vanishing joint effects
on infeasible fault sets. The same marginal energy bounds can coexist with
different joint outcomes and opposite recovery verdicts. Thus the remaining
construction must control one joint measurement, including its physical
realization, rather than only its individual flag probabilities.

The finite primal/dual test now supplies exact certificates for local
syndrome proposals. In the paired-projector example the enlarged
neighborhood's optimal local constant is `(N^2+1)/4`, proved by matching
certificates, so it still diverges. The rounder route now explicitly
requires `amplifier-has-compatible-local-syndrome-effects`. That uniform
construction, its physical realization, and the completeness-preserving
constant-locality, constant-dimension amplifier remain open.

The kernel-resolution continuation gives a separate sufficient route:
feasible input supports must resolve `I`, and local neighborhood operators
must have uniformly bounded nonzero spectra. A fixed finite term collection
with bounded neighborhood size supplies the spectral part only. The
resolution is not implied by spanning or generic normalization. No such
uniform resolution and complete amplifier are constructed here.

The fixed-term spin-chain audit further excludes an unconditional inference
from local spectra and a finite collection of term matrices to such a
resolution. For that family, a finite-cost construction requires
`R(L+1)^4 >= (n-1)/16`. The family has vanishing combinatorial gap and
does not refute the amplified constant-gap construction. No full QPCP
proof is claimed by this obstruction.

**2026-09-11 positive shift audit.** Replacing every term by
`(1-epsilon)h_a+epsilon I` keeps locality, local dimension and descriptions,
and scales the promise gap by `1-epsilon`. It also makes exact combinatorial
soundness, bare rounder cost and trivial syndrome ports vacuous
(`positive-shift-trivializes-exact-combinatorial-soundness`). Applied to the
standard inverse-polynomial reduction, it satisfies every requirement of the
anchored route except the YES margin, and a shifted root witness satisfies the
whole criterion (`anchored-criterion-components-are-shift-satisfiable`). So
`qpcp-from-anchored-amplifier` reduces this claim to
`amplifier-preserves-yes-energy-below-the-floor`, which is equivalent to it;
the route `yes-margin-criterion-from-quantum-pcp` records the converse. The
same theorem shows that robust combinatorial soundness with a positive
tolerance is energy soundness up to constants. An amplifier must therefore
deliver energy or robust soundness, or keep frustration-free YES outputs.
The latter, for a QMA-hardness reduction with exactly implementable term
measurements, also places QMA inside QMA_1, which Aaronson's quantum oracle
(arXiv:0806.0450) rules out for quantumly relativizing proofs.

## Attempts

- **Ordinary energy gap amplification.**  Killed for this target by
  `ordinary-gap-amplification-grows-locality`: the detectability-lemma
  amplification of Aharonov--Arad--Landau--Vazirani buys gap by enlarging the
  support of the terms, and the constant-locality promise here is exactly
  what that spends.
- **Circuit-to-Hamiltonian plus fault tolerance, used directly.**  Killed by
  `abn-energy-to-fault-loss-is-exponential-in-depth`: the Anshu--Breuckmann--Nguyen
  adversarial-noise semantics holds at energy density exponentially small in
  the circuit depth, and even the combinatorial-state version is only
  polynomially small.  Neither reaches a constant density.
- **Adversarial fault tolerance alone.**  Killed by
  `whole-time-slice-corruption-costs-inverse-depth`: on a depth-`D` circuit
  Hamiltonian a whole time layer is only a `Theta(1/D)` fraction of the
  terms, so a constant-density adversary can erase one outright, and no
  per-timestep guarantee tolerating `o(N)` corruptions survives that.
- **Bare rounder existence.**  Not an attack at all: by the converse half of
  `combinatorial-gap-and-rounder-give-energy-gap`, a uniform constant-cost
  rounder on a positive-combinatorial-gap family is equivalent to its
  uniform NO-side energy floor. Proving that bound and a complete hardness
  reduction is still required.
- **Exact combinatorial soundness plus syndrome technology, without a YES
  margin.** Vacuous: the shifted standard reduction meets (LPC1), a
  constant rounder, compatible local ports, the exactifier, the uniform kernel
  resolution, and the anchor and recursion inequalities, while its YES margin
  is inverse polynomial (`anchored-criterion-components-are-shift-satisfiable`).
  (LPC1) as written is now established by `lpc1-from-shifted-kitaev-reduction`.
  That records the vacuity; it is not progress toward this claim.
