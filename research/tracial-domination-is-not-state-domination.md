---
rg: 2
id: tracial-domination-is-not-state-domination
kind: claim
title: A trace-weighted domination gives no state-weighted domination, and the repair costs the dimension
invalidates:
  - syndrome-domination-by-tracial-outlier-cut-import
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
distinct_from:
  classical-pcp-gap-is-not-tracial-pvm-gap: that is a statement about classical unsatisfiability versus tracial forbidden mass on a BCS; this is the elementary geometric fence separating the normalized-trace GNS quadratic form from a state-weighted operator inequality, and it names no constraint system.
  balanced-overlay-common-reducing-outlier-cut: that is a positive tracial theorem producing a common reducing cut for high square-function outliers; this records what that theorem does not deliver after transport into the tensor-product geometry of an arbitrary witness state.
---

**ESTABLISHED.**  Every gap theorem in this corpus -- for instance
`gapped-face-pinchings-give-same-hilbert-code-pvm-rounding` and
`balanced-overlay-common-reducing-outlier-cut` -- is an inequality of
quadratic forms on `L^2(M, tau)`, the GNS space of the **normalized trace**.
The domination (SD) required by
`commuting-syndrome-domination-gives-a-rounder` is an inequality in the
state-weighted tensor-product geometry, and on a QMA instance the state is an
arbitrary, typically pure, witness.

**(i) No transfer.**  For `d >= 2` and `psi = e_1` put

```text
A = |psi><psi|,     B = ( I - |psi><psi| )/(d-1).               (TDS1)
```

Then `tau(A) = tau(B) = 1/d`, so `A` is trace-dominated by `B` with constant
`1`, while for `rho = |psi><psi|`

```text
Tr(A rho) = 1,      Tr(B rho) = 0.                              (TDS2)
```

Hence there is **no** constant `c` with `Tr(A rho) <= c Tr(B rho)` for all
states, and a fortiori `A <= cB` fails for every `c`.

**(ii) The only general repair is dimensional.**  For `A >= 0` and any state
`rho`,

```text
Tr(A rho) <= ||rho||_inf Tr(A) = ||rho||_inf * d * tau(A),      (TDS3)
```

and the factor `||rho||_inf * d` equals `1` exactly at `rho = I/d` and equals
`d = 2^n` at a pure witness on `n` qubits.  That factor is a modular /
Radon--Nikodym condition number, and it is exponential precisely in the
regime the local Hamiltonian problem lives in.

**Consequence for the attack.**  An (SD)-type inequality must be proved in
the state-weighted geometry directly.  Importing a tracial outlier cut or a
tracial pinching gap yields, at best, (TDS3), which is useless at
`C = O(1)`.  This is a fence on one identification of geometries, not a
claim that no relation exists: a hypothesis bounding the witness's
Radon--Nikodym derivative against `tau` on the relevant subalgebra would
reopen the import, and no such hypothesis is available for an arbitrary QMA
witness.
