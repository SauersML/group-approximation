---
rg: 2
id: coherent-shear-is-combinatorially-invisible
kind: claim
title: A coherent frame shear costs inverse-depth energy but cannot be exactified faithfully at constant cost
invalidates:
  - qpcp-rounder-from-combinatorial-soundness-alone
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
distinct_from:
  normalized-hs-taylor-remainder-is-not-dimension-free: that obstructs a normalized-HS Newton argument by exhibiting perturbations with tiny 2-norm and order-one operator norm on word maps; this is a tensor-site local Hamiltonian family on which exact fault count and soft energy are decoupled by a factor growing with the depth.
  classical-pcp-gap-is-not-tracial-pvm-gap: that separates classical unsatisfiability from tracial forbidden mass on a fixed BCS; this separates soft energy from exact fault count on an explicit 2-local qubit chain, with no BCS and no trace in the statement.
---

**ESTABLISHED.**  Fix `theta in (0, pi/2]`.  On qubits `0,...,D` put

```text
h_t = ( I - SWAP_(t,t+1) ) / 2,       t = 0,...,D-1,            (CSI1)
```

so `0 <= h_t <= I` and each `h_t` is `2`-local, and let

```text
rho_D = tensor_(t=0)^D |v_t><v_t|,
v_t = cos(t theta/D)|0> + sin(t theta/D)|1>.                    (CSI2)
```

**(i) The shear is cheap.**

```text
sum_(t=0)^(D-1) Tr(h_t rho_D) = (D/2) sin^2(theta/D) <= theta^2/(2D).  (CSI3)
```

**(ii) Exact satisfaction of every term forces exchangeability.**  If
`Tr(h_t sigma) = 0` for every `t`, then `sigma` is supported in the symmetric
subspace of all `D+1` qubits, hence invariant under permuting them, hence all
its single-qubit marginals coincide.  More generally, exactness off a set `S`
makes `sigma` exchangeable on each block of consecutive indices in the
complement of `S`.

**(iii) Endpoint-faithful exactification is not constant-cost.**  Call an
exactifier *endpoint-faithful* if the single-qubit marginals of `sigma_S` at
`t = 0` and `t = D` equal those of its input.  The endpoint marginals of
`rho_D` are at trace distance `2 sin theta > 0`, so by (ii) no endpoint-faithful
exactification of `rho_D` can have `S` empty.  Comparing `|S| >= 1` with
(CSI3), any endpoint-faithful rounder for this family has

```text
C >= 2D / theta^2  -->  infinity.                               (CSI4)
```

**What this fences.**  Soft energy and exact fault count are decoupled by a
factor growing with the depth as soon as the exactifier is required to
preserve constant-scale logical data.  A rounder therefore cannot be produced
by any argument whose only input is a conversion of energy into a count of
violated constraints: on this family the count is `1` and the energy is
`Theta(1/D)`, and a purely combinatorial assignment cannot perform the
infinitesimal rotation that a quantum state performs for free.  The
combinatorial gap of this family is `0`, so combinatorial soundness is
vacuous here -- which is precisely the point: it is not a hypothesis that any
exactification argument may quietly rely on.

Note also that dropping endpoint faithfulness makes the statement false and
uninteresting: the constant instrument of
`combinatorial-gap-and-rounder-give-energy-gap` is then a `0`-rounder.  The
faithfulness clause is where the quantum content sits.
