---
rg: 2
id: multiplicity-return-transducer
kind: claim
title: A finite presentation returning the Schur-Clifford multiplicity wire at fixed packet scale
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  semisimple-packet-multiplicity-collapse: that asks whether a Kazhdan compressor forces a packet's multiplicity vector to change, for a general finite-dimensional packet; this fixes the packets to be the explicit class-two two-groups of the rank compiler and asks for a transport network that returns them at a fixed irreducible size.
  atlas-fractional-pauli-return-network: that asks for a weighted return network whose reproduction number exceeds one, in the Pauli branching lane; this asks for a return that compares multiplicity at a fixed packet scale, and its surplus is manufactured by a Boolean predicate rather than by branching.
  extensive-cosystolic-index-defect: that asks a presentation to turn marked separation into positive-density local syndromes paying relator energy; this already has the extensive defect and asks only for the transport that makes it visible.
---

Construct a finitely presented group `Gamma`, a marked word `w`, finitely many
Schur--Clifford context packets `A_(f_c) <= B_(f_c)` for the violation
predicates of a fixed BCS `B` with a tracial but no Connes-embeddable tracial
state, and a finite recurrent transport network, with the following property.

For every sufficiently accurate finite-dimensional normalized-HS microstate `U`
of `Gamma` in which `w` stays `alpha`-separated from the identity:

1. a fixed positive fraction of the marked spectral carrier exactifies into the
   baseline spin packet types;
2. the packet multiplicity vectors transport around the finite network with
   total transport defect at most `C E(U)`;
3. the forbidden-mass gap of `non-ce-bcs-has-finite-dimensional-forbidden-mass-gap`
   forces a positive fraction of transported packet copies to traverse
   rank-jump edges;
4. after one return cycle those jumps create a multiplicity surplus of at least
   `eta d` **on a packet of fixed matrix size**;
5. the return relation identifies source and target packet types, so at least
   `c eta d` Hilbert dimension must lie in the transport defect.

Then `E(U) >= eps_0(alpha) > 0` and `Gamma` is not hyperlinear.

**Why clause 4 carries the whole difficulty.**  By `(PRM1)` Hilbert dimension
is conserved when a predicate is violated: the violating simple is twice as
large and there are half as many of them.  A finite-dimensional approximator can
therefore absorb any *absolute* divisibility requirement by increasing
dimension.  Only once the packet irreducible dimension is uniformly bounded does
an extensive multiplicity mismatch become an extensive Hilbert-space mismatch,
which is what normalized Hilbert--Schmidt norm can see.

## Attempts

- **Bass--Serre gluing.  Dead, and for two independent reasons.**  A finite
  graph of finite groups has virtually free fundamental group, hence is
  residually finite and hyperlinear, and
  `finite-graph-of-groups-representation-types-are-integer-flows` gives the
  representation-theoretic form: the dimension vector is a positive stationary
  solution of the edge restriction equations, so an apparent supercritical
  component must leak into complementary types.
- **Mandatory falsification test.**  By
  `multiplicity-surplus-is-blind-to-the-non-ce-input`, every downstream step
  after the forbidden-mass bound is a function of the constant `beta` alone, and
  a classically unsatisfiable CSP supplies such a constant with no
  non-embeddability input at all.  So any candidate argument must be run on a
  classically unsatisfiable CSP and must be seen to fail there.  A candidate
  that survives that test is using the non-CE hypothesis somewhere; one that
  does not is wrong.
- **The centrality obstruction, which bites immediately.**  The class-two packet
  declares its selectors central, and a selector central in both factors of an
  amalgam is central in the amalgam.  So the naive gluing over shared selectors
  makes the BCS variables globally commuting and collapses the system to the
  classical CSP above.  The transducer must glue the packets by something that
  does not centralize the selectors -- a two-dimensional holonomy relation, a
  compressor or self-similar action, or a nonamenable edge with quantitative HS
  rigidity.
- **Reuse of the existing multiplicity infrastructure.**  The natural next step
  is to replace the generic finite-dimensional packet in
  `semisimple-packet-multiplicity-collapse` by these class-two two-groups, whose
  blocks, radical, restriction matrices and conditional expectations are all
  explicitly computable from
  `clifford-commutator-rank-is-packet-dimension`, and to feed the resulting
  multiplicity defect vector to `scaled-kazhdan-transport`, which is already
  proved for arbitrary weights.
- **Not attempted: exactification.**  Clause 1 assumes the finite packet can be
  exactified inside a microstate while retaining the shared selector words up to
  controlled HS error.  Nothing in this repository supplies that for these
  packets.
