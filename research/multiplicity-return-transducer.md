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
3. the group-word energy gap of
   `non-ce-bcs-has-robust-approximate-energy-gap` either already pays constant
   relator energy or forces a positive fraction of locally exactified packet
   copies to traverse rank-jump edges;
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
  `multiplicity-surplus-is-blind-to-the-non-ce-input`, a downstream theorem
  whose only BCS-dependent input is the scalar forbidden-mass constant also
  fires on a classically unsatisfiable CSP and is wrong.  The robust
  shared-word gap consumes the full noncommutative contextual tuple before
  local exactification; the return still must not forget that input.
- **Centrality is not the obstruction.**  Overlapping central context packets
  impose contextwise, not global, commutation: gluing `<x,y>` and `<y,z>` over
  `<y>` gives `C_2 x (C_2*C_2)`, with no relation `[x,z]=1`.  Ordinary
  Bass--Serre gluing nevertheless fails by the virtually-free/integer-flow
  argument above.
- **Reuse of the existing multiplicity infrastructure.**  The natural next step
  is to replace the generic finite-dimensional packet in
  `semisimple-packet-multiplicity-collapse` by these class-two two-groups, whose
  blocks, radical, restriction matrices and conditional expectations are all
  explicitly computable from
  `clifford-commutator-rank-is-packet-dimension`, and to feed the resulting
  multiplicity defect vector to `scaled-kazhdan-transport`, which is already
  proved for arbitrary weights.
- **Uniform three-XOR specialization.**
  `taller-vidick-uniform-rank-pressure-return` removes the arbitrary-predicate
  layer.  Taller--Vidick output three-variable parity equations, and each
  verifier rejection splits into one parity bit and one Alice--Bob consistency
  bit.  Both are affine and use the same two-pair packet.  No common classical
  assignment is assumed and no Fanizza tape-level selector renewal is needed.
  The remaining obstruction is still genuinely global: a tracially exact
  return must align the contextual endpoints and expose the one-versus-two
  finite packet-type count without complementary leakage.
- **Local exactification is discharged; simultaneous correction is bypassed.**
  `finite-schur-clifford-packet-flexible-hs-exactification` applies fixed
  word-table telescoping and Gowers--Hatami stability to each individual
  packet.  Its correcting isometry depends on the context, but
  `non-ce-bcs-has-robust-approximate-energy-gap` works on the original shared
  selector words and supplies ordinary relator energy or forbidden-product
  mass before correction.  Fixed-word telescoping transfers the latter
  locally.  The remaining return/payment interface is therefore only
  `fixed-scale-contextual-multiplicity-holonomy`.
