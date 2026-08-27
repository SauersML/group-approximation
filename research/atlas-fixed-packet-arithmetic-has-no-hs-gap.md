---
rg: 2
id: atlas-fixed-packet-arithmetic-has-no-hs-gap
kind: claim
title: Fixed A4 packet congruences and multiplicity lattices have no positive normalized HS gap
distinct_from:
  atlas-a4-context-types-live-in-fixed-rational-polytope: that classifies the unrestricted exact A4 type profiles; this proves that finite homogeneous congruence and divisibility refinements do not shrink their normalized closure.
  fixed-packet-hall-atlas-has-no-julia-cutoff-gap: that treats linear capacities and Hall matchings for a cutoff selector; this treats arbitrary finite-index multiplicity lattices and finitely generated affine semigroups before any particular inequality is chosen.
  fixed-depth-rank-mesh-has-zero-hs-density: that estimates one integral numerator through finitely many contractions; this gives the exact projectivized-semigroup closure and characterizes when any continuous profile cost can have a positive gap.
  semisimple-trace-charts-cannot-authenticate-proper-fullness: that classifies when one fixed semisimple projection has representation-independent trace; this removes finite congruence residues and treats the normalized closure of the whole packet-flow semigroup.
---

Let `P_A4` be the fixed rational multiplicity polytope of the exactified A4
atlas packet.  Add any finite family of homogeneous congruence or divisibility
conditions on the integral vertex, edge, or atom multiplicities.  Then these
conditions do not remove any normalized matrix profile after a suitable
common amplification.

Indeed the conditions define the kernel of a homomorphism from the integral
multiplicity lattice to a finite abelian group `F`.  If `r` is the exponent
of `F`, then every integral profile `x` has

```text
r x in ker(phi),             (r x)/dimension(r x)
                              =x/dimension(x).          (APA1)
```

Thus parity, determinant phase, fixed divisibility, and every other finite
multiplicity residue are exactly invisible on normalized profiles once
amplification is permitted.

More generally, let a fixed finite packet calculus allow finitely many atomic
integral type vectors `v_1,...,v_s` and all their direct sums.  For a positive
rational dimension functional `d`, the closure of its normalized profiles is

```text
closure { x/d(x) : x=sum_j n_j v_j, n_j in N }
 =conv { v_j/d(v_j) : 1<=j<=s }.                       (APA2)
```

The same conclusion holds for a rational polyhedral multiplicity cone by a
finite Hilbert basis.  Hence matrix profiles are dense in the corresponding
real tracial multiplicity simplex, including on every rational face.

Consequently, if a fixed normalized-HS cost is a continuous function of this
finite multiplicity profile, a positive lower bound on all exact matrix
profiles extends to the whole real tracial simplex.  Such a bound is not a
matrix-only arithmetic effect.  It comes from the real compatible profile
set already missing the proposed zero locus--an exact representation-type
incompatibility.  If the real zero locus meets the compatible simplex, matrix
profiles approach it and the infimum normalized cost is zero.

There is a precise nonlinear boundary.  A minimal-degree natural nonlinear
example for a finite group representation

```text
V=directSum_i S_i tensor C^(m_i),
```

the first natural amplification-invariant nonlinear rank statistic is the
normalized rank of the Reynolds projection on `End(V)`:

```text
q_H(V)=dim End_H(V)/(dim V)^2
      =sum_i m_i^2/(sum_i dim(S_i)m_i)^2.              (APA3)
```

It is quadratic and survives `m->k m`, unlike a bounded residue.  But in
normalized type coordinates `p_i=dim(S_i)m_i/dim(V)`,

```text
q_H(V)=sum_i (p_i/dim(S_i))^2,                         (APA4)
```

so it is a continuous function on the same real simplex.  It can witness a
positive gap only when packet types or Reynolds ranges are already
incompatible over the real profile geometry; it cannot rescue congruence or
divisibility alone.

Applied to the radius-nine A4 branch, no fixed system of integer ranks,
parities, determinant residues, or bounded packet multiplicities supplies
the missing matrix-only separator.  A surviving rank mechanism must leave
the fixed projective multiplicity simplex--for example through a
dimension-activated family or a global nonlinear coupling not determined by
the finite packet type vector.
