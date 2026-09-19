# Support-packet covariant Wedderburn detector

**Date:** 2026-08-20  
**Status:** Exact finite representation theorem proved; global one-sided
compressor placement remains open.  This is not yet a nonhyperlinear group.

## Result

For the order-128 support packet, the involution

```text
J <-> z_e,  z_f fixed,
p_1,p_2 fixed,
q_1 -> q_1 q_2, q_2 fixed
```

interchanges the four-dimensional simple types `011` and `101`.  The two
seven-dimensional coefficients

```text
V_+=3*trivial + T_011,
V_-=3*trivial + T_101
```

have identical diagonal-tensor commutant types on all three allowed
`J=-1` sectors.  On the forbidden sector their amplified commutants are

```text
M_(2m)^4 + M_(3m)       versus       M_m^16 + M_(3m).
```

Their Reynolds projections stay at squared normalized-HS distance at least
`1/49` under every underlying unitary conjugacy.

## Computation

`experiments/schur_packet_tensor_fusion_search.py` constructs all 38
irreducible characters directly from Pauli normal forms and verifies the full
order-128 character table.  It searched:

```text
779 coefficients with at most two irreducible summands,
9,880 coefficients with three summands,
101,270 coefficients with four summands,
850,668 coefficients with five summands.
```

No equal-capacity forbidden detector exists with at most three summands.  At
four summands there are 1,936 commutant-dimension detectors, and the stronger
complete-Wedderburn search finds the seven-dimensional pair above.  The run on
`acn112` used one process, 22.3 seconds and 79.9 MB maximum RSS.

The follow-up exact enumeration
`experiments/support_packet_wedderburn_tag_capacity.py` classifies all
`101270` four-summand coefficient multisets by coefficient dimension and the
complete Wedderburn signature on all twelve irreducible sources over the three
allowed `J=-1` central characters. It finds `905` allowed-equivalence classes:
`697` expose one forbidden signature and `208` expose two. The maximum is two,
so this ansatz has a sharp one-bit non-character tag capacity. The complete
machine-readable output is
`experiments/support_packet_wedderburn_tag_capacity_4.json`; rerunning the
script reproduced it exactly after deleting only the timing field.
`experiments/run_support_packet_capacity.sbatch` records the corresponding
single-core five-summand cluster run.  On MSI node `acn112` it exhausts all
`850668` five-summand coefficients in 239.0 seconds with 12.9 MB maximum RSS.
There are `3483` complete allowed-equivalence classes: `2578` have one
forbidden signature and `905` have two.  The maximum is again two.  The exact
machine-readable output is
`experiments/support_packet_wedderburn_tag_capacity_5.json`.

`experiments/schur_packet_wedderburn_holonomy_opt.py` independently builds the
two 25-dimensional Reynolds ranges inside `End(C^28)`.  With one BLAS thread,
the aligned overlap is exactly `17`; six Haar restarts and local hill climbing
found no larger value.  Runtime was 7.4 seconds and 36.8 MB.  The exact proof
uses the transportation bound, not this optimization.

## Remaining group problem

This replaces selector-dependent retraction by one fixed automorphism.  The
remaining construction should place isomorphic coefficient packets `K_0` and
`K_1=sK_0s^-1` across a one-sided Kazhdan compressor so that the boundary
coefficient is oriented as `V_+ -> V_-`, while scaled Kazhdan transport rules
out the reverse reservoir which finite Bass--Serre models use.  On a forbidden
external packet sector, the returned diagonal commutants then pay `1/49`; on
allowed sectors their Wedderburn types match exactly.
