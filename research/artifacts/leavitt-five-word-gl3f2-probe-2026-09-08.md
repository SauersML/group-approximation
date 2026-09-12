# Exact small-group check after authenticating the root order

2026-09-08. One completed, bounded exact enumeration on MSI acn112,
using the system Python 3.11 and no third-party packages or builds.
The implementation is `experiments/leavitt_packet_gl3f2_probe.py`;
the complete result is
`research/artifacts/leavitt-five-word-gl3f2-probe-2026-09-08.json`.

The four original coefficient words have an exact 24-dimensional
model, proved in `leavitt-four-word-packet-24-point-countermodel-2026-09-08.md`.
Its missing relation is `d^2=1`. The present check therefore tests
the augmented packet `r_*,R_v,R_0,R_sum,d^2`.

The code filters all 512 binary three-by-three matrices to obtain
the 168 elements of `GL_3(F_2)`, builds exact product and inverse
tables, and verifies the 56 elements of order three. For each such
cycle, it considers all ordered triples from each of the two groups

```text
<x_12(1),x_13(1)>,       <x_21(1),x_31(1)>.
```

Each group has four elements. Thus there are exactly
`56*2*4^3=7168` tested tuples. Identity entries in a triple are
allowed: if a solution had been found, adjoining independent
central `C_2^3` labels would embed the marked second factor and
preserve every tested word, because each has zero central label.

All 7168 tuples were evaluated, with no solution of the five rows.
Exactly 48 tested tuples passed the original four rows; each failed
the additional order-two relation.
The exact filtering, tables, and enumeration took about `0.1043`
seconds, within a five-second timer and ten-second outer timeout.
The requested class was exhausted; no restart or larger group
search was performed. This record claims only the stated finite
enumeration, without a classification argument for other models.
It supplies no normalized-HS lower bound for arbitrary unitaries.

The independent analytic argument in Section 5 of the 24-point
countermodel artifact also excludes `S_n` with abelian central
padding for `n<=5`: the augmented packet forces the commutator
`[b_3,c]` to have order four in the derived subgroup, whereas
`A_n` has no such element at these degrees.

Further finite-group enumeration is unnecessary for the different
nine-word set constructed in
`leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md`:
that packet already excludes every exact finite-dimensional
unitary model retaining the marked cycle. The open issue there
is quantitative control in unbounded dimension.
