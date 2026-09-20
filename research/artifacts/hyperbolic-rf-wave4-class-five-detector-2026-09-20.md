# A finite detector for the canonical mod-seven central mark

20 September 2026. **This is a finite detector, not a counterexample to
hyperbolic residual finiteness.** It settles the selected mod-seven
central-class test in the direction of virtual splitting.

Let K=K7 and B=B_c0 be the exactly marked integral central extension,
with central generator z, described in
`hyperbolic-rf-wave4-class-two-2026-09-20.md`. There is an explicit
surjection

    f:B -> F,
    |F|=7^28, exponent(F)=7, nilpotency_class(F)=5,

such that f(z) has order seven. Moreover z belongs to gamma5(B) but
not gamma6(B). The reduction c0 mod7 vanishes on a normal subgroup
K0 of K of index 7^27. Therefore the finite central extension
B/<z^7> virtually splits; it is residually finite if and only if K is.

## The standalone finite witness

The complete multiplication data for a 28-dimensional F7 Lie algebra L
are in
`experiments/hrf-wave4-four-generator-2026-09-20/class_five_lie_witness.json`.
The file specifies all nonzero brackets of distinct basis elements,
the six vectors U0,V0,U1,V1,U2,V2, and a vector Z. Missing brackets
are zero; reversing the order negates a bracket.

The independent standard-library verifier
`experiments/hrf-wave4-four-generator-2026-09-20/verify_finite_witness.py`
does not run or import either quotient-construction algorithm. It checks:

- alternation and all 3276 distinct basis-triple Jacobi identities;
- lower-central dimensions 28,24,21,17,11,0;
- generation of the whole Lie algebra by the six specified vectors;
- the abelian H0 relations and the two Heisenberg vertex relations;
- that Z is central, nonzero, and belongs to gamma5(L);
- the six exactly marked face equations described below.

For j=0,1,2 and i in F7, set

    q_j(i)=i U_j-i^2 V_j/2+sigma_j i^3[U_j,V_j]/12,
    sigma=(0,-1,1).

The verifier checks

    BCH(BCH(q_0(i),q_1(i)),q_2(i))=-Z   for i=1,...,6.

It derives the degree-five BCH polynomial independently from the
two-letter associative exponential and logarithm. Its conversion into
nested Lie brackets is itself checked as a free associative polynomial
identity. Thus no stored BCH coefficient table or quotient rank is
trusted for these final equations.

The output receipt is `finite_witness_verification.json` beside the
witness. The root replayed the full checker successfully. All operations
are exact modulo seven; no numerical tolerance is used.

## From this certificate to a finite group homomorphism

The Lie algebra has class five, less than seven. The truncated BCH
operation therefore defines a group F on its underlying set, by the
Lazard correspondence. Its order is 7^28 and its exponent is seven.
The lower-central computation gives exact class five. The relevant
correspondence and tensor construction are stated in
Garaialde Ocaña--González-Sánchez,
[Section 2, Theorem 1](https://arxiv.org/pdf/1405.4654).

The vertex relations give homomorphisms from H0=C7^2 and the two
exponent-seven Heisenberg groups H1,H2 to F. Their corner words have
logs q_j(i), by the already checked vertex-weight identities. Assign
the marked central generator z to exp(Z). Centrality and all six
equations above are exactly the marked presentation of B, so these
assignments extend to a homomorphism f:B->F.

The vertex vectors generate L. Subgroups correspond to Lie subalgebras
under Lazard, hence their group images generate F. Thus f is onto.
Since Z is a nonzero vector over F7, exp(Z) has order exactly seven.

The independent class-four obstruction already proves z in gamma5(B).
If z belonged to gamma6(B), its image in the class-five group F would
be trivial. Therefore z is not in gamma6(B), proving the sharp position.

## Exact virtual splitting

Since f(z)^7=1, f descends to B7=B/<z^7>. Its restriction to the
central subgroup A=<z>=C7 of B7 is injective. Put U=ker(B7->F) and
K0=image(U->K). Then U intersects A trivially, so U maps isomorphically
onto K0 and supplies a section of the restricted central extension.

The subgroup K0 is the kernel of the induced surjection K->F/f(A).
It is normal and has index |F|/7=7^27. Thus c0 mod7 restricts to zero
on K0. The preimage of K0 in B7 is A x K0.

Residual finiteness is inherited by subgroups and by finite-index
overgroups. Consequently B7 is residually finite exactly when K0 is,
and K0 is residually finite exactly when K is. This particular central
extension cannot create a new residual-finiteness failure over an RF K.
No residual-finiteness assertion about K itself is made.

## Discovery and independent cross-checks

The six-generator tensor-Lie computation gave free dimension1960,
relation-ideal dimension1932, quotient dimension28, and a nonzero mark.
The independent filtered elimination of two generators gave free
dimension294, ideal dimension266, the same quotient dimension28,
and a nonzero mark. The elimination proof is in
`hyperbolic-rf-wave4-filtered-elimination-2026-09-20.md`.

The finite witness and its standalone verifier are stronger evidence for
existence of the detector than agreement of these two rank computations:
they directly verify a concrete finite algebra satisfying every required
relation and preserving the marked element. This is not a proof-assistant
formalization.

Both the matching lane and the separate audit lane independently read and
replayed the standalone verifier and returned PASS. They also reviewed
the marking and the exact virtual-splitting argument. Their checks do not
assume residual finiteness of K.

## What remains open

The detector gives central order seven, not unbounded central orders.
It does not settle reductions c0 mod ell for other primes, residual
finiteness of B or K, flexible Hilbert--Schmidt stability, or Problem141.
In particular, existence of this finite detector must not be recorded as
residual finiteness of the entire central extension.
