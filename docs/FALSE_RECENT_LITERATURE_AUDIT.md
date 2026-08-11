# FALSE-side audit of the recent approximation literature

Date: 2026-08-10

## 1. Executive conclusion

None of the papers in the current reading list proves that a hyperlinear
nonsofic group exists.  They nevertheless isolate the two most credible
FALSE-side routes:

1. build an operator-norm MF model of the cyclic-shear finite central
   extension, and then use a finite-normal-subgroup norm-to-trace theorem;
2. produce a co-hyperlinear, non-co-sofic **normal Dirac** invariant random
   subgroup.

The first route is currently blocked by a projective-sector extension
problem.  The second is exactly the original hyperlinear-versus-sofic problem
in IRS language; the known non-co-sofic IRS examples are not normal Dirac
masses.

## 2. Bachner--Dogon--Lubotzky: powerful but conditional in the needed place

Bachner--Dogon--Lubotzky, *On L1-approximation of groups*,
[arXiv:2508.17392](https://arxiv.org/abs/2508.17392), Proposition 1.6, proves
the following implication:

`F finite normal in E`, `E/F hyperlinear`, `E MF`  implies  `E hyperlinear`.

This is an excellent norm-to-trace converter.  It does **not** prove that a
finite central extension of an MF group is MF.

For the cyclic-shear candidate

`1 -> <z> ~= C_2 -> J -> K -> 1`,

the quotient `K` has a regular MF realization.  Applying Proposition 1.6
would still require both:

* an operator-norm MF model of the total group `J`; and
* hyperlinearity of `K`.

The first item is precisely the projective-sector gate `(PSC4)` in
`FALSE_FINITE_KERNEL_AUDIT.md`.  The second is not obtained from a regular
operator-norm MF realization: canonical trace moments do not by themselves
give normalized-Hilbert--Schmidt multiplicativity for the same matrices.

Thus the BDL theorem is a converter after the hard extension data has been
built, not an MF permanence theorem for finite kernels.

## 3. Manzoor: the exact reformulation, not the missing counterexample

Manzoor, *There Is An Equivalence Relation Whose von Neumann Algebra Is Not
Connes Embeddable*,
[arXiv:2502.06697](https://arxiv.org/abs/2502.06697), identifies the gap
between

`closure(T_IRS(F) intersect T_fd(F))`

and

`T_IRS(F) intersect closure(T_fd(F))`.

For `Gamma=F/N` with `N` normal, the normal Dirac trace `1_N` belongs to the
first set exactly when `Gamma` is sofic, and to the second exactly when
`Gamma` is hyperlinear.  Therefore a normal Dirac point in the difference
would solve the FALSE direction immediately.

The constructed non-co-hyperlinear IRS does not supply such a point, and the
known non-co-sofic IRS constructions are not shown to be normal Dirac.  Taking
normal cores destroys the information in the currently available examples.
So Manzoor provides the cleanest global language for the target, but no
shortcut to it.

## 4. Stability and cyclic-shift papers: what they do and do not propagate

Eckhardt,
[*Residually finite amenable groups that are not Hilbert--Schmidt stable*](https://arxiv.org/abs/2501.07791),
shows that operator-norm almost representations cannot in general be
Hilbert--Schmidt-corrected to honest representations.  This rules out a
structure-free MF-to-HS-stability argument.  It supports the need for the
specific central, Kazhdan, Clifford, or shear structure used in our
candidates, but it is not evidence of a hyperlinear nonsofic group by itself.

Lubotzky--Salomon,
[*Z^2 is flexibly stable in the operator norm*](https://arxiv.org/abs/2607.17578),
develop clock/shift and dimension-enlargement methods.  Those methods can
absorb an operator-norm obstruction into `o(d)` extra dimensions.  Our
FALSE-side need is the opposite: force a norm-visible sector to occupy
`Omega(d)` dimensions.  The paper is therefore technically relevant to the
cyclic shear, but does not provide the required rank amplification.

Paddock's maximally-entangled rounding theorem and the
Bowen--Chapman--Lubotzky--Vidick subgroup-test framework operate upstream of
the decisive conversion.  They produce or test tracial/IRS data; they do not
turn an arbitrary tracial unitary model into permutations while preserving
normal-Dirac fixed-point traces.

## 5. A newly isolated strong-trace gate

The exact Mackey construction in `FALSE_MACKEY_SECTOR.md` uses

`G = H * Z`

and two representations of `G` whose restrictions to the cyclic edge are
the trivial and parity sectors.  Let `A_Mac` be the C-star algebra generated
by the resulting exact shear representation.

**Proposition (necessary reduced-vertex gate).**  If `A_Mac` is MF, then
`C*_r(G)` is MF.

**Proof.**  The two Mackey vertex representations are faithful on
`C*_r(G)` in the present construction (the free product `G` is C-star simple,
and the relevant weakly regular representations have the canonical trace).
Hence `A_Mac` contains a C-star subalgebra isomorphic to `C*_r(G)`.  The MF
property passes to C-star subalgebras.  End proof.

This proposition exposes a tempting but invalid shortcut.  A **regular MF
realization** of `H` only supplies:

* operator-norm asymptotic multiplicativity; and
* convergence of normalized traces on group elements.

It does not supply convergence of matrix norms of all noncommutative
polynomials to the reduced C-star norms.  Existing strong-asymptotic-freeness
arguments for adjoining a free Haar unitary require this stronger norm
control.  Existing reduced-free-product MF theorems impose correspondingly
strong hypotheses (for example special MF/AH input with faithful traces), not
mere convergence of group-element moments.

Consequently, one cannot currently deduce

`regularly MF-realized H  =>  C*_r(H*Z) MF`.

Even `C*_r(G) MF` would only pass the necessary vertex gate above.  To make
`A_Mac` MF one must still put the two vertex embeddings into a common matrix
corona so that their edge restrictions agree after the parity twist.  By
Shulman's general amalgam criterion, that compatibility is exactly the
missing projective-sector datum, not a consequence of MF of each vertex.

## 6. Ranked live targets

The current FALSE-side targets, in decreasing order of directness, are:

1. construct the projective asymptotic sector `(PSC4)` for the cyclic-shear
   extension;
2. prove the exact Mackey algebra `A_Mac` is MF by compatible norm-corona
   embeddings, not merely by separate vertex MF models;
3. exploit candidate-specific structure to obtain positive-rank propagation,
   bypassing the functorially optimal `sqrt(d)` loss proved in
   `FALSE_FERMIONIC_AMPLIFICATION.md`;
4. construct a co-hyperlinear/non-co-sofic IRS that is actually a normal
   Dirac mass.

The BDL theorem becomes immediately decisive after target 1 plus quotient
hyperlinearity.  Manzoor becomes immediately decisive after target 4.  The
other cited stability papers provide local tools, but none removes either
missing hypothesis.
