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

The separate Thom-group shortcut is audited in
`FALSE_THOM_K_DOMINANT_CENTRALIZER_AUDIT.md`.  Its Prüfer tower gives
divisibility of favorable finite centralizer orbits but no control of their
normalized size.  The exact missing input is a dominant-orbit/ergodic-
centralizer theorem, not another iteration of the non-Hopfian quotient.

The atlas-side finite-central shortcut is closed in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`.  For the natural
map

`A_8*A_8 -> A_8 *_H A_8`,

the kernel `K` satisfies `K=[A_8*A_8,K]`.  Hence any central kernel in an
intermediate boundary quotient is automatically trivial.  The genuine
Leavitt boundary quotient nevertheless does not identify the aligned copies
of `H`, so its kernel over the amalgam is genuinely noncentral.  This gives
an explicit distant exact tracial branch and rules out globalization of the
classical boundary Jacobian by arbitrary finite-tracial rigidity.  The live
atlas target is now a matrix-specific coefficient/root-character extraction
theorem which turns group microstates into forbidden approximate Leavitt
operators inside the finite coefficient algebra.

The BDL theorem becomes immediately decisive after target 1 plus quotient
hyperlinearity.  Manzoor becomes immediately decisive after target 4.  The
other cited stability papers provide local tools, but none removes either
missing hypothesis.

## 7. The non-CE equivalence-relation factor does not become a group factor

The 2026 equivalence-relation construction should not be combined with
Chifan--Drimbe--Ioana's embedding-universality theorem by silently replacing
"generated by a representation" with "group factor."  The distinction is
the entire group problem.

Chifan--Drimbe--Ioana, *Embedding universality for II1 factors with property
(T)*, Theorem A(1), says that for every separable tracial von Neumann algebra
`M` and every acylindrically hyperbolic group `H`, there is a factor `Q`
containing `M` and a homomorphism

```text
pi:H -> U(Q),                 pi(H)''=Q.              (RLA1)
```

If `M` is Manzoor's non-CE equivalence-relation factor, then `Q` is non-CE.
Nevertheless `(RLA1)` does **not** imply that `H` is nonhyperlinear.  The
factor `Q` is the GNS factor of the extremal character

```text
chi(h)=tau_Q(pi(h)),                                    (RLA2)
```

and `(RLA2)` need not be the regular character.  Hyperlinearity of `H`
controls Connes embeddability of `L(H)`, equivalently of the regular
character, not of every factorial character of `H`.  A free group already
shows how large the difference is: arbitrary separable factors are generated
by representations of a free group.

The source states the remaining boundary explicitly: it is open whether the
family of group factors `L(G)` is embedding universal (Remark 1.1).  Its
relation theorem (Theorem D) embeds a trivial amplification of a p.m.p.
equivalence relation into another equivalence-relation factor.  It does not
identify the target with `L(G)` for a discrete group.  Thus neither Theorem A
nor Theorem D turns Manzoor's factor into a nonhyperlinear group.

There is, however, an exact character-rigidity reduction worth retaining.

**Proposition (universality/character bridge).**  Let `H` be an
acylindrically hyperbolic group such that every nonregular extremal character
of `H` has a Connes-embeddable GNS factor.  Then `H` is nonhyperlinear.

**Proof.**  Apply Theorem A(1) to a separable non-CE factor `M_0`.  This gives
`Q` and `pi` as in `(RLA1)`, with `M_0 subset Q`; hence `Q` is non-CE.  Since
`Q` is a factor, `(RLA2)` is extremal.  By the hypothesis it cannot be a
nonregular character, so it is regular.  Therefore the trace-preserving map
from `L(H)` onto `Q` is an isomorphism.  Thus `L(H)` is non-CE and `H` is
nonhyperlinear.  End proof.

A charmenable group with trivial amenable radical satisfies the character
hypothesis: its extremal characters are regular or von-Neumann amenable.
This does not currently instantiate the proposition.  Known charmenable
rigidity families are higher-rank/product-type groups, while the
acylindrically hyperbolic/SQ-universal input in Theorem A lies on the other
side of the normal-quotient divide.  No known group in the audited literature
has both properties.  Finding one would itself finish the problem.

Primary pins: Chifan--Drimbe--Ioana, Theorem A(1), Theorem D, Remark 1.1,
and the proof of Theorem A; Bader--Boutonnet--Houdayer--Peterson for the
charmenable character dichotomy; Manzoor for the non-CE relation factor.
