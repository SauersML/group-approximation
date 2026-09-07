# Cancellation phases: literature audit

Date: 2026-09-07. This is a bounded primary-source comparison, not a
novelty determination. No source below settles direct finiteness for all
group algebras in positive characteristic.

## Signatures and the current extension

[Igor Mineyev, *The topology and geometry of units and zero-divisors:
origami*](https://www.mineyev.web.illinois.edu/art/top-geom-uzd-origami.pdf),
section 2.2, defines a signature assigning signs to the two support sets
so that paired products receive opposite signs. Section 3.6 uses these
signatures to obtain cancellation identities over arbitrary coefficient
rings with unity. This is an explicit antecedent for the signed
cancellation construction. The inspected author-hosted version records
minor revisions dated August 12, 2026.

Cairn's accompanying argument extends the coefficient choices from signs
to roots of unity of order a power of two. For each oriented cell pair
put v_e = e_i + f_j - e_i' - f_j'. The assignment v_e -> -1 defines a
character of their integral span exactly when every integral relation
among them has even coefficient sum. Smith normal form extends that
character to the ambient lattice using finitely many such roots. The
forward identity lifts to cyclotomic integers; characteristic-zero direct
finiteness supplies the reverse identity, which reduces to the original
unsigned identity modulo two. This extension and its finite phase-order
bound were independently proved and audited in the current work. That
description asserts proof provenance within Cairn, not historical novelty.

The subsequent independently audited extension allows noncommuting
coefficients: the signed matching group has a central involution J, and
if J survives then Z[H]/(J+1) embeds in a complex group-algebra corner.
Tensoring with the external group algebra, reversing there, and reducing
by augmentation modulo two gives the unsigned reverse identity. The
obstruction to this lift is an odd identity among the actual normalized
relators; asphericity of that presentation excludes the obstruction.
The C_4/D_8 example shows this criterion is strictly stronger than scalar
phase liftability. These arguments are proved directly in the accompanying
Cairn routes; this bounded search does not establish their novelty.

## Universal presentations and support bounds

[Ken Dykema, Timo Heister, and Kate Juschenko, *Finitely presented groups
related to Kaplansky's Direct Finiteness
Conjecture*](https://arxiv.org/abs/1112.1790), develops universal
left-invertible-element groups from cancellation partitions and reduces
direct-finiteness questions to these presentations. Its classified cases
establish direct finiteness over F_2 for support pairs (3,n), n <= 11,
and (5,5), with the symmetric cases obtained by reversing multiplication.
The classification includes sofic nonamenable groups: nonamenability of
a universal presentation is not itself a counterexample. These are the
general support exclusions already imported into Cairn. This audit located
no verified larger general bound; failure to locate one is not a claim
that none exists.

## The geometric route and its stated obstruction

[Henry Shin, *A global girth obstruction for Garg--Mineyev taiko product
structures*](https://arxiv.org/abs/2607.01716), submitted July 2, 2026,
states in Theorem 1.1 that no complete even or odd product structure with
both support sizes at least two simultaneously admits coherent
orientation, no-fold, and the Garg--Mineyev triple-girth condition. The
three regimes require horizontal/middle girths at least (6,6), (4,8), or
(3,12). Thus the stated obstruction concerns one geometric assembly
mechanism at every support size. It does not assert the impossibility of
arbitrary weighted metrics or arbitrary cancellation presentations. The
primary theorem statement and scope were inspected; the full proof and
its supplementary finite certificate were not independently checked in
this audit.

The target distinction matters throughout: a nontrivial unit can have a
perfectly good two-sided inverse. An exact forward identity and distinct
support labels establish neither a nonzero reverse defect nor failure of
direct finiteness. A counterexample still requires BA = 1 and AB != 1 in
the same ordinary group algebra. The phase criterion excludes templates
that lift; its failure supplies a necessary obstruction, not that missing
reverse-defect certificate.
