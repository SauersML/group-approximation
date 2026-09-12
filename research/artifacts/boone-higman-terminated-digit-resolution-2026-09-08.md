# Resolve arithmetic shell limits by terminated digits, 2026-09-08

The entire explicit arithmetic A5*A5 shell envelope now has a
faithful embedding in a full contracting rational similarity group,
and hence in a finitely presented simple group. Its own finite
presentation remains open, as does the universal Boone--Higman
conjecture. This is a positive result for the whole restricted
envelope, beyond the previously constructed ambient groups for
its near and germ quotients.

## The four-map nucleus

Use a graph with a root node X, r edges to a digit node Y, h
digit loops at Y, and a terminator # returning to X. Digits
1,...,h encode a nonnegative integer in bijective base h, and
the terminator ends that integer without touching the remaining
path. On the digit cone, the injections I and D perform q->q+1
and q->h*q on terminated integers.

Their recursive formulas have only themselves and the two node
identities as local actions. Their inverse formulas exchange I
and D as recurrent states. The products I*D and D*I are prefix
injections, and I^2,D^2 have only I or D and identity recurrent
states. The attached proof explicitly checks all four products,
the inverse domains, and recurrence. Thus the four maps form a
finite nucleus of injections, not just a finite list of transducer
states for unrelated generators.

The graph is irreducible. The nucleus classification and embedding
theorems in [Belk--Bleak--Matucci--Zaremsky](https://arxiv.org/pdf/2309.06224)
(Definition 2.43, Theorem 2.46, and Theorems B,C) supply a full
contracting RSG H_(h,r), its finite presentation, and a finitely
presented simple overgroup. Those are imported theorems, applied
to the nucleus verified here.

## Faithfully lift the original group

Encode a binary gap 0^n*1 by a root residue i, the terminated
bijective-base word for q, where n=r*q+i, and then the next gap.
The paths with infinitely many terminators form a dense invariant
copy of the binary sequences with infinitely many 1s. Binary
prefixing by 0 increments the first gap; prefixing by 1 prepends
the zero-gap token. Their rational images are disjoint clopen
pieces covering the new path space, so binary V tables lift.

Fixed-base odometer near charts also lift: a finite prefix change
is followed by a fixed integer carry on the remaining digit word.
Finite exceptions are exact replacements of terminated tokens.
The carry states belong to the same nucleus. These lifts agree
with the original shell generators on the invariant dense set.
Relations extend by continuity, and faithfulness follows on that
same set. The neighborhood kernels are retained.

For the A5 example, h=59 and r=4: doubling the single-ray action
gives source step 236 and image steps 13924,236,4, with odd
indices fixed. These are the required four-root charts. The
result embeds E_nu in H_(59,4), not merely its germ quotient.

## Scope of the result

The new Cantor space replaces each eventual-zero limit point by
a Cantor fiber of nonterminating digit paths. This is a different
action, not a conjugacy of the original binary shell action.
It does not contradict the earlier proof that the specified
binary shell generators are not rational.

The fixed-base near-chart hypothesis is a real restriction.
It implies residue-affine regular input data and hence polynomial
word problem for that input, as previously proved. Arbitrary
decidable inputs cannot be required to have this complexity.
No universal fixed-base compiler is claimed, and finite presentation
of the particular subgroup E_nu has not been inferred from its
embedding in the finitely presented H_(59,4).

The commutator-subgroup question that motivated this audit was
not resolved: finite presentation of an odometer group alone does
not establish finite presentation of its simple commutator subgroup.
The terminated-digit embedding uses the published contracting-RSG
theorem instead. These arguments are written proofs, not Lean
certificates or GPU results.

## Remote validation

The written claims and routes were committed in `4720da4e7` and
integrated into main at `2bf6d9341b14c6694eb804b35a50d8d0a40a13aa`.
[GitHub Actions run 34302815969](https://github.com/SauersML/group-approximation/actions/runs/34302815969)
passed on that exact integration commit. Its checks covered source
syntax, the existing exact finite controls, and Cairn graph validation.
The downloaded exports are in
`.cairn/bh-digit-resolution-check-20260908/`.

The nucleus, faithful lift, and A5 simple-host nodes are all
`ESTABLISHED` through the written routes displayed in their `why`
exports. The A5 envelope's own finite presentation, the universal
perfect-input envelope claim, and Boone--Higman remain `OPEN`.
These statuses record dependencies on written proofs and imported
theorems; they are not independent proof verification. No Lean
proof of this construction or GPU computation was run.
