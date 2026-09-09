# Enlarge the digit-fiber stabilizer, 2026-09-08

The previous double-coset obstruction can be bypassed in the
explicit digit model by enlarging the stabilizer. For H=H_(h,r),
let F be the initial nonterminating digit fiber and K its full
setwise stabilizer. The written proofs in this batch show

    K finitely generated,   core_H(K)=1,   |K\H/K| <= h^3.

Thus H has a concrete type (A) action on its orbit of F. For
any lifted fixed-base shell envelope E, the intersection K intersect E
is exactly its original point stabilizer S. The index [K:S] is
infinite. This preserves the old shell orbit as an E suborbit
inside the larger action and explains why the earlier obstruction
for S does not apply to K.

This is a restricted construction. The universal Boone--Higman
claim and the new permutation-extension hypothesis remain open.

## Supported transport of boundary pieces

Write T for infinite digit words at node Y. A boundary tile is
alpha*T, with alpha ending at Y. Finite tile unions have a
well-defined count modulo h-1, preserved by all nucleus states
and hence all of H. Two nonempty unions of the same residue
can be transported by a prefix homeomorphism inside any clopen
set containing them.

The extension over the complement is explicit. A graph-prefix
forest with x leaves of type X and y of type Y has weight r*x+y
modulo r+h-1. Expand X leaves to Y leaves; a Y expansion followed
by expansion of its new X child adds r+h-1 Y leaves. Equal
weights therefore give matching refinements. After equalizing
the boundary tile counts modulo h-1, the two complements have
equal weights and can be matched by this calculation.

## The full stabilizer is finitely generated

Restriction of K to F maps onto B=V_(h,r)(Z_odometer). Boundary
tables lift using the partial carry maps I^c. Their omitted finite
unions of token cones can be matched using the lifted binary V
action, even when the two numbers of omitted cones differ.

The restriction kernel J consists exactly of maps which are
identity near F. Pointwise identity on F excludes both nonidentity
nucleus states: I restricts to the adding machine a, and D
restricts to prefix(h)*a^-1. Consequently a sufficiently deep
neighborhood of F has only identity local states.

Let A be the full copy of H supported in the zero-gap token cone.
The lifted binary prefix shift t expands the first N+1 gap cones
to the first N+2. Hence J is the ascending union of t^N*A*t^-N.
The host H is finitely presented, and B is finitely generated,
so A, t, and finitely many lifts of B generators generate K.
This does not assert that J is finitely generated, that the
extension splits, or that K is finitely presented.

## Three regions classify the double cosets

For S=g(F), record the labels of F intersect S, F minus S,
and S minus F. A label distinguishes the empty set from the
h-1 possible residues of a nonempty boundary set. There are h
labels in total.

Matching labels on the two regions inside F gives a boundary
prefix map, which lifts to K. The remaining region off F can
then be matched by supported prefix transport fixing F. Thus
equal triples give the same K orbit, and there are at most h^3
double cosets. Not every label triple is asserted to occur.

Translates of F also separate the dense set of paths with finitely
many terminators: a translate can lie in any prescribed clopen
neighborhood of such a point while containing that point. An
element preserving every translate fixes this dense set and is
identity. This proves core-freeness.

The finite presentation of H uses the existing
[full contracting RSG theorem](https://arxiv.org/pdf/2309.06224).
Finite generation of the odometer prefix quotient follows from
the existing [bounded-automata finiteness theorem](https://arxiv.org/html/2407.03149v1#S2.SS3).
The resulting faithful finite-rank action meets the
[type (A) criterion](https://arxiv.org/pdf/2405.18354). The transport,
kernel calculation, and this particular orbit action are the
additional written arguments here.

## What remains for the universal problem

The new OPEN claim permits an arbitrary finitely presented Gamma
containing E_nu and a finitely generated core-free K of finite
bi-index, with K intersect E_nu=(E_nu)_p. It is weaker than asking
to retain the old stabilizer unchanged. The digit model proves
these requirements in its arithmetic setting, including A5*A5.

An arbitrary decidable input need not admit a rational action,
so the existence of H_(h,r) cannot be used as a universal compiler.
The outstanding task is to construct such a permutation extension
without that arithmetic hypothesis. No proof of that existence
statement, Lean certificate, or GPU result is claimed.
