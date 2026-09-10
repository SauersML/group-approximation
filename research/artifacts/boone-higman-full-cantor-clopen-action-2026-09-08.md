# Full Cantor groups and the clopen action

Attachment reconstructed on September 10, 2026 from the six surviving
statement and proof nodes listed below. This is not recovered text of
the missing attachment and does not constitute a new independent proof
review. Its purpose is to supply the mathematical argument already
recorded in those nodes at their declared artifact path.

Let C be binary Cantor space and V its standard binary prefix group.
The hypothesis V<=D<=Homeo(C) always refers to that concrete action.
Fullness means that every homeomorphism locally agreeing with D belongs
to D. Containing an abstract copy of V does not supply this hypothesis.

## Supported copies and stabilizers

For a nonempty clopen U, partition C and U into equally many binary
cones and use prefix replacements to obtain a homeomorphism f:C->U.
Every sufficiently small restriction of f or f^-1 extends to V: shrink
its domain and image to proper cones, refine the complementary cone
partitions to equal leaf counts, and complete the prefix bijection.

For g in D, let lambda_U(g) be f g f^-1 on U and the identity outside U.
Near each point in U it agrees with v2 g v1 for suitable elements of V;
outside U it agrees with the identity. Fullness puts it in D(U).
Conversely f^-1 k f locally agrees with D for every k in D(U), so
fullness puts it in D. These operations are inverse homomorphisms.
Thus D(U) is isomorphic to D.

An element preserving every cell of a finite clopen partition splits
into its supported restrictions, each in D by fullness. They commute,
have trivial pairwise intersections, and multiply to the original
element. The partition stabilizer is therefore a finite direct power
of D. For a finite family of clopen sets, take its nonempty Boolean
atoms. The pointwise family stabilizer is such a direct power; the
setwise family stabilizer is a finite extension of it. Finite generation
and finite presentation pass through these operations.

Surviving sources: [claim](../full-binary-cantor-groups-have-copy-stabilizers.md)
and [proof](../full-cantor-prefix-compression-and-partition-proof.md).

## Clopen action and type A

Assume D is finitely presented. Proper nonempty clopen sets form a
countable set. Its D-action is faithful because clopen sets separate
points. A finite tuple is classified under V by which of its labeled
Boolean atoms are nonempty: refine corresponding cone partitions to
the same leaf counts and match them. Every homeomorphism preserves
that pattern, so the same classification holds under D. The action
is oligomorphic.

For an ordered pair, its four atoms have a two-by-two support matrix
with no empty row or column. There are two supports of size two,
four of size three, and one of size four: seven ordered-pair orbits.
After removing equality and forgetting order, the two containment
orientations merge and the other types remain distinct, giving five
orbits of two-element subsets. A clopen point stabilizer is D times D,
and finite-family stabilizers have the finiteness properties above.

Together with finite presentation of D these verify the type A
hypotheses of the separately registered
[embedding theorem](../type-a-action-gives-boone-higman-for-subgroups.md).
That theorem gives the finitely presented simple overgroup, and its
word-problem consequence applies to finitely generated subgroups.
This assumes a finitely presented full actor; it does not construct
one for arbitrary decidable input groups.

Surviving sources: [claim](../fp-full-binary-cantor-groups-have-type-a-actions.md)
and [proof](../full-cantor-boolean-atom-orbits-and-embedding-proof.md).
They cite [Belk--Bleak--Matucci--Zaremsky, Definition 2.24](https://arxiv.org/pdf/2309.06224)
for fullness and [Zaremsky's type A criterion](https://arxiv.org/pdf/2405.18354).

## Shell fullness

For a shell envelope E_nu, use the finite-germ and single-singularity
realization results declared in its surviving proof node. A local
patching f has, by compactness, finitely many local representatives
and a finite singular set F relative to V. It preserves every V-orbit.
Use high transitivity of V on the singular orbit to postcompose f so
that it fixes F. At each q in F, realize its isotropy germ by an E_nu
element singular only at q. Prefix interpolation corrects that element
to be the identity near the other finitely many points of F without
altering its germ at q. The product of these corrected elements has
all the prescribed germs. The remaining homeomorphism is locally V
everywhere, hence belongs to V by fullness of V. Thus f belongs to E_nu.

The supported-copy result applies. Finite generation of the input
implies the stated finite-generation consequences for these stabilizers.
Fullness does not prove finite presentation: the proof node explicitly
requires the known non-finitely-presented shell examples to retain that
distinction.

Surviving sources: [claim](../shell-envelopes-are-full-cantor-groups.md)
and [proof, including its three declared premises](../shell-local-patching-and-independent-germ-fullness-proof.md).
