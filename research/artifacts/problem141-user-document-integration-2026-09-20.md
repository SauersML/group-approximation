# Integration of the supplied Problem 141 proof attempt

20 September 2026. Provenance: the user supplied the document headed
"Problem 141: residual finiteness of hyperbolic groups — A proof attempt,
two transfer obstructions, and a precise remaining construction".
This index integrates its mathematical content without duplicating claims
already in Cairn. The document explicitly does not solve Problem 141;
neither does this integration. No claim of historical priority is made.

## Canonical map

| Supplied section | Cairn location | Logical role |
| --- | --- | --- |
| 2.1, 3 | `wave2-finite-lamp-wreath-hyperbolic-subgroups-are-rf` and `wave2-finite-lamp-wreath-subgroup-proof` | Proved finite-support embedding; hyperbolic and torsion-free subgroup corollaries. |
| 4 | `wave2-split-locally-finite-residuals-coincide` and `wave2-split-locally-finite-residual-proof` | Proved equality of finite and word-hyperbolic residuals for a split locally finite extension of an RF group. |
| 5 | `hyperbolic-rf-wave2-user-transfer-audit-2026-09-20.md`, application section | Direct proof that the specified actor is RF and the two-lamp mark is nonidentity and finite-residual; no analytic Liu theorem required. |
| 6 | `problem141-common-kernel-double-contains-product` and its proof route | Proved explicit copy of N times Z in a proper symmetric double, hence Z² when N has an infinite-order element. |
| 7 | `kun-thom-centralizer-normality-automatic-in-hyperbolic` and `hyperbolic-image-compression-kernel-2026-09-12.md` | Existing compression-image obstruction; reused, not rediscovered. |
| 8.1 | `central-pullback-finite-image-center-criterion` and its proof route | Established conditional theorem transporting a central prime mark. |
| 8.2 | `deligne-triple-cover-finite-residual-is-center` and its proof route | Existing Deligne triple cover; the supplied argument only needs the weaker inclusion of its C3 kernel in the finite residual. |
| 8.3 | `hyperbolic-finite-images-exclude-a-central-prime` | OPEN construction input. |
| 8.4 | `rips-central-pullback-finite-image-centers-2026-09-12.md` | Existing equivalence with conjugation-invariant homomorphisms from finite-index normal subgroups to Cp. |
| 9 | Explicit proof below | Free-group pullbacks split, so invisibility does not automatically survive a hyperbolic cover. |
| 10 | `finite-central-extension-rf-iff-virtually-splits` and its proof route | Existing criterion with its RF-base hypothesis retained. |
| 11 | `non-residually-finite-hyperbolic-group` and `non-rf-hyperbolic-via-central-rips-pullback` | Main target and conditional route remain OPEN. |

The two `wave2-` theorem/proof pairs and their complete transfer-audit
artifact were already present as uncommitted work matching this supplied
document. This integration adopts those exact scoped files instead of
creating duplicate theorem identities. Other concurrent campaign and
Lean changes are not included.

## An important existing equivalence

`hyperbolic-rf-central-prime-center-equivalence` proves more than a
one-way sufficient criterion. For each fixed prime p, existence of a
non-elementary hyperbolic group whose every finite-image center has order
prime to p is equivalent to existence of a non-RF hyperbolic group.

The forward construction is Deligne plus Belegradek--Osin and the
finite-image-center pullback criterion. For the converse, the
Kapovich--Wise equivalence supplies a nontrivial hyperbolic group with
no nontrivial finite quotients if universal hyperbolic RF fails. It must
be infinite and non-elementary, since finite and virtually cyclic groups
are RF; it satisfies the finite-center condition at every prime.

The canonical proof now uses this direct Kapovich--Wise dependency,
rather than the stronger RF/virtual-torsion-free/Kazhdan equivalence.
No property-(T) or filling argument is needed for this direction.
This is a simplification of dependencies, not a new existence proof.

Thus the missing H0 in supplied Section 8.3 is a precise reformulation
of the main difficulty, not an established kernel or a known easier
construction. The p=3 specialization is valid, but remains conditional.

## Free pullbacks: explicit failure of automatic invisibility

Let E -> Q be the supplied central C3 extension, and choose a finite-rank
free group F surjecting onto the finitely generated group Q=Sp4(Z).
Its pullback Y_F -> F is a central C3 extension. Choose a lift in Y_F
of each free generator of F. Freeness extends the lifts to a homomorphism
F -> Y_F whose composite with the projection is the identity. Since the
kernel is central, multiplication gives an isomorphism C3 times F -> Y_F.
Projection to C3 detects the pulled-back central generator. Thus the
original finite-residual element need not remain finite-residual after
pullback along a word-hyperbolic cover, even with finite central kernel.
This does not provide a Rips kernel with prescribed additional properties.

This proof is in the supplied Section 9. The earlier transfer-audit
artifact acknowledges it but its reference to the September 12 artifact
should not be read as a claim that that artifact contained this exact
free-group example. The proof is recorded here to remove that ambiguity.

The supplied Section 5 is also already connected to stronger canonical
results: `kun-thom-nonsofic-wreath` records the actor's residual finiteness;
`kun-thom-wreath-carries-rigid-defect` supplies the compression witness;
and `kun-thom-wreath-sofic-radical-is-fibre-parity-kernel` identifies the
whole finite residual. Its elementary two-lamp proof remains useful and
is retained in the transfer artifact without depending on Liu's analytics.

## Scope and attribution retained

- The finite-support subgroup argument applies to nonabelian finite
  lamps, arbitrary actions, and H not necessarily finitely generated.
  It uses finite H-intersection with the lamp group; the hyperbolic
  corollary follows from bounded orders of finite subgroups.
- Equality of residuals concerns **word-hyperbolic targets**, not the
  hyperlinear radical. It does not assert that every hyperbolic quotient
  is RF. A quotient can acquire a different residual obstruction.
- The double obstruction needs a proper edge subgroup and an
  infinite-order element in the common normal kernel to produce Z².
  No assertion about every Rips double is made without those hypotheses.
- The central pullback criterion is conditional on all finite images
  of the kernel, not just congruence images or a tested finite list.
  Property (T) does not supply the missing mod-p assertion.
- Liu is credited for the claimed nonhyperlinear wreath theorem, but
  none of the elementary transfer obstructions in this document uses
  his analytic centralizer proof. Earlier Cairn arguments retain their
  original citations; the supplied write-up is recorded as user input.

## Review boundary

The supplied finite-support, finite-image replacement, explicit lamp,
double-normal-form, and pullback arguments were checked directly.
Existing theorem identities and prerequisites were searched before
adding nodes. Independent internal review is not formal certification.
The exact roots and the missing finite-center input remain OPEN in the
validated graph. No claim that all hyperbolic groups are RF is made.

Independent review also found and repaired two older explanatory passages:
finite elementary groups do have property (T), and their centralizers in
a hyperbolic ambient group need not be finite. The finite-subgroup case
uses equality of a subgroup and its compressed conjugate by cardinality;
the non-elementary case uses finiteness of the centralizer. Neither
canonical theorem changes. This distinction matches supplied Section 7.
