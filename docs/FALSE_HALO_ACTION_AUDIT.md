# FALSE lane: the hyperlinear halo-action shortcut is circular

Date: 2026-08-10

Alekseev--Bradford, *Sofic actions, halo products, and metric
approximations of groups* (arXiv:2601.18742), prove that a semidirect product
of hyperlinear groups is hyperlinear when the automorphism action is a
sofic hyperlinear action.  Since the Kun--Thom group

`W=(directSum_(G/Gamma) C_2) semidirect G`                    `(HAA1)`

is exactly a permutational wreath product, this looks like a possible direct
route to a hyperlinear nonsofic group.  The following audit shows why the
framework does not manufacture the first such example from ordinary matrix
or Clifford witnesses.

## 1. The finite-data target reduction

In Alekseev--Bradford Definition 4.1, a finite action test consists of

* finite sets `F subset G` and `E subset Delta`;
* a finite permutation approximation `phi:G->Sym(A)`;
* a large set `S subset A`; and
* injective partial homomorphisms

`pi_s:E->Lambda`, `s in S`,                               `(HAA2)`

for one target group `Lambda` in the selected approximation class.  The
covariance identities involve only the finitely many elements appearing in
the images in `(HAA2)`.

**Lemma (local target reduction).**  For each such finite witness, `Lambda`
may be replaced by the subgroup

`Lambda_0=<pi_s(e):s in S, e in E>`.                       `(HAA3)`

In particular `Lambda_0` is finitely generated.

**Proof.**  Every partial product, injectivity assertion, and covariance
identity in the definition is an equality or inequality among elements of
the finite union of the images in `(HAA2)`.  All those elements lie in
`Lambda_0`, and the inclusion `Lambda_0->Lambda` is injective.  Thus the
same maps and the same permutation approximation remain a witness.  End
proof.

## 2. Locally sofic targets collapse the distinction

**Theorem (locally sofic collapse).**  If an automorphism action has
Alekseev--Bradford witnesses whose target groups are locally sofic, then it
is already a sofic sofic-action in their sense.              `(HAA4)`

**Proof.**  Apply `(HAA3)` to every finite test.  The resulting target
`Lambda_0` is finitely generated and lies in a locally sofic group, hence is
sofic.  These are exactly the same witnesses with the target class changed
from the original class to the class of sofic groups.  End proof.

Finite-dimensional unitary and Clifford targets are covered by `(HAA4)`.
Every finitely generated subgroup of `U(n)` is a finitely generated linear
group and therefore residually finite by Malcev; in particular it is sofic.
Finite Clifford groups are of course finite.  Direct products and matrix
amplifications do not change this conclusion at any fixed finite action
test.

## 3. Consequence for the Kun--Thom action

Both factors in `(HAA1)` are sofic: the lamp group is locally finite and
the acting group `G` is residually finite.  Alekseev--Bradford's semidirect
product theorem for the sofic class would therefore imply that `W` is sofic
if its automorphism action admitted the witnesses in `(HAA4)`.  Kun--Thom
prove that `W` is nonsofic.  Consequently:

`the Kun--Thom action has no locally-sofic target witnesses.`  `(HAA5)`

In particular, replacing the coset labels by finite-dimensional vector,
Pauli, Clifford, or unitary labels cannot establish that the action is a
sofic hyperlinear action.  If a hyperlinear-action proof exists, then for
some finite test its target `Lambda_0` in `(HAA3)` must itself be a finitely
generated hyperlinear nonsofic group.  Producing that target already solves
the main problem.

Thus the halo-action theorem is an excellent permanence result once a
hyperlinear-nonsofic seed is known, but it is circular as a method for
constructing the first seed.  The FALSE lane must create trace-visible
nonsoficity before invoking this framework, not inside its finite local
targets.

## Source

* V. Alekseev and H. Bradford, *Sofic actions, halo products, and metric
  approximations of groups*, arXiv:2601.18742, especially Definition 4.1,
  Corollary 5.2, and the halo-product consequences.
