# Action-class separation already contains the exotic group

Date: 2026-08-11

## 1. Outcome

The action-level reformulation in `(AHG1)--(AHG5)` of `notes/NOTEPAD.md`
is a correct sufficient criterion for FALSE, but it is not a shortcut to a
construction using known hyperlinear groups or finite matrix groups.

The reason is purely quantificational.  Let `C_1 subset C_2` be two classes
of groups.  If an action is a sofic `C_2`-action but not a sofic
`C_1`-action in the sense of Alekseev--Bradford, then one of the auxiliary
target groups occurring in the definition already belongs to

`C_2 minus C_1`.                                       `(AAN1)`

For `C_1` equal to the sofic groups and `C_2` equal to the hyperlinear
groups, that auxiliary target is itself a hyperlinear nonsofic group.
There is no need to form the semidirect product in order to obtain the
counterexample.

Applied to the explicit gauge action `beta` from `(AHG1)`, whose failure to
be a sofic action is proved there, the statement

`beta is a hyperlinear-sofic action`                    `(AAN2)`

already contains a hyperlinear nonsofic target group at one fixed finite
obstruction window.  Thus `(AAN2)` remains a valid endpoint, but it cannot
be established by taking the Alekseev--Bradford target `Lambda` to be a
finite group, a finite-dimensional linear group, or any other known sofic
group.

## 2. The nested-class theorem

Recall Definition 4.23 of Alekseev--Bradford.  An action

`alpha:Gamma->Aut(Delta)`                              `(AAN3)`

is a sofic `C`-action if, for every finite `F subset Gamma`, finite
`E subset Delta`, and `epsilon>0`, there exist

1. a target group `Lambda in C`;
2. a finite set `A`;
3. a unital `(F,epsilon)`-multiplicative map
   `varphi:Gamma->Sym(A)`; and
4. injective partial homomorphisms `pi_s:E->Lambda` on a subset of more
   than `(1-epsilon)|A|` states,

satisfying the exact automorphic compatibility equation on the prescribed
window.

**Theorem 1 (action-class separation).**  Let `C_1 subset C_2`.  If
`alpha` is a sofic `C_2`-action and is not a sofic `C_1`-action, then there
are finite `F,E` and `epsilon>0` such that every automorphic approximation
of that window has target outside `C_1`.  In particular, applying the
`C_2` hypothesis to this window produces a group

`Lambda in C_2 minus C_1`.                            `(AAN4)`

**Proof.**  Negating the definition for `C_1` gives finite `F,E` and
`epsilon>0` for which no target `Lambda in C_1` admits the required data.
The `C_2` definition applied to exactly this triple supplies the data for
some `Lambda in C_2`.  That target cannot belong to `C_1`.  End proof.

The theorem is valid for any nested approximation classes; it does not use
the semidirect-product permanence theorem.

## 3. Consequence for the explicit gauge action

The action-level theorem in `notes/NOTEPAD.md` proves that the explicit
gauge action

`beta:G->Aut(Delta)`                                  `(AAN5)`

is not a sofic action with targets in the class of sofic groups.  Equivalently,
there is at least one finite triple

`(F_0,E_0,epsilon_0)`                                 `(AAN6)`

for which every admissible target is nonsofic.

If `(AAN2)` holds, use its hyperlinear target on `(AAN6)`.  Theorem 1 gives

`Lambda_0 is hyperlinear and nonsofic`.               `(AAN7)`

This proves FALSE before applying Alekseev--Bradford Corollary 5.2 to
`Delta semidirect_beta G`.

There is a useful finite-generation refinement.  Only the finite union of
the images `pi_s(E_0)` and the finitely many products required by the
partial-homomorphism table are used.  The subgroup `Lambda_0'` they
generate is finitely generated.  Hyperlinearity passes to subgroups.  If
`Lambda_0'` were sofic, the same finite table would be an approximation
with a sofic target, contradicting `(AAN6)`.  Hence one may take the
counterexample in `(AAN7)` to be finitely generated.

## 4. What this rules out computationally

Every finite group is sofic.  More generally, every finite-dimensional
linear group is sofic as an abstract group: each of its finitely generated
subgroups is residually finite by Malcev's theorem, and soficity is local.
Therefore none of the following can serve as `Lambda` for the obstruction
window `(AAN6)`:

1. a finite permutation group;
2. a subgroup of one fixed `U(d)`;
3. a finite Clifford or Pauli normalizer;
4. a finite congruence group; or
5. any other already-known sofic target.

A finite matrix computation can still search for compatible microstates
whose tracial-ultraproduct image supplies `Lambda_0`, but the exact target
group extracted from a successful sequence is already the desired
hyperlinear nonsofic group.  Describing the problem as a hyperlinear-sofic
action does not remove the same cross-level consistency and injectivity
gate which appears in the direct microstate formulation.

The correct value of the action language is organizational: it isolates a
single finite automorphic table and proves that any hyperlinear realization
of that table is automatically exotic.  It does not reduce the positive
half to covariance inside familiar finite-dimensional groups.

## 5. Revised computational endpoint

The useful next object is the obstruction window `(AAN6)`, not a generic
test of Definition 4.23.  An effective program would seek:

1. an explicit finite `F_0,E_0` and rational `epsilon_0` witnessing failure
   of every sofic target, preferably through a positive finite-action loss
   certificate; and
2. a sequence of matrix microstates realizing the same automorphic table
   in a tracial ultraproduct, with all elements of `E_0` separated.

The first item turns the qualitative nonsoficity proof into a finite dual
certificate.  The second item then constructs the group in `(AAN7)`
directly.  This is the action analogue of the permutation-versus-unitary
domination-constant program, and it makes clear that a one-level finite
matrix target can never be enough.

## Reference

Vadim Alekseev and Henry Bradford, *Sofic actions, halo products, and
metric approximations of groups*, arXiv:2601.18742, Definition 4.23 and
Corollary 5.2.
