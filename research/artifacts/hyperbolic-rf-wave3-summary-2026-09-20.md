# Problem 141: third parallel campaign

20 September 2026. **No non-residually-finite word-hyperbolic group has
been constructed. The root remains OPEN.**

This campaign investigated the finite-central-extension route after the
supplied proof attempt excluded the wreath subgroup and marked quotient
transfers. The supplied finite-image-center condition is not established;
the existing Deligne/Rips equivalence shows that finding a hyperbolic input
with that condition would itself resolve the root problem.

## Exact results

1. **A second specified cover does not split any of the three five-twists.**
   For the explicit PSL2(19) triangle, all three independent central
   five-twists remain nonzero on the kernel of the combined quotient to
   PSL2(19)^2. Prime-to-five transfer reduces the test to a 400-point
   permutation action. Three stored vectors satisfy the 720 required
   orbit-sum equalities and give the identity moment matrix over F5.
   This is a statement about one specified cover, not all covers.
   See `hyperbolic-rf-wave3-detectors-2026-09-20.md`.

2. **The canonical GHB7 face-zero class evaluates primitively.**
   Its integral evaluation ideal is Z. Exact local enumeration and the
   cyclic augmentation-module argument prove this without assuming
   residual finiteness. The central generator of its integral cover is
   therefore in the commutator subgroup. In every finite image F, its
   cyclic image A is a quotient of H2(F/A;Z). This supplies a necessary
   condition for detection, not a global bound on its finite orders.
   See `hyperbolic-rf-wave3-canonical-class-2026-09-20.md`.

3. **The stable Steinberg construction cannot detect this class.**
   Every CCKW matrix map over an associative unital F7-algebra lifts to
   the stable Steinberg group. This includes noncommuting block
   parameters. The corresponding central pullbacks and pushouts split,
   so cannot realize the canonical class modulo any m>1. Full finite-field
   Sp4 quotient bases also have trivial multiplier and kill the central
   generator. Arbitrary central extensions of the actual finite matrix
   image are not covered by the stable-lifting argument.
   See `hyperbolic-rf-wave3-visibility-2026-09-20.md`.

4. **H31 has only four finite images with abelian Sylow-five subgroups.**
   They are 1, C5, PSL2(31), and PSL2(31) x C5. Such an image makes the
   finite five-group vertex abelian, forcing c to centralize a and b;
   the quotient then factors through PSL2(31) x C5. Simplicity and
   perfectness classify its four quotients. All have order prime to
   seven. Thus a central-seven detector requires nonabelian Sylow-five
   subgroups. The root lane independently checked the presentation and
   the normal-subgroup argument.
   See `hyperbolic-rf-wave3-audit-2026-09-20.md`.

5. **The commutative scalar family also lifts to rank-two symplectic
   Steinberg groups.** Direct C2 root commutators verify all eleven
   defining relators. This excludes central extensions receiving the
   Steinberg preimage, including its central pushouts, without assuming
   that the entire unstable kernel is central. It still does not classify
   arbitrary abstract central extensions of the actual matrix image.
   The root independently checked this additional proof.
   See `hyperbolic-rf-wave3-symplectic-lift-2026-09-20.md`.

## Verification and remaining work

The separate audit lane reviewed the twist certificate, primitive-class
proof, and stable Steinberg lift. The root independently replayed both
standard-library certificate scripts. These are mathematical reviews and
exact computation checks, not proof-assistant formalizations.

The graph validation receipt is
`hyperbolic-rf-wave3-validation-2026-09-20.json`. It records canonical
loading, schema/artifact checks, and dependency states. It is not the
full duplicate/policy validation pass, and graph status does not certify
mathematical truth.

The next mathematical question remains quantified over **all** finite
quotients or covers: either prove persistence of a nonzero prime class
under every finite-index restriction, or uniformly bound the finite
orders of the chosen integral central generator. None of the finite
computations or restricted quotient classifications above supplies that
universal statement. No counterexample or positive solution is claimed.
