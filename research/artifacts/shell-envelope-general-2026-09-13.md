# Shell envelopes in general: complexity wall, rigidity, shift normalization, 2026-09-13

Lane `solve-shell-envelope-general`. Target: `decidable-inputs-have-fp-shell-envelopes`,
which is OPEN. The target node was edited by another lane within 6 hours, so it is
not edited here and everything below lands as new nodes.

## Verdict

- **The complexity wall does not apply** to shell envelopes as a family (Section 1).
- **Two new theorems**, both computing ESTABLISHED in Cairn. Neither has been
  independently reviewed, and no novelty is claimed.
  - `fp-shell-envelopes-are-unique-shell-solutions-of-their-relators`: a finite
    presentation of `E_nu` (or `A_1`) has `rho` as its only shell-shaped
    solution, and the solution set is closed.
  - `one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`: for a
    one-ended input, no power `s^m` with `m != 0` conjugates `lambda(P)` into
    itself near infinity, through any endomorphism. So the ascending gate can
    never be witnessed by `B = lambda(P)`.
- **No finite presentation**, and no obstruction to one, is found for any input
  that is not virtually cyclic. The target stays OPEN.

## 1. The complexity wall

- **What the wall says.** `complexity-bounded-host-classes-are-not-universal`
  and `uniform-wp-bound-excludes-bh-universal-targets` rule out any host class
  whose word problems share one recursive time bound.
- **Why it doesn't apply.** Every shell envelope contains `hat(P) ≅ P`
  (`shell-cantor-embeddings-are-finite-germ-extensions`), so the word problem of
  `P` reduces to that of `E_nu` letter by letter. The inputs range over decidable
  groups of arbitrarily high complexity (`kms-arbitrarily-hard-fp-rf-groups`), so
  no recursive bound covers the family. Shell envelopes are exactly the shape the
  wall permits: the host is built from an actor already containing the input.
- **Where it does bite.** It bites on sub-families of enumerations with a uniform
  ceiling on germ complexity. The arithmetic benchmark gives a decision procedure
  for fully residue-affine regular actions
  (`research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md`),
  and the lane idea A5 notes their bounded complexity (see
  `research/artifacts/shell-envelope-local-tests-2026-09-13.md`, Section 4).
  Route-form enumerations (`route-form-shell-inputs-have-computable-mixed-near-relations`)
  make only one generator arithmetic, so they escape it.
- **Effective consequence of finite presentation.** A finite presentation forces
  `nu` to be computable (`shell-recursive-presentations-compute-enumerations`).
  No recursive runtime bound is forced, and none is needed.

## 2. What Belk–Hyde–Matucci Theorem 2.1 asks for here

Theorem 2.1 and the SingFix definition are quoted verbatim in the local tests
artifact.
- **The clauses at `n = 2`.** They are `Fix_V(F)` for rational `F`, which is
  known finitely presented, together with `A_1`, `A_12` and `A_2`.
- **Finite generation.** Every `S(M,M')` is finitely generated for every
  enumeration (`shell-finite-point-stabilizers-are-finitely-generated`).
- **Recorded chain.** `A_1` finitely presented implies `Q` finitely presented,
  equivalently `F_nu` finitely presented. That implies `R_nu` finitely presented
  plus the ascending gate.
- **Status.** Only the implications toward the gate are proved. The gate is not
  known to be necessary for `E_nu` itself.

**Presentation of `A_1`, in outline only (not landed as a claim).** Let `K` be
the elements of `V` equal to the identity near `p`. Then `A_1` is presented by:
- the relators of `Fix_V(p)`;
- lifts of the relators of `Q` in `hat(S)` and `t`, each set equal to its value
  in `K`;
- the conjugation relations `hat(s)^(+-1) k hat(s)^(-+1) = k'` for `k` in a
  generating set of `K`.

Why this is a presentation:
- The conjugation relations make the image of `K` normal.
- The quotient by that image is `Q`.
- `K` injects into `A_1`, so the kernel meets it trivially.

Consequence:
- If `Q` is finitely presented, finite presentation of `A_1` is equivalent to
  finitely many conjugation relations implying the rest.
- For a finitary shell transposition `(n n+1)`, the relation says
  `hat(s) (n n+1) hat(s)^-1 = (rho_s(n) rho_s(n+1))` for all `n`.
- Whether `Q` finitely presented implies `A_1` finitely presented remains open.

## 3. Rigidity

- **Statement.** `fp-shell-envelopes-are-unique-shell-solutions-of-their-relators`
  says: if a finite presentation on `Y ∪ S` holds for `V` together with shell
  relabelings `h(pi_s)`, then `pi = rho`.
- **Scope.** The tuples `pi` are arbitrary permutations of `N`, with no group
  action assumed. The solution set is closed.
- **Proof ingredients.** A double commutator shows the induced map is injective.
  Localized suffix elements `u_n` then read off `pi_s(n)`.
- **Use as an obstruction.** Finite presentation fails as soon as every finite
  set of valid relations has a second shell solution. The free-shift obstruction
  is one such construction.
- **What it does not give.** Sym(N)^S is not compact, so this does not by itself
  give a pumping or complexity argument. The E_2 analogue
  (`fp-bounded-displacement-e2-envelopes-are-eventually-periodic`) needs bounded
  displacement. For regular actions that forces linear growth, hence a virtually
  cyclic input, so that route adds nothing beyond the finite-ray case.

## 4. Shift normalization

`one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`:
- **Setup.** A shift-normalizing enumeration transports `s^m` to a near-bijection
  `sigma` of `P` with `sigma(gy) = phi(g) sigma(y)` on all but finitely many edges.
- **Rigidity.** One-endedness leaves a single cofinite component, where `sigma`
  is the affine map `y -> phi(y) c`.
- **Contradiction.** Near index `m != 0` is incompatible with agreeing with a
  bijection off a finite set.
- **Relation to the prefix core.** The prefix-core classification is the case
  `phi = id`. This claim allows any endomorphism, including automorphisms of
  infinite order.
- **Sharpness.** The zigzag enumeration of `Z` realizes `s lambda_1 s^-1 = lambda_(-1)`.

For the gate:
- `ker(eta)` contains every conjugate `s^k lambda(P) s^-k`, and for one-ended
  inputs the ascending subgroup `B` cannot be `lambda(P)`.
- Any witness needs a finitely generated `B` strictly larger than `lambda(P)`,
  with `s^-epsilon B s^epsilon <= B` and the ascending union equal to `ker(eta)`.
- Coarse versions of the argument, with bounded-length words in place of single
  letters, give no contradiction. A bi-Lipschitz index-one bijection exists on
  any infinite bounded-geometry graph (push along a ray). So this rigidity is
  specific to exact normalization.

## 5. Test instances

- **(a) `P = Z`.** Positive: the signed-coset finite-ray enumeration makes every
  `S(M,M')` finitely presented (`virtually-cyclic-inputs-have-fp-shell-stabilizers`).
  The zigzag enumeration shows `s` normalizing `lambda(Z)` through inversion.
- **(b) `P = BS(1,2)`.** One-ended, since it is solvable, not virtually cyclic,
  and not a free product. So:
  - no shift power normalizes `lambda(P)`;
  - rational regular shell actions are excluded
    (`rational-regular-shell-actions-require-virtually-cyclic-input`).

  Partial normalization of the subgroup `<a>` alone, `s^-1 lambda_a s = lambda_(a^2)`,
  is not excluded. The Schreier graph of `<a>` has infinitely many two-ended
  components, and Step 3 of the proof needs connectedness. No enumeration was
  decided.
- **(c) `P = Z wr Z`.** Not finitely presented, so it lies outside the target's
  hypothesis. The Boone–Higman route already passes to perfect finitely presented
  decidable inputs. No obstruction to a finitely presented `E_nu` for a
  non-finitely-presented input was found.

  Note that `lambda_g -> g`, `s -> 1` does NOT define a homomorphism
  `R_nu -> P`: for the zigzag enumeration `s lambda_1 s^-1 lambda_1 = 1` near
  infinity, but the image is `2 != 0`. So finite presentation of `P` can't be
  obtained from finite presentation of `R_nu` by that retraction. `Z wr Z` is
  one-ended, so Section 4 applies to it.
- **(d) General inputs.** See the gap.

## 6. Exact gap

- **Needed.** A one-ended decidable finitely presented input `P` and an
  enumeration `nu` such that:
  - `R_nu` is finitely presented;
  - `ker(eta)` is an ascending union of `s^(+-1)`-conjugates of a finitely
    generated `B` strictly larger than `lambda(P)`;
  - the conjugation relations of Section 2 are finitely generated modulo the
    germ relations.

  That would make `A_1` finitely presented; analogous control is still needed
  for `A_12` and `A_2`.
- **Alternatively.** A finite presentation argument for `E_nu` that doesn't go
  through `A_1`. Its necessity chain is not established.
- **Obstruction side.** A second shell solution for every finite relator set,
  for every enumeration of some one-ended input, would refute the target.

## 7. Verification boundary

- **Proofs.** Written proofs in the two route nodes. No computation was needed
  or run.
- **Sources.** The only external input is Belk–Hyde–Matucci Theorem 2.1, as
  quoted in the local tests artifact, and it is not used in either proof. The
  standard facts on ends are labeled standard in the claim text.
