---
rg: 2
id: gap-refuted-witness-holes-are-collapse-equivalent
kind: claim
title: Prescribed-carrier and corona-module Leavitt decoders are equivalent to marked collapse
distinct_from:
  affine-leavitt-decoder-interface-is-mark-collapse-equivalent: that audits an existential carrier and is killed by the zero carrier; this treats the prescribed-carrier decoders (APC, AMR/BLAMR) and the exact corona-module decoder, where the carrier cannot be chosen, and kills them by a zero-operator or two-valued step modulus instead.
  heisenberg-decoder-premise-scale-lattice-is-two-valued: that (OPEN, demoted) proves an emptiness principle for decoders whose output corners are existential and of positive trace; this proves the equivalence for carriers fixed by the root spectrum or by the carrier theorem, where the output must live on a prescribed possibly rank-one atom, and uses only established gap lemmas.
  atomic-three-row-compiler-is-prototype-gap-equivalent: that shows the three-row compiler interface ATG1 is equivalent to ATG2; this shows the compiler's own consumer BLAMR is equivalent to the goal, so the whole AMR chain is target-equivalent.
  coherent-heisenberg-decoder-is-marked-nonhyperlinearity: that is the positive-density HS module decoder; this is the corona-module decoder, the atomic operator-norm decoder and the prescribed HS decoder.
  atomic-morita-return-kills-finite-order-mf-mark: that proves AMR implies collapse; this adds the converse, so AMR is exactly collapse and its modulus is two-valued.
artifacts:
  - research/gap-refuted-witness-holes-collapse-equivalence-proof.md
---

**ESTABLISHED LOGICAL AUDIT** (route
`gap-refuted-witness-holes-collapse-equivalence-proof`).  No Property `(T)`,
stability, or character input is used in either direction.

**Conventions.**
- `Gamma` is finitely presented, and `w` is a word with `w^p=1` in `Gamma`, of
  exact order `p>=2`.
- A `delta`-model is a unitary map on the finite relator window with defect at
  most `delta`, in the operator norm or in the normalized HS norm as stated.
- Spectral rounding sends each eigenvalue of `w(U)` to the nearest `p`-th root
  of unity. Because of the fixed derivation of `w^p=1`, the rounding radius
  `r(delta)` tends to `0`.
- `c_p = sin(pi/p)`.

## (A) Atomic Morita Return is two-valued and equals collapse

For `(Gamma,w)`, the following are equivalent.

1. **(a)** AMR holds with some modulus `eta(delta)->0`, as in
   `atomic-morita-return-kills-finite-order-mf-mark` (AMR1).
2. **(b)** There is one `delta_1>0` such that every operator-norm
   `delta_1`-model has every nontrivial rounded spectral projection `p_U=0`.
3. **(c)** `w in Rad_MF(Gamma)`.

**Consequences.**
- The modulus in AMR is two-valued. Only the existence of one scale with
  `eta<1/3` carries any content, and at that scale the hypothesis says
  "`p_U=0`".
- For `Gamma=Delta=St_20(L_(F_2)(1,2))` and `w=z=x_13(s_1t_1)`,
  `binary-leavitt-atomic-morita-return` (BLAMR) is **equivalent to the goal
  `property-t-free-leavitt-full-mf-radical` verbatim**, because `z` normally
  generates `Delta`.
- Its remark "the carrier is prescribed, so the zero-carrier shortcut is
  unavailable" is correct, but it does not make BLAMR a decomposition. Zero
  *coefficient operators* are admissible at every scale above `delta_0`,
  where the step modulus is `1`. Below `delta_0` the atom is itself zero.

## (B) The prescribed-carrier HS decoder equals HS marked collapse

In `affine-leavitt-prescribed-root-spectral-carrier-decoder`, (APC3) with some
`omega->0` is equivalent to

```text
||w_A(U)-I||_2 <= eta(delta),     eta(delta)->0,          (ADI3)
```

that is, to the target of `affine-leavitt-decoder-interface-is-mark-collapse-equivalent`.
- **Converse direction.** Take `S_i=T_i=0`. They are admissible with
  `omega=(eta+kappa)/(2 sin(pi/p))`, because (APC1) and (APC4) force
  `tr(P)^(1/2) <= (eta+kappa)/(2 sin(pi/p))`.
- **What this refutes.** The node's sentence "The claim is therefore a genuine
  nonvacuous root-to-coefficient extraction target" is false as a
  decomposition claim. The prescribed carrier only moves the vacuity from `P`
  to the operators.

## (C) The corona coefficient-module decoder equals emptiness of its premise

Fix `(R,n,i,j,r_0)` with a binary Leavitt family in `R`. Then
`corona-coefficient-module-decoder` for this datum is equivalent to:

```text
no norm-corona representation rho of E_n(R) has rho(x_ij(r_0)) != 1.   (NS)
```

- **Forward.** The unital ring homomorphism `R -> End(P_rho)` and
  `corona-projective-hilbert-hotel-cancellation` force `P_rho=0`. That
  contradicts the nonzero carrier of
  `finite-root-windows-share-one-reducing-corona-carrier`.
- **Converse.** Vacuous.
- **For the literal datum.** `R=L_(F_2)(1,2)`, `n=20`, root `x_13(q)`, and the
  same statement for whichever group (`E_20(R)` or `Delta`) the route feeds.
  Here `(NS)` is corona invisibility of the marked root, which is
  `Rad_MF`-membership of that root. The root normally generates, so (NS) is
  total MF collapse of that group. So the ⚑ last-missing hole of
  `property-t-free-leavitt-via-corona-module-decoder` is the goal itself,
  restated.
- **The other inputs.** The remaining prerequisites of that route are the
  carrier theorem, branch faithfulness and saturation. They play no role in
  the forward implication beyond supplying `P_rho != 0`.

## (G) The general lemma and criterion (NV)

**General lemma.** Let `H` be a hole of the form "for every model `M` in a
class, a witness of type `W` exists on a carrier `P(M)`". Suppose:

- a **gap lemma** shows that no witness of type `W` with defect below `g>0`
  exists on a nonzero carrier; and
- a **trivial witness** (zero operators) has defect bounded by a function
  `f(P)` that tends to `0` with the carrier.

Then `H` is equivalent to "the carrier vanishes uniformly", in whatever norm
`f` uses. Such an `H` is never a proper intermediate step toward that
vanishing.

**Criterion (NV).** A prerequisite decomposes the goal only if its witness
type is **inhabited on some nonzero carrier by some model of the class**, for
example by an exact finite model of a finite fragment. Equivalently, its
output must be a finite-matrix inequality that nonzero examples can satisfy
or violate. Examples are (ALG1), (ARL2), or the payment dichotomies in the
format of `mf-radical-words-have-linear-certificates`.

**Where this class dies.** Every "decode the Leavitt arrows on the carrier"
proof must, on every nonzero carrier, output operators that cannot exist:
- the invariant (ALG1) gives defect at least `1/3` in operator norm;
- (ARL2) gives `tr(P)<=3 omega` in the HS norm;
- Hilbert-hotel cancellation gives the exact corona version.

So the construction step is a proof by contradiction from a surviving model,
and that is the goal. This holds for both ways of phrasing such a decoder:
- an existential decoder is target-equivalent by (A)–(C);
- an explicit decoder, meaning functorial fixed group-algebra formulas, is
  target-equivalent for the same reason. It is also refuted outright on the
  regular marked corner by
  `fixed-group-algebra-polynomials-cannot-supply-atomic-return`.

## Frontier classification of the goal cone

**Class (A): gap-refuted and target-equivalent.** None of these is a
decomposition step.
- `corona-coefficient-module-decoder`, by (C).
- `binary-leavitt-atomic-morita-return`, by (A). The same holds for
  `binary-leavitt-three-row-atomic-compiler` via
  `atomic-three-row-compiler-is-prototype-gap-equivalent`.
- `affine-leavitt-prescribed-root-spectral-carrier-decoder`, by (B).
- `coherent-heisenberg-multiplicity-decoder`, by
  `coherent-heisenberg-decoder-is-marked-nonhyperlinearity`.
- `opnorm-leavitt-coarse-fine-return-row`. Its output row is refuted on every
  nonzero carrier by `rank-deficient-return-row-has-operator-norm-one`, so the
  same general lemma applies.

**Class (B): semantic holes implied by the target and inhabitable.** These
pass (NV).
- The arbitrary-profile cross-Gram positivity
  `binary-leavitt-arbitrary-profile-native-cross-gram`. Positive Gram mass is
  satisfiable on nonzero carriers.

**Class (C): syntactic or combinatorial holes.** These pass (NV).
- `binary-leavitt-bounded-area-chromatic-code`, a uniform area bound.
- Word-level linear certificates.

Work on the goal should therefore go to classes (B) and (C), or to
finite-matrix payment inequalities, and not to further constructions of
Leavitt arrows on a surviving carrier.
