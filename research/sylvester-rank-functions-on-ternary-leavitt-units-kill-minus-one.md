---
rg: 2
id: sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one
kind: claim
title: Every Sylvester rank function on the ternary Leavitt unit group algebra kills one minus the central involution
refuted_by:
  - ternary-leavitt-units-have-a-nontrivial-char-three-rank-model
distinct_from:
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that is the binary statement over F_2, where there is no central involution and the defect is the two-root product; this is the ternary statement over F_3 about 1 - [z]
  ternary-leavitt-units-have-a-nontrivial-char-three-rank-model: that asks for a matricial rank model and refutes this; this is the abstract No branch, stronger than triviality of matricial models
  ternary-anti-central-unit-class-is-nonpositive: that is the counterexample, failure of the rank condition on S_-; this is only absence of Sylvester rank functions on S_-, which that implies, and they coincide exactly when ternary-anti-central-states-give-sylvester-rank-functions holds
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`, `z = -1` and `S_- = eps_- F_3[G]` with `eps_- = (1 - [z])/2`.
Every Sylvester matrix rank function on `F_3[G]` has `rk(1 - [z]) = 0`.

**Equivalent forms** (artifact Section 4.4).
- `S_-` has no Sylvester matrix rank function `N` with `N(eps_-) = 1`.
  - A rank function with `rk(eps_-) = t > 0` gives `N(X) = rk(eps_- X)/t` on `S_-`.
  - Conversely `rk(X) = N(eps_- X)` extends a normalized `N` on `S_-`, because `eps_-` is central.
- `G` has no anti-central model in an abstract `F_3`-rank algebra. In one direction this is Corollary 7.2
  of the `w3-gate-char3` artifact (`S_-/ker N` is such a model). In the other, a model pulls back along
  `F_3[G] -> B`.

**What it gives and what gives it.**
- **It gives the matrix "No" branch.** It implies that every characteristic-three matrix rank model of `G`
  is trivial, so `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model` fails. A nontrivial
  matrix model moves `z` and pulls back to `rk(1 - [z]) > 0`.
- **It follows from the counterexample.** `ternary-anti-central-unit-class-is-nonpositive` implies it, and
  so does the corner equation: no state means no rank function.
- **With (U1) it is the counterexample.** Together with `ternary-anti-central-states-give-sylvester-rank-functions`
  it gives `ternary-anti-central-unit-class-is-nonpositive`, through the route
  `ternary-counterexample-from-rank-kill-and-state-realization`.

*Verification by `w3-vf-linear` (2026-09-12), Section 25 of
`research/artifacts/w3-vf-linear-verification-2026-09-12.md` (1eec8d6307): PASS on both equivalences.
The claim itself stays OPEN.*
- *Normalization and extension: `X -> eps_- X` is a unital ring map because `eps_-` is central, and
  `1 - [z] = 2 eps_-` with `2` a unit.*
- *Abstract models: a model with `sigma(z) = -1` pulls back to a Sylvester function with value 1 on
  `1 - [z]`; the converse is Corollary 7.2.*

**Scope warning.** The landed characteristic-two triviality nodes (matrix-unit, unipotent-valued,
flag-preserving) and the hard R4 mechanisms are matricial, in characteristic two. None of them is
evidence here until it has been scope-checked for abstract rank algebras in characteristic three.

## Attempts

- 2026-09-12 `w3-strategist-neg`: opened after `w3-gate-char3` showed that the gate equivalences, the
  corner kill and the Haar law hold for abstract rank algebras (its artifact, Section 7).
- **The signed Thompson subgroup reduces to `V` (w5-c3-signed-thompson, c4f44ada52;
  `research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md`).**
  - **Subgroup form.** Restricting to `E ⋊ V`, which contains `z`, preserves `rk(1 - [z]) > 0`.
  - **Equivalence.** Over any field, `K[E ⋊ V]` carries a rank function moving `z` iff `K[V]` carries a
    non-augmentation one (`signed-thompson-z-moving-rank-functions-match-v-rank-functions`). The proof uses only
    Sylvester axioms, simplicity of `V` and transitivity on clopens, so it holds in the abstract setting of this
    node.
  - **Route.** `ternary-units-kill-minus-one-via-thompson-v-augmentation` derives this claim from
    `thompson-v-ternary-rank-functions-are-augmentation`.
  - **Where it stops.** That prerequisite makes `V` nonsofic, which is open and at least as hard. A proof of this
    claim that does not settle `V` must use elements of `G` outside `E ⋊ V`: the Hadamard unit `h`, root elements
    `x_12(r)`, compressors, or the `SD16` and `GL_2(F_3)` blocks.
- **Sofic subgroups and locally finite HNN data carry anti-central rank functions (w5-c3-submult, 5281756de8;
  `anti-central-sofic-data-cannot-force-defect-submultiplicativity`).**
  - **Sofic subgroups.** Every sofic `S <= G` containing `z` has an anti-central rank model over `F_3`. Linearize a
    sofic approximation and compress by `f = 2(1 - tau(z))`. On finite subgroups it realizes the regular profile
    `rk(alpha) = dim(alpha F_3[K] eps_-)/(|K|/2)`, with `rk(1 - [z]) = 1`.
  - **HNN data.** The same holds for every HNN datum over a locally finite base containing `z`, with letters for
    arbitrary units.
  - **Consequence.** A proof of this claim that consumes only `F_3[S]` for one sofic `S`, or only relations of a
    locally finite subgroup plus single conjugations, fails. On the cylinder frames these models have
    `rk(D_A) = 5/9` and exactly multiplicative disjoint defects, so the descent route through
    `ternary-disjoint-cylinder-defects-strictly-submultiplicative` must also use a nonsofic configuration.
- **Characteristic-three descent machinery, scoped for abstract rank functions (w5-c3-descent;
  `research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md`).**
  - **Gap, established** (`ternary-anti-central-two-root-defect-has-a-uniform-gap`). Over anti-central Sylvester
    rank functions, `min N(D)` is attained and lies in `(0, 2/3]`. No fixed-point-free quotient or finite
    generation is needed.
  - **Descent, established** (`ternary-cylinder-defect-products-descend-in-sign-sectors`).
    * `f(k+1) <= (2/3) f(k)`.
    * `f(k+1) >= c_3 N(Q_B P_k)`, and `N(Q_B P_k)` is at least half of the even-sector part.
    * The characteristic-two lower bound and near-minimal multiplicativity do not port in either scope (artifact
      Section 4).
  - **Route.** `ternary-rank-kill-via-anti-central-defect-deficit` derives this claim from the open
    `ternary-anti-central-disjoint-defects-have-a-strict-deficit`: disjoint defect products are nonzero, and
    compressing along `Q_B D_A` lowers the defect by a fixed factor. An attained minimizer contradicts it.
- **Outside E ⋊ V is one element (w5-c3-outside, bdc24926b1, c69a5bda20;
  `research/artifacts/ternary-minus-one-gate-outside-signed-thompson-2026-09-12.md`).**
  - **Generation, established** (`leavitt-prime-field-units-generated-by-v-and-one-transvection`).
    `G = ⟨V, x⟩` with `x = 1 + s_00 t_01`. Nonidentity elements of disjoint transvection trees are all conjugate
    to `x`.
  - **Support conjugacy, established** (`leavitt-semisimple-torsion-units-conjugate-iff-same-support`).
    Semisimple torsion units are conjugate iff their spectral supports agree. So `h ~ wd in E ⋊ V`, and every
    non-central involution is `~ τ_([0])`. The order-8 Singer elements of level-one `GL_2(F_3)` are not conjugate
    into `E ⋊ V`.
  - **Firewalled.** Both results give only single-conjugation symmetries, and the anti-central HNN models above
    realize them. A proof avoiding the V gate must use as a factor a depth-mismatched transvection pair such as
    `T_(0,1)`, `T_(1,00)`, whose product contains the infinite-order unit `1 + s_0 t_00`.
  - **Open.** `v-detecting-rank-functions-extend-to-ternary-leavitt-units`. With it, this claim becomes equivalent
    to the V gate (route `v-augmentation-from-minus-one-gate-and-extension`). Where it dies:
    - pullback: `G` is Kazhdan and `V` is Haagerup, so every homomorphism `G -> V` is trivial;
    - `x` has no permutation model.
