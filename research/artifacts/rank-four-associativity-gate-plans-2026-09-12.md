# Rank-four associativity: decisive plans for the two-root gate

Lane `w3-strategist-gate`, 2026-09-12. Now the lead lane of family R4.

This artifact turns the state of the R family into plans for the rank gate
`rank-models-of-el3-satisfy-the-two-root-identities`. The gate says that `N_23 N_12 = 0` in every
characteristic-`p` rank model of `EL_3(R)`, where `R = L_K(1,2)` and `K` is finite. Closing the gate in
either direction settles `leavitt-el3-rank-models-over-finite-fields-are-trivial`, and with it
`non-linear-sofic-group`.

**Lead pass (family R4).** Section L and the passages marked *(lead)* replace the first landing
(5b46fe59c5). In short:
* **Mechanism dies.** The mechanism listed for Plan 1 fails, because all of its relations lie in
  `U_4(R)` (L7).
* **Index-3 placement fails.** The placement the orth lane fixed holds only modulo block-support defects
  (L3).
* **Route survives.** The route is still valid, and it is equivalent to the gate.
* **Endpoint.** Completeness is not needed, and approximate relations suffice (L1).
* **Calibration corrected.** An exact family inside `F_2[R^x]` would give a Gottschalk counterexample. It
  would not be an absurdity (L4a, corrected by w4-vf-gate).
* **Live questions (current).**
  * **Strict deficit, both characteristics.**
    * **What is established.** The defect gap and two-sided descent hold for abstract Sylvester rank
      functions: in characteristic two for all of them, and in characteristic three for the anti-central
      ones (L9b).
    * **What would close the gate.** A strict deficit `theta < 1`. In characteristic two this is
      `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (L5); in characteristic three it is
      `ternary-anti-central-disjoint-defects-have-a-strict-deficit` (L9b). In characteristic two the weaker
      distortion input of L5 would also do.
  * **Constraints on any proof** (L5, L7). It cannot come from any of these:
    * relations of locally finite subgroups;
    * single conjugations of locally finite data;
    * finite-subgroup rank calculus;
    * witnesses from rank-modelled subgroups off the cylinder set;
    * relations of any sofic subgroup containing both frames (w5-sub-fock, verifier PASS).

    It has to use relations beyond those shapes: straddling units as factors in a nonsofic configuration,
    properties that no rank model has, or global inputs such as corner locality.
  * **Cohn coefficients** (L8). This question lies between the V gate and the binary gate, so it adds no
    new decisive input.
  * **One shared input** (L5, L8). The Toeplitz form of the descent line and the Cohn reduction through
    `binary-jacobson-el3-rank-radical-is-the-finitary-kernel` both need `EL_3(J)`, `J = F_2<s0, t0>`, to be
    nonsofic. Its soficity is undecided on main. Nonsoficity is necessary for either route and proves
    neither. The Jacobson claim implies nonsoficity, since a sofic group has a faithful permutation model,
    and no converse is known. A nonsofic `EL_3(J)` only removes the firewall without giving a deficit
    (w4-vf-gate check).
  * **Wave 7 lanes on these inputs** (started about 20:45; verifier w4-vf-gate unless noted).
    * w7-el3j-sofic decides the shared input. `EL_3(J)` maps onto `EL_3(F_2[z, z^-1])` with a locally
      finite kernel and a residually finite quotient, so the lane first checks whether it contains `V`
      or another group of unknown soficity.
    * w7-sub-multiletter works on L1 SUB from the multi-letter inputs only: V's multiplication table on
      depth-changing letters, commutation of disjointly supported depth-changing letters, and the
      Toeplitz quarter.
    * w7-sylv-global (verifier w4-vf-linear-b) works on the Sylvester counterparts of the descent line on
      `F_2[R^x]`: `sylvester-leavitt-kazhdan-fixed-ideals-are-global` and
      `sylvester-near-minimal-leavitt-defects-are-multiplicative` (both OPEN).
    * w7-v-cycle-c2 and w7-v-cycle-c3 (verifier w3-vf-linear) work on the V gate upstream of L8, through the
      open order-char cycle law at `p = 2` and `p = 3`.

Commit hashes below are the ones reported by the landing lanes. Node ids are the stable references.

## The opening the finished lanes leave

Two established results frame the problem.
* By `leavitt-isometry-commutators-constrain-el3-rank-models`, the gate amounts to assembling an order-two
  Leavitt family in a corner.
* By `scalar-two-root-rank-data-cannot-force-the-identity`, rank values alone do not suffice.

By Khanh--Thanh, `R^x = EL_n(R)` for every `n >= 2` (`leavitt-gl-equals-el-and-perfect-unit-group`), so
every model of `R^x` is also a model of `EL_4(R)`. *(lead)* This adds coordinates, not relations. The
first landing claimed that the rank-3 analysis "cannot see" these identities. That claim was wrong.

## Plan 1: the four-index Cuntz assembly

Node `rank-four-isometry-relations-give-corner-cuntz-family`, route
`leavitt-el3-triviality-via-rank-four-cuntz-family`.

**Claim.** If the block defect `D` is nonzero, then some nonzero corner holds an order-two Leavitt family.
Such a family is excluded (L1). So `D = 0`, and the model is trivial.

*(lead)* **The listed mechanism dies (L7).** The fixed placement is circular (L3).

## Plan 2: the Heisenberg centre pairing

Node `heisenberg-centre-pairing-constrains-two-root-defect`.

*(lead)* **Dead as written (L7).**

## Plan 3: the algebra dichotomy

Node `leavitt-unit-linear-soficity-is-ring-rank-approximability`.

*(lead)* **Collapsed.** w4-r4-approx (b7b0e9d387, 9930bb89f5) shows that the right-hand side is false:
every unital map `L_K(1,d) -> M_n(k)` has a multiplicativity defect of at least `1/3` on one of three
pairs. Moreover `rk(1 - st) = rk(1 - ts)` exactly. So the node only restates "`R^x` is not `F_p`-linear
sofic".

## Ranking (lead pass)

1. The strict deficit `theta < 1`, in characteristic two (L5) and characteristic three (L9b), under the
   constraints of L4, L5 and L7. The Cohn question (L8) lies between the V gate and the binary gate.
2. The Plan 1 route: valid and equivalent to the gate. Its mechanism and placement are dead.
3. Plans 2 and 3: dead or collapsed.

## L. Lead integration (family R4)

### L1. Target: approximate relations in one corner

**Canonical endpoint.** `toeplitz-isometry-defects-have-total-rank-at-least-one` (w4-r4-approx). For every
Sylvester matrix rank function, and all `S_0, S_1, T_0, T_1` in `eAe`,

```text
rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0) .
```

**Exact form.** `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple` (w4-r4-corner, 5d14c96d85).
w4-r4-complete retired its own duplicate (b09f639b5d).

**Verification.** w4-vf-gate: PASS, with three independent derivations agreeing (e4d7e1c7fa).

**Consequences.**
* Check (ii) is not needed.
* It is enough to give definitions whose three defects sum to less than `rk(e)` at a single finite stage.

### L2. Logical status

The claim's conclusion is impossible in every rank ultraproduct. So, given the established nodes, the
claim is equivalent to the gate. For exact relations, positivity of `e` comes for free (w4-r4-corner).
All the weight falls on the construction.

### L3. Candidate placements, and why both are circular

**Baseline.** In `F_2[R^x]`, put `tau(a) = (x_12(a) - 1)(x_21(1) - 1)`. The linear extension
`pi : F_2[R^x] -> M_3(R)` sends `tau(a)` to `a E_11`. The resulting candidate is the matrix-unit
extraction. Every relation it needs is `sigma` of a nonzero element of `ker pi`, and forcing those
elements to vanish is the gate itself. (Verifier: PASS.)

**Index-3 placement.** w4-r4-orth (fcffe16327), `index-three-corner-placement-holds-only-modulo-two-root-defects`.
* **Definition.** `S(b) = n_31(b) n_13(1)` and `T(a) = n_34(a) n_43(1)`. Let `e` be the range idempotent
  of `n_31(1) n_13(1)`, and put `S_j = e S(s_j) e`, `T_i = e T(t_i) e`. In honest models this is the
  index-3 corner family, with `e = E_33`.
* **Exact identity.**
  `T(a) S(b) = n_31(ab) W n_13(1) + Delta_row + Delta_rev`, where
  `W = X_41(b) X_34(a) X_31(b) X_43(1)`, `Delta_row` carries the same-row product `n_31(b) n_34(a)`, and
  `Delta_rev` carries the reversed product `n_41(b) n_34(a)`.
* **Verdict.** Both deviation terms are block-support failures in `ker pi`, so the placement has the L3
  shape. Replacing index 4 by index 2 gives the same identity inside `EL_3`, so the fourth index adds
  nothing here. The cross term `T(t_1) S(s_0)` is nonzero in the regular representation of `SL_8(F_2)`,
  so the joint Leavitt relations must enter.
* **Consequence.** Check (i) fails for both admissible placements.

### L4. Calibrations

**(a) Kaplansky and Gottschalk (corrected by w4-vf-gate, §1.8 of `gk-vf-gate-verification-2026-09-12.md`).**
* Suppose the three relations of L1 held, with `e != 0`, inside `F_2[R^x]` itself. Then `F_2[R^x]` would
  not be directly finite. That refutes Kaplansky's direct finiteness conjecture for `R^x` in characteristic
  two.
* Through `nonsurjunctive-from-stable-finiteness-failure`, this gives a **Gottschalk counterexample**. That
  is a payoff, not an absurdity.
* The first version said instead that Elek--Szabo would make `R^x` non-sofic. That adds nothing, because
  `R^x` is already nonsofic on main (`openai-leavitt-unit-nonsofic`).
* So this is a marker for an outcome, not a firewall. The constraint applies to (i) and (iii) jointly:
  (i) may be ring identities, provided that `e != 0` is certified through the rank on `M`.

**(b) Test bed.** Theorem 3 of `el3-two-root-self-similarity-2026-09-12.md` gives models with
`rk(N_23 N_12) = 2/9` over coefficient rings that have rank models. If a proof of positivity uses only
Steinberg relations and rank, the chosen `e` must have positive rank in those models.

### L5. Defect gap established; the descent cannot finish

w4-gate-descent: `leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`,
`nested-two-root-defect-pieces-decay-geometrically-both-ways`,
`near-minimal-defect-models-have-multiplicative-cylinder-defects`, and the artifact
`two-root-defect-descent-gap-2026-09-12.md`.

* **Gap.** There is a constant `c_0 > 0` with `c_0 rk(1-f) <= rk((1-f) D_A) <= rk(1-f)/2`, where `fM` is
  the fixed right ideal of `sigma(R^x)`. The constant `c_0` is not explicit.
* **Descent.** For disjoint cylinders, `c_* f(k) <= f(k+1) <= f(k)/2`. The pieces at least halve at every
  step, so there is no limit corner, and the finish the first version proposed has nothing to act on.
* **Commits reported by the lane.** Gap e24abed257; descent and near-minimal models 3116be756a; open
  target 015be9163a.
* **Live question.** Open node `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, with route
  `leavitt-rank-triviality-via-strict-defect-submultiplicativity` into `non-linear-sofic-group`. Find an
  operation on fixed-point-free models that lowers the normalized defect by a fixed factor. The natural
  source, per w4-gate-descent, is the halving relation
  `iota_A(x_12(1)) = (1 + S[A00]T[A100])(1 + S[A01]T[A101])`. It gives
  `D_A = (1+b+d)X + (1+a+c)Y + XY + cb + da`, where `X` and `Y` are the child defects. No bound has been
  extracted yet.
  * Strict submultiplicativity would suffice: `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with `theta < 1`.
  * Honest tensor configurations attain `theta = 1`, so a proof must use the Leavitt relations.
  * By L7, it must also use units outside `iota_A(U_3) x iota_B(U_3)`.
  * **Halving does not give `theta < 1`** (w4-r4-orth, f25ccc5958; artifact
    `rank-four-orthogonality-check-2026-09-12.md`, Section 5). Both the prepend form
    `iota_A(Delta(g)) = iota_(A0)(g) iota_(A1)(g)` and the swap `iota_A(w)` live in the locally finite
    group `(iota_(A0)(UT_3(R)) x iota_(A1)(UT_3(R))) x| <iota_A(w)>`. Its regular rank model has
    `delta = 3/8` and `f(2) = delta^2`, so `theta = 1` there.
  * **Untested sources.** Opposite roots at a child cylinder, the compressors, the nine-leaf
    configuration, and the block root groups of `GL_2(R)` normalized by the torus
    `iota_0(R^x) x iota_1(R^x)`.
  * **Commutant independence** (w4-sub-weyl, family SUB, 6ecf8dd0a;
    `near-minimal-defects-are-rank-independent-of-cylinder-commutants`; verifier PASS §11.1). In a
    nontrivial fixed-point-free model, let `X` commute with `sigma(iota_A(R^x))`. Then
    `c_* rk(X) <= rk(D_(AP) X) <= delta - c_*(1 - rk X)` for every proper prefix `P`. So near-minimal
    defects are rank-independent of the whole cylinder commutant.
    * Lead spot-check of the triangular count: pass. `rk(TM) >= rk(TK) + rk(J) - rk(K)`, with
      `K = r.ann(X)` and `J = TM + K`, and `rk(J) - rk(K) = rk(TX)`.
    * **What it means for L5** (lead, corrected). Defects on disjoint cylinders lie in that commutant,
      so at near-minimal defect `rk(D_A D_B)` is about `delta^2`, which is `theta = 1`.
      * This is a theorem about near-minimal models, not a counter-model. A proof of `theta < 1` has
        to show that near-minimal models do not exist, which is a proof by contradiction of the L2
        shape.
      * The earlier sentence here said that any proof "has to pass through operators outside the
        commutant". That was a heuristic stated as if it were a firewall.
      * The four untested sources above do lie outside the commutant.
  * **Weaker sufficient input.** Route `leavitt-rank-triviality-via-commutant-rank-distortion` into
    `non-linear-sofic-group` (e2e57e9f5). It requires:
    * the OPEN `some-commutant-element-distorts-defect-range-rank`;
    * the ESTABLISHED `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant`;
    * the defect gap.

    `commutant-distortion-from-strict-defect-submultiplicativity` derives distortion from strict
    submultiplicativity. So distortion is a weaker decisive input for the descent line than
    `theta < 1`.
    * **Firewall for distortion.** Node `commuting-subgroup-witnesses-cannot-distort-defect-ranges`, from
      lane w5-commutant-distort; established, with verification requested from w4-vf-gate.
      * **Result.** Take `L <= G_U` infinite, locally finite and containing the frame's transvections. Take
        `Lambda <= G_(U^c)` with some characteristic-two rank model `rho`. Then `sigma_L (x) rho` is a
        nontrivial fixed-point-free model of `L x Lambda`, and `rk(D_Theta Z) = delta rk(Z)` for every
        matrix `Z` over `sigma(F_2[Lambda])`.
      * **Consequence.** Witnesses from a rank-modelled subgroup supported off the cylinder set never
        distort, even infinite-order ones such as `iota_A(w_23) iota_(A1)(w_12)`. A distortion proof has to
        use one of three inputs:
        * straddling units as factors, not only as conjugators;
        * properties of `Lambda` that no rank model has;
        * global inputs such as corner locality, globality or compactness.
  * **Two more firewalls** (family SUB; both established, with verification requested from w4-vf-gate).
    * `finite-subgroup-data-cannot-force-defect-submultiplicativity` (w4-sub-weyl).
      * The regular assignment `rk_reg(alpha) = dim(alpha F_2[K])/|K|` is a rank function on every
        locally finite subgroup and is invariant under conjugation by every unit.
      * It gives `rk_reg(D_(A_1)...D_(A_k)) = (3/8)^k`.
      * So `theta < 1` does not follow from finite-subgroup rank calculus, relations inside finite
        subgroups, or rank equalities between conjugates. That covers Weyl elements, the halving
        sheets, prefix doubling, the swap, and conjugation by torus units or compressors.
    * `locally-finite-hnn-data-allow-independent-cylinder-defects` (w4-sub-adversary).
      * Take a countable locally finite `L <= R^x` and letters `t_u` that act as conjugation by
        arbitrary units `u` on `L cap u^-1 L u`.
      * The group they generate has a genuine fixed-point-free rank model with `rk(D_A) = 3/8` and
        independent defects, so `theta = 1`.
    * **Consequence for the untested sources.** Compressors, nine-leaf units and `GL_2` block root
      groups cannot give `theta < 1` when they enter only through single conjugations of locally finite
      data. A proof has to use relations of `R^x` that do not follow from locally finite subgroup
      relations plus single partial conjugations.
  * **Sofic firewall and the Toeplitz input** (lane w5-sub-fock, family SUB; 2cf82d01d7, 0d600e4efd;
    artifact `fock-toeplitz-input-and-sofic-independence-2026-09-12.md`; verifier PASS §28).
    * `sofic-subgroups-carry-independent-cylinder-defects`. Let `H <= R^x` be sofic and contain the
      frames `iota_(A_i)(D_8)` at disjoint cylinders. The permutation model of a sofic approximation is
      free on every finite subgroup, gives `rk(D_(A_1)...D_(A_k)) = (3/8)^k`, and has no fixed vector
      once `H` has an element of infinite order.
      * **Consequence.** Both firewalls above extend from locally finite data to every sofic subgroup,
        infinite-order factors included. A relation-only `theta < 1` has to use a nonsofic subgroup
        containing both frames, and it proves that subgroup nonsofic.
      * **Not covered.** The global inputs of the route (the defect gap, near-minimal multiplicativity)
        do not restrict to subgroups.
    * `toeplitz-pair-and-weyl-elements-generate-jacobson-el3`.
      * The Toeplitz pair `x_12(t0)`, `x_23(s0)` generates a dihedral group of order 8 inside an
        order-128 unitriangular group. So the exact Toeplitz commutator is finite-subgroup data, and the
        quarter of `natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter` measures
        truncated-shift realizations, not rank models.
      * With `EL_3(F_2)` the pair generates `EL_3(J)`, `J = F_2<s0, t0>`. With the constant root groups
        `x_ij(R_0)` it generates `R^x`. The same holds over `F_3`.
    * **Where this meets L8** (lead).
      * The smallest two-cylinder configuration in which Toeplitz data can bite is
        `iota_A(EL_3(J)) x iota_B(EL_3(J))`, which is sofic iff `EL_3(J)` is.
      * The Jacobson claim of L8, `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`, also makes
        `EL_3(J)` nonsofic.
      * So the Toeplitz form of the descent line and the Cohn reduction need the same input: `EL_3(J)` is
        not sofic. If `EL_3(J)` is sofic, the Jacobson claim is false and Toeplitz-plus-Weyl data at two
        cylinders cannot force `theta < 1`. The next configuration, with the constant root groups, is
        already all of `R^x`, so a relation-only proof would isolate no smaller certificate.
      * The soficity of `EL_3(J)` is undecided on main: locally finite kernel, residually finite
        quotient, and the literature check owed in L8 still stands.
      * **Archive context** (09-08 Jacobson region; lead summary).
        * `binary-jacobson-core-is-weakly-sofic-with-fd-head-radical`: `EL_28(J)` is weakly sofic by
          Glebsky's extension theorem, and every finite-dimensional unitary representation of it kills the
          finitary kernel. The block subgroup `EL_3(J)` is therefore weakly sofic.
        * `binary-jacobson-mf-radical-dichotomy`: the MF radical of `EL_5(J)` is `1` or the finitary kernel.
        * `leavitt-first-offdiagonal-core-is-marked-non-lef`: the Toeplitz core over `R` is not LEF.
        * So weak soficity holds, exact finite images of `EL_28(J)` erase the head, and soficity is the
          approximation notion still open.

### L6. Status

| item | lane | status |
|---|---|---|
| (i) three relations | w4-r4-orth | placement fixed and circular (L3); positivity established (row iii); redirected to L5; halving obstruction landed (f25ccc5958); finishing |
| (ii) completeness | w4-r4-complete | not needed. Transport formula `leavitt-completeness-transport-formula-for-root-data` established and firewalled (it lives in `U_3(R)`). Opened L8 (b09f639b5d) |
| (iii) positivity | w4-r4-corner | free for exact relations; for w4-r4-orth's placement, established in characteristic two by `opposite-unit-root-product-vanishes-only-for-trivial-models` (ef454c9283; lead spot-check of the braid step passes); only the L3 deviation terms remain open; route framing merged (b0d955566e) |
| endpoint | w4-r4-approx | canonical form established; verifier PASS |
| block to whole group | w4-r4-corner | `el4-model-trivial-on-one-unit-root-element-is-trivial`; verifier PASS; required by the route |
| odd characteristic | w4-r4-adversary | `reversed-root-pair-identity-forces-root-squares-to-vanish` (9fd9898e8e); verifier PASS; used by the route |
| break the plan | w4-r4-adversary | mechanism dies (c6697aa47b; L7) |
| approximability node | w4-r4-approx | collapsed |
| Heisenberg node | w4-heisenberg | dead; firewall landed (f576dccf26); finished |
| defect gap and descent | w4-gate-descent | Established, verifier PASS: gap, two-sided descent, near-minimal multiplicativity. Open target: `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, with route `leavitt-rank-triviality-via-strict-defect-submultiplicativity` into `non-linear-sofic-group`. Lead spot-check of the route passes: `f(2) >= c_* delta >= delta^2/(1+eps)` contradicts `theta delta^2` once `eps < 1/theta - 1`. The verifier also passes it as a conditional route (§8.4): `theta < 1` holds uniformly over models, so the choice of near-minimal model cannot evade it |
| Toeplitz input and sofic firewall | w5-sub-fock (family SUB) | Established, verifier PASS §28: the Toeplitz pair is finite-subgroup data; `sofic-subgroups-carry-independent-cylinder-defects`; `toeplitz-pair-and-weyl-elements-generate-jacobson-el3`. Open input shared with L8: soficity of `EL_3(J)` (L5) |
| wave 7 input lanes | w7-el3j-sofic, w7-sub-multiletter, w7-sylv-global; w7-v-cycle-c2, w7-v-cycle-c3 (upstream of L8) | Started about 20:45; nothing landed yet. Targets: soficity of `EL_3(J)`; `theta < 1` from multi-letter inputs; the two OPEN Sylvester descent counterparts; the order-char cycle law at `p = 2, 3` (header) |
| verification | w4-vf-gate | Record: `gk-vf-gate-verification-2026-09-12.md`, Sections 1--10 (later sections, through §28, cover the SUB, characteristic-three and Cohn landings folded into L5, L8 and L9). §10 passes orth's halving obstruction. PASS on every established family node: endpoint, block triviality, reversed root, both firewalls, index-3 placement, completeness transport, defect gap, descent, near-minimal models, opposite-root positivity, approximability collapse. Corrections folded in: L4a, frames, odd characteristic. Plan 2 stays open with two overstatements (§1.7). No decision-level verdict |

### L7. The listed mechanism dies

**Abelian model.** w4-r4-adversary (c6697aa47b), `unipotent-frame-relations-cannot-assemble-corner-cuntz-family`.
* `g -> u^phi(g_12) v^phi(g_23)` on `F_p[C_p^2]` is a homomorphism of `U_4(R)`.
* It satisfies every listed relation.
* It has `rk(N_23 N_12) = (p-1)^2/p^2` and zero `x_14` data.
* Lead spot-check: pass.

**Locally finite firewall.** w4-heisenberg (f576dccf26), `unitriangular-data-cannot-assemble-corner-leavitt-families`.
* `UT_4(R)` is locally finite.
* Its regular rank model satisfies every `UT_4` relation and every rank that is invariant under
  conjugation.
* It has `rk(N_23 N_12) = 3/8`.

**Consequences.**
* A proof must use `sigma` on opposite root, Weyl or torus elements, jointly on a nonsofic subgroup,
  together with the rank of `M`.
* The Heisenberg plan dies the same way on `U_3(R)`.
* **Later results from other families** (both established; verified in `gk-vf-gate-verification-2026-09-12.md`).
  * **`binary-locally-finite-hnn-models-violate-two-root-identity`.**
    * **Result.** HNN extensions of a locally finite subgroup along single-letter partial conjugations
      carry characteristic-two rank models that violate the identity.
    * **Consequence for the gate.** Relations of locally finite subgroups, together with single
      conjugations by arbitrary units, cannot prove the gate. So "jointly" above has to mean relations
      that are not of this HNN shape.
    * **Overlap.** This overlaps `locally-finite-hnn-data-allow-independent-cylinder-defects` (L5), whose
      model already has `rk(D_A) = 3/8`. The steward may want a `distinct_from` line between the two nodes.
  * **`swap-group-cylinder-lift-trees-halve-but-never-refine`.**
    * **Result.** In every nontrivial characteristic-two rank model of the Leavitt units, swap-group lifts
      of cylinder projections halve exactly at every cylinder but never refine.
    * **Relation to L9(a).** It points the same way as the monotone rigidity recorded there.

### L8. Cohn coefficients (w4-r4-complete, open)

The node is `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`. It asks whether
`N_23 N_12 = 0` in every rank model of `EL_3(C)`, where `C` is the Cohn algebra `t_i s_j = delta_ij`,
without completeness.
* **`C` has no unital rank model.** `T_0 S_0 = 1` forces `S_0 T_0 = 1`, so `T_1 = 0`.
* **Pullback.** `R` is a quotient of `C`, and `EL_3(C) -> EL_3(R)` is onto. So every rank model of
  `EL_3(R)` pulls back to a rank model of `EL_3(C)` with the same `D`.
* **If the node is true,** it gives the binary gate.
* **If it is false,** completeness must enter any construction. It cannot enter through root data, since
  the transport formula lives in `U_3(R)`. It has to enter through units outside `U_4(R)`.
* **Reduction** (lane w4-cohn-el3, 013740e0d; route `cohn-el3-two-root-identity-from-jacobson-rank-radical`;
  verifier PASS as a conditional route, §14.3). The target follows from the OPEN
  `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`.
  * **The Jacobson claim.** Every characteristic-two rank model of `E = EL_3(J)`, with
    `J = F_2<S,T | TS = 1>`, kills `x_13(1 - ST)`. By the node's established dichotomy, the rank radical
    of `E` is either `1` or the finitary kernel `L = GL_fin(N x {1,2,3}, F_2)`.
  * **How the route uses it.** `S -> s_0`, `T -> t_0` embeds `E` in `G = EL_3(C_2)` and sends the head
    `x_13(1 - ST)` to a nontrivial element. The established
    `cohn-elementary-group-rank-radical-is-trivial-or-everything` then gives rank radical `G`. So every
    model of `G` is trivial, and every such model satisfies the identity.
  * **Strength marker** (lead; literature status not verified).
    * The Jacobson node already records that its claim makes `E` non-sofic.
    * `L` is locally finite, and `E/L = EL_3(F_2[z,z^-1])` is residually finite
      (`laurent-elementary-groups-are-residually-finite`). So the claim would give a non-sofic group
      with locally finite kernel `L` and residually finite quotient `E/L`.
    * Elek--Szabo's closure theorem covers amenable quotients, not amenable kernels. Check whether the
      kernel case is known before relying on this marker in either direction.
    * If soficity is closed under amenable kernels, the Jacobson claim is false. This route would then
      die, but the L8 target would be untouched.
* **Rank four.** Source: w4-cohn-el3, `thompson-v-lifts-into-rank-four-cohn-elementary-group`, established;
  verification requested from w4-vf-gate.
  * **The lift.** Thompson's `V` lifts injectively into `GL_2(C_2)` over the quotient `C_2 -> R`. The lift
    differs from prefix replacement only by finitary units. Since `V` is perfect,
    `phi(V) (+) 1_2 <= EL_4(C_2)`.
  * **Normal subgroups.** Those of `G_4 = EL_4(C_2)` are `1`, `K_4 = GL_fin(W x 4, F_2)` and `G_4`. So every
    nontrivial characteristic-two rank model of `G_4` is injective.
  * **Consequence.** The OPEN V gate `thompson-v-has-no-nontrivial-f2-rank-model` kills every rank model of
    `EL_4(C_2)`. Every rank model of `R^x = EL_4(R)` pulls back to `EL_4(C_2)`, so this gives a Cohn-level
    form of the binary gate. The direct implication from the V gate to the binary gate (`V <= R^x`, and
    `R^x` is simple) is not new.
* **Rank three** (w4-cohn-el3; verified in `gk-vf-gate-verification-2026-09-12.md`).
  * **Established:** `cohn-pair-compression-embeds-el-2n-into-el-n`. A Cohn pair compresses `EL_2n` into
    `EL_n`, so `EL_3(C_2)` contains every `EL_m(C_2)`, every `EL_m(J)`, and `V`.
  * **Established:** `cohn-elementary-group-is-not-lef`. `EL_3(C_2)` contains `EL_4(J)`. The finitely
    presented Steinberg cover of `EL_4(J)` kills the head root in every finite image.
  * **Route:** `cohn-coefficient-el3-two-root-identity-from-v-gate`. It derives the L8 target from the OPEN
    V gate, through the embedding of `V`, the rank-radical dichotomy and the rank-four lift.
  * **Where L8 sits** (lead). The target lies between the V gate and the binary gate: the V gate implies
    it, and it implies the binary gate by pullback along `EL_3(C_2) -> EL_3(R)`. So the route adds no new
    decisive input. It shows that the Cohn question is no harder than the V gate.
* **V gate firewalls** (lane w5-v-nonamenable; established, verifier PASS: w3-vf-linear §31 at 94f11d0bdc,
  artifact `thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md`). They constrain every
  proof of the V gate, which sits upstream of L8.
  * `sofic-configurations-cannot-force-v-rank-triviality`. For every sofic `K <= V`, sofic approximations
    give Sylvester rank functions on `F[K]` with `rk(1 - [g]) = 1 - 1/ord(g)` that satisfy every confined
    premise. So no argument confined to a sofic configuration forces the V gate.
  * `char-uniform-identities-cannot-force-v-rank-triviality`. The von Neumann rank on `C[V]` satisfies
    every premise whose identities already hold over a subring of `C`. So a proof in characteristic `p`
    must use a `p`-sensitive identity, such as `(1 - [s])^p = 0` for a clopen `p`-cycle `s`.
  * **Next step, open.** `v-rank-order-char-cycles-are-trivial-plus-regular`: the Jordan profile
    `rk((1 - [s])^j) = (1 - phi_V)(p - j)/p` for `1 <= j <= p` (range corrected by the lane after the
    restart). Only upper bounds are proved, and the lane records that the law does not imply the gate.
  * *(lead)* The first firewall is the V-side analogue of the sofic cylinder-defect firewall in L5. So a
    proof of either gate has to work in a configuration not known to be sofic.

### L9. Adjacent plans from w3-strategist-neg (tracked here; not an R4 lane)

Source artifact: `strategist-neg-counterexample-plans-2026-09-12.md`.

**(a) Covariant diagonal on the defect piece.** Node `leavitt-two-root-defect-piece-forces-covariant-diagonal`,
route `el3-rank-triviality-via-defect-piece-covariance`. w4-r4-adversary has been asked to attack it.
* **The endpoint is sound.** Suppose there were a `V`-covariant family of orthogonal idempotents with
  `e_w = e_(w0) + e_(w1)` and some `rk(e_w) > 0`. Then all proper cylinders would share one rank `c`,
  with `c = 2c`. `thompson-v-cantor-system-has-no-covariant-rank-model` excludes that. So, as in L2, the
  claim is equivalent to the gate, and its content is the construction.
* **The first lemma points away from orthogonality** (lead). Suppose the spans `V_(w,w')` have ranks.
  Transitivity gives them all one rank `c`. In a regular rank ring, `V_(w0,w') <= V_(w,w')` together
  with equal rank forces `V_(w0,w') = V_(w,w')`. So image spans are refinement-invariant and cannot be
  the `e_w`. Orthogonality is block support under another name, which is the L3 shape.
* **Kill test** (lead). Root elements at `(w0,w')` and `(w1,w')` commute, because `t_(w') s_(w1) = 0`.
  Finitely many of them generate an elementary abelian 2-group `H_0 x H_1`. In its regular rank model
  the two augmentation images meet in normalized rank `(1 - 1/|H_0|)(1 - 1/|H_1|) > 0`. So a proof of
  orthogonality must use `sigma` outside that locally finite subgroup (L7), most likely on the
  prefix replacements that do not preserve measure. That is also where the endpoint gets its
  contradiction.
* **Audit** (w4-r4-adversary; artifact `covariant-diagonal-plan-adversarial-audit-2026-09-12.md`).
  The claim is not refuted, and its route stays valid.
  * **Joins exist.** In a rank ultraproduct, every countable family of principal right ideals has a
    join in the lattice of principal right ideals, with rank equal to the supremum of its finite joins.
    Leastness is among principal right ideals only (verifier scope remark, §12.1). That settles the
    "if the spans have ranks" caveat above.
  * **The first lemma is automatic.** By `covariant-monotone-cylinder-families-in-rank-models-are-constant`,
    every covariant, refinement-monotone family of principal right or left ideals indexed by proper
    cylinders is constant. This holds in every rank model, whatever `N_23 N_12` is. Orthogonal cylinder
    families are monotone, so covariant orthogonal diagonals are zero. "Orthogonality is the missing
    input" therefore names the contradiction; it is not a step toward it.
  * **What the span coincidence gives.** If `N_(b,a1)(y) N_(a0,b)(z) = 0` for all coefficients on one
    frame of disjoint cylinders `(a0, b, a1)` (with `a ∪ b != X`, as in the node), then `sigma` is
    trivial. This is the known direction, that a nontrivial model violates the identity, now with a
    group-theoretic proof.
  * **Kill tests.** The join test fails. The Toeplitz test is consistent, because that algebra has no
    depth-changing units. The one remaining test is the gate itself.

**(b) Abstract Sylvester rank functions and characteristic three.** This bears on step (U2) of
`ternary-counterexample-from-rank-triviality-and-state-upgrade`. The table records what the landed
statements say. It is not a re-verification.

| node | abstract Sylvester rank function | characteristic three |
|---|---|---|
| `toeplitz-isometry-defects-have-total-rank-at-least-one` | stated for every Sylvester matrix rank function | yes |
| `el4-model-trivial-on-one-unit-root-element-is-trivial` | group-theoretic | yes |
| `reversed-root-pair-identity-forces-root-squares-to-vanish` | ring identity | yes |
| `opposite-unit-root-product-vanishes-only-for-trivial-models` | identity holds whenever `2 = 0`; positivity needs a faithful rank | no; characteristic two only |
| firewalls of L7 | counter-models into matrix algebras, so they bind in any rank setting | via the abelian model, stated for every `p` |
| defect gap, descent, near-minimal multiplicativity | transferred by w4-upg-audit (rows below) | no; characteristic two only |
| `sylvester-rank-functions-have-a-uniform-two-root-defect-gap` | every Sylvester matrix rank function on `F_2[R^x]` that moves a generator by `eta` has corner defect rank at least `c^Syl(eta)` | no |
| `corner-defect-killing-rank-functions-are-augmentation` | a Sylvester rank function that kills one corner defect is the augmentation rank | no |
| `leavitt-defect-descent-chain-holds-in-regular-rank-rings` | defect piece, gap, two-sided descent and near-minimal multiplicativity in every faithful regular rank ring | no |
| `regular-rank-ring-compressors-conserve-fixed-right-ideals` | compressors conserve fixed right ideals in every faithful regular rank ring | no characteristic stated |

**Update** (w4-upg-audit; all four nodes established, verification requested from w4-vf-gate).
* **What changed.** The first version of this table said that the gap, descent and positivity mechanisms
  were stated only for faithful rank ultraproducts. That is now stale in characteristic two:
  * the gap and positivity hold for every Sylvester matrix rank function on `F_2[R^x]`;
  * the descent chain holds in every faithful regular rank ring.

  So in characteristic two these mechanisms no longer depend on matrix ultraproducts.

  **Later** (lane w5-regular-rankfn; established, verified in `gk-vf-gate-verification-2026-09-12.md`).
  * **Result.** The gap and the geometric two-sided descent hold for every Sylvester matrix rank function
    on `F_2[R^x]` other than the augmentation rank, taken through its augmentation quotient.
  * **Nodes.**
    * `sylvester-leavitt-defect-gap-and-geometric-descent`;
    * `perfect-group-augmentation-quotient-ranks-are-fixed-point-free`: on a perfect group the quotient
      is fixed-point-free;
    * `sylvester-rank-functions-descend-to-quotients-and-compressions`: ideal quotients and commuting
      compressions of Sylvester rank functions are Sylvester rank functions.
  * **Consequence.** In characteristic two the regularity and faithfulness hypotheses are now gone as well.
    In both characteristics the gap and descent hold for abstract Sylvester rank functions (in
    characteristic three over the anti-central ones, as below), so they no longer need (U2). The strict
    deficits are still open in both characteristics.
* **What still holds.** The ternary route needs characteristic three, and none of these mechanisms has a
  characteristic-three counterpart yet. So (U2) is still open there.
* **Characteristic three, later landings** (another family; verified in `gk-vf-gate-verification-2026-09-12.md`).
  * **Established.** `signed-thompson-z-moving-rank-functions-match-v-rank-functions`: the signed Thompson
    group algebra has a rank function moving `-1` if and only if `V` has a non-augmentation rank function.
  * **Open target.** `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` is the Sylvester
    form of the ternary gate.
    * **Route.** `ternary-units-kill-minus-one-via-thompson-v-augmentation` derives it from the OPEN
      `thompson-v-ternary-rank-functions-are-augmentation`.
    * **Strength.** That input is at least as strong as `V` failing to be sofic.
    * **Consequence.** A proof that does not settle `V` must use elements of `G_3` outside `E x| V`.
  * **Open.** `thompson-v-carries-ternary-nonaugmentation-rank-function` follows from `thompson-v-is-sofic`.
  * **Converse route** (verified as a conditional route, §27.3 of `gk-vf-gate-verification-2026-09-12.md`).
    `v-augmentation-from-minus-one-gate-and-extension` derives `thompson-v-ternary-rank-functions-are-augmentation`
    from three inputs:
    * the minus-one gate;
    * the OPEN extension claim `v-detecting-rank-functions-extend-to-ternary-leavitt-units`;
    * the established augmentation-or-detecting dichotomy for simple groups.

    So, if the extension claim holds, the minus-one gate is equivalent to ternary V augmentation. In that
    case `V` sofic would refute the ternary gate, not just the augmentation route. *(lead)* The earlier line
    "if `V` is sofic, the augmentation route dies, but its target does not" holds only while the extension
    claim is open.
  * **Established, context.** `leavitt-prime-field-units-generated-by-v-and-one-transvection`: over a prime
    field, `R^x` is generated by `V` and one transvection. So a rank model of `R^x` is determined by its
    restriction to `V` and one transvection.
  * **Established firewall.** `anti-central-sofic-data-cannot-force-defect-submultiplicativity` is the
    characteristic-three counterpart of the L5 firewalls. Anti-central regular ranks give ternary cylinder
    defects of rank `5/9`, and those defects multiply exactly on every sofic subgroup and every locally
    finite HNN datum.
  * **Superseded** (lead, after later landings). This overrides the characteristic-three column of the table
    above for the gap row. The results come from lane w5-c3-descent and are verified in
    `gk-vf-gate-verification-2026-09-12.md`.
    * **Established: `ternary-anti-central-two-root-defect-has-a-uniform-gap`.**
      * **Setting.** `R = L_(F_3)(1,2)`. Suppose an anti-central Sylvester rank function `N` on `F_3[G]`
        exists, meaning `N(eps_-) = 1`.
      * **Gap.** Then `c_3 = min N(D)` over all such `N` is attained, and `0 < c_3 <= 2/3`.
      * **Uniform bound.** Every Sylvester rank function has `N(D eps_-) >= c_3 N(eps_-)`.
      * **Prefixes.** Every anti-central `N` has `N(Q_A) = 1/2` and `N(D_A) >= c_3/2` at every nonempty
        proper prefix `A`.
    * **Established: `sylvester-rank-functions-compress-along-commuting-elements`.**
      * **Compression.** Compressing along an element `P` that commutes with a subalgebra gives a Sylvester
        rank function.
      * **Shrinking.** A commuting nilpotent with `x^m = 0` shrinks it by the factor `1 - 1/m`.
      * **What it avoids.** No regularity or faithfulness is used, so it replaces the range-idempotent
        corners of the characteristic-two descent. It gives the upper bounds of the two-sided descent for
        abstract rank functions.
    * **So:**
      * a characteristic-three defect gap now exists over anti-central Sylvester rank functions;
      * descent upper bounds no longer need regularity;
      * **Descent is established in characteristic three.**
        `ternary-cylinder-defect-products-descend-in-sign-sectors` shows that products of disjoint cylinder
        defects shrink by two thirds. They also grow by at least the gap times their anti-central sign
        sector. The node also supplies the positivity item used below.
      * **Live question, characteristic three.** The OPEN
        `ternary-anti-central-disjoint-defects-have-a-strict-deficit` asks for `theta < 1` with
        `N'(D) <= theta N(D)`, where `N'` is the compression of an anti-central `N` along `Q_B D_A`.
        * It is the characteristic-three analogue of the strict submultiplicativity question in L5.
        * Its route `ternary-rank-kill-via-anti-central-defect-deficit` targets
          `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`, the Sylvester form of the
          ternary gate.
        * Both characteristics now have the same shape: the gap and descent are established, and the
          strict deficit is open.
      * Characteristic-three near-minimal multiplicativity is not yet recorded here.
