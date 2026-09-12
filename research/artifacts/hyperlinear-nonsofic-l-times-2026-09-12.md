# How the binary Leavitt unit group relates to hyperlinearity

Lane `hyperlinear-nonsofic-l-times`, 2026-09-12.
- **Objects.** `R = L_(F_2)(1,2)` and `Q = R^x`.
- **What is known.** `Q` is nonsofic (`openai-leavitt-unit-nonsofic`, resting on Kun--Thom Theorem 4.1, which is not refereed). Whether `Q` is hyperlinear is open (`binary-leavitt-unit-group-hyperlinear`). A yes would give a hyperlinear nonsofic group.
- **Question.** How do the repository's non-hyperlinear chain and the nonsoficity proof bear on `Q`?

## 0. Summary

- **Both outcomes stay open.** Nothing here decides hyperlinearity of `Q`.
- **The Kun--Thom chain does not reach `Q` as it stands.**
  - It proves non-hyperlinearity, once its crux closes, only for the Kun--Thom coset wreath `W` over the Theorem E pair.
  - `Q` inherits the conclusion only if `W`, or a group with the same hyperlinearity status, embeds in `Q`. That is the new open claim `kun-thom-wreath-embeds-in-leavitt-unit-group`, wired to `leavitt-steinberg-hs-stable` by `leavitt-nonhyperlinear-via-kun-thom-wreath-embedding`.
  - Its actor `G` is linear over no field of positive characteristic (Section 1.3). So no matrix embedding over a commutative subring of `R` exists.
- **The chain has no internal Leavitt instance.** `leavitt-pair-vertex-rounding-is-nonhyperlinearity` is ESTABLISHED.
  - For the nine-leaf pair `Gamma = EL_alpha(R) < G_L = EL_D(R)`, the rounding hypothesis (H1) is equivalent to `Q` not being hyperlinear. Both groups are `Q`, and `Q` is minimally almost periodic.
  - Consequence 1: the literal general form of `hs-stable-vertex-rounding-for-every-model` implies that `Q` is not hyperlinear.
  - Consequence 2: a hyperlinearity proof for `Q` would refute that general form.
- **Mechanism.** The nonsoficity proof converts approximations into exact finite objects by counting. In the Hilbert--Schmidt row, property (T) still rounds, but the faithful size is missing. This is the ladder's (A3), `rigid-compression-defect-ladder-2026-09-11.md` Sections 10 and 11.
  - The Kun--Thom chain substitutes a finite-stage size built from congruence images of its vertex.
  - Every Kazhdan corner `EL_3` inside `Q` is minimally almost periodic, so that substitute cannot exist inside `Q`.
- **Existence.** Any hyperlinear model of `Q` has no genuine skeleton. It stays at distance `sqrt 2` from every genuine representation on each minimally almost periodic subgroup, including the embedded `V` and every `EL_3` corner. It also has to model `V` first (`thompson-v-hyperlinear-from-leavitt-unit-hyperlinear`).

## 1. The embedding question

### 1.1 What the chain proves and about which group

Route `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` needs three premises:
- `theorem-e-vertex-rounds-to-unit-type-representations` (OPEN; its crux is `vertex-rounding-deep-nonunit-root-mass-vanishes`);
- `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` (established);
- `kun-thom-wreath-carries-rigid-defect` (established).

Together they give that `W = (direct_sum_(G/Gamma) Z/2) semidirect G` is not hyperlinear, where

```text
Gamma = EL_r(F_q[x_1..x_d])  <  G = EL_r(F_q[x_1^(+-1)..x_d^(+-1)]) semidirect SL_d(Z),   r, d >= 3.
```

The first premise uses finite congruence images of `Gamma`. Every finite-dimensional unitary representation of `Gamma` factors through a finite Steinberg group `St_r(R_+/I)`, and the unit-type projections `P_n` are central projections onto constituents. They are the size that the Hilbert--Schmidt row otherwise lacks.

### 1.2 Why the chain cannot be run inside `Q`

`Q` has its own infranormal non-normal Kazhdan pair with a nontrivial rigid defect (`leavitt-unit-group-carries-nontrivial-rigid-defect`). Replaying the chain there fails at the first premise:
- `GL_n(R) = EL_n(R)` for all `n >= 2`, and complete prefix codes give `M_k(R) ~= R`.
- So `Gamma = EL_alpha(R) ~= EL_3(R) ~= Q` and `G_L = EL_D(R) ~= Q`.
- `Q` is minimally almost periodic (`binary-leavitt-unit-group-is-minimally-almost-periodic`). So every genuine `pi_n : Gamma -> U(n')` is trivial.
- A trace-preserving `sigma` keeps each nontrivial Kazhdan generator at distance `sqrt 2` from `1`. So (H1) at this pair holds exactly when no trace-preserving `sigma` exists, i.e. when `Q` is not hyperlinear.

This is `leavitt-pair-vertex-rounding-is-nonhyperlinearity`. Read literally, `hs-stable-vertex-rounding-for-every-model` quantifies over every infranormal non-normal Kazhdan pair. Its general form therefore contains this instance. A consumer that uses (H1) only at the Theorem E pair is unaffected.

### 1.3 The actor is not linear in positive characteristic

**Lemma.** Let `K` be a field of characteristic `p > 0` and `a, b` in `GL_n(K)`. If `c = [a,b]` commutes with `a` and `b`, then `c` has finite order.

*Proof.*
1. Pass to the algebraic closure. `a` and `b` commute with `c`, so they preserve each generalized eigenspace `E` of `c`, with eigenvalue `lambda`.
2. On `E`, `a b a^-1 = c b`. Taking determinants, `det(b|E) = det(c|E) det(b|E) = lambda^(dim E) det(b|E)`, so `lambda^(dim E) = 1`.
3. Every eigenvalue of `c` is a root of unity, so the semisimple part `c_s` has finite order.
4. The unipotent part `c_u` satisfies `c_u^(p^m) = 1` for large `m`, and it commutes with `c_s`. So `c` has finite order. ∎

**Corollary.** For `d >= 3` the actor `G` contains the integer Heisenberg group, the upper unitriangular matrices in `SL_3(Z) <= SL_d(Z)`. Its central commutator `x_13(1) = [x_12(1), x_23(1)]` has infinite order, so `G` embeds in `GL_n(K)` for no field `K` of positive characteristic. In particular `G` has no embedding into matrices over a commutative subring of `R`.

### 1.4 Other obstacles

- **Regular representation.** It embeds finitely generated characteristic-two linear groups of transcendence degree at most one in `Q`, and stops there by a Krull-dimension bound (`char-two-curve-linear-groups-satisfy-boone-higman`). The vertex needs transcendence degree `d >= 3`.
- **Disjointly supported Thompson elements.** Let `g, h` in the embedded `V` have disjoint supports.
  - `R` is simple, so any nonzero module is faithful; take the Chen module on infinite paths.
  - A path in the support of `h` is fixed by `g`. So `(g - 1)(h - 1)` kills every basis path, and `(g - 1)(h - 1) = 0` in `R`.
  - Such pairs never generate a Laurent ring in two variables.
- **Digit interleaving.** With `C ~= C x C` via odd and even digits, only length-preserving prefix replacements act on one coordinate. Infinite-order elements of `V` change lengths and move infinitely many digits across the two coordinates.
- **First concrete test.** Does `Q` contain `H_3(Z)` with a central commutator of infinite order? Sections 1.3 and 1.4 exclude the linear sources and the disjoint-support sources. Nothing examined here decides the question.

### 1.5 What either answer would buy

- **Embedding exists, and the chain's crux closes:** `Q` is not hyperlinear. By `leavitt-unit-hs-stable-iff-nonhyperlinear` it is normalized-HS stable (`leavitt-steinberg-hs-stable`).
- **Embedding exists, and `Q` is hyperlinear:** `W` is hyperlinear. The chain's two established premises then force `theorem-e-vertex-rounds-to-unit-type-representations` to fail.
- **No embedding:** the two questions stay independent. A non-hyperlinear `W` says nothing about `Q`.

## 2. The mechanism question

The nonsoficity proof is the OPENAI criterion, or equivalently Kun--Thom Theorem 4.1 through `rigid-compression-defect-normalization-dichotomy`. Its steps (following `rank-row-compression-audit-2026-09-12.md` Section 3 and the ladder artifact):
- **(K)** Kun's decomposition rounds the almost-action of the Kazhdan group into expanding components.
- **(T1)** A compressed component lies almost inside one component.
- **No room to drift.** Components are finite sets with cardinalities, so an injective compression between equal-size pieces is onto.
- **Collision and conclusion.**

In the normalized Hilbert--Schmidt row:
- **(K) has an analogue.** Property (T) gives a spectral gap on `L^2(M) ⊖ L^2(M^Gamma)` (ladder Section 10, `kazhdan-asymptotic-commutant-transport`).
- **The size is missing.** No faithful conjugation-invariant size exists on relative commutants of infinite index (`invariant-size-collapse`), and compressors can rotate multiplicity spaces. This is the missing (A3).
- **The chain's substitute.** For the Theorem E vertex, the finite congruence images give central projections `P_n` whose traces act as a finite-stage size. That is exactly what `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` consumes.
- **Inside `Q` the substitute cannot exist.** Every `EL_3` corner of `Q` is isomorphic to `Q` and minimally almost periodic. Any Hilbert--Schmidt proof of non-hyperlinearity for `Q` needs a size on relative commutants that does not come from finite-dimensional representations of its Kazhdan subgroups. It does not transcribe from the nonsoficity proof.

The weakly-sofic lane records the same boundary for the rank and weak-sofic rows (`weakly-sofic-extension-metric-scope-2026-09-12.md`). The two unitary-specific points added here are the congruence-size substitute and why `Q` excludes it.

## 3. Existence attempts for hyperlinear models

These are necessary conditions. None is a construction.

- **No genuine skeleton.** Every minimally almost periodic subgroup of `Q`, including `V` and each `EL_3` corner, is at distance `sqrt 2` from every genuine finite-dimensional representation in any trace-preserving model. So no architecture can round a Kazhdan or Thompson piece to an exact representation and perturb.
- **`V` comes first.** `Q` hyperlinear implies `V` hyperlinear (`thompson-v-hyperlinear-from-leavitt-unit-hyperlinear`), which is open. The natural Cantor truncations that would model `V` lose rank at length-changing prefixes. That is recorded dead for `F_2`-rank models on `binary-leavitt-unit-group-is-f2-linear-sofic`, and its Hilbert--Schmidt analogue is the open soficity question for `V`.
- **Algebra representations give nothing finite.** `R` has no unital rank model (`leavitt-algebra-has-no-unital-rank-model`). Its unitary representations from infinite-path spaces are infinite-dimensional with no normalized trace. Truncating them reintroduces the defect at length changes.
- **What remains.** A model has to be approximate everywhere on each Kazhdan corner. That is the regime `binary-leavitt-unit-group-hyperlinear` lists as the only one not excluded by its eight dead architectures.

## 4. Landed and open

- **ESTABLISHED:** `leavitt-pair-vertex-rounding-is-nonhyperlinearity`, with its route `leavitt-pair-vertex-rounding-nonhyperlinearity-proof`.
- **OPEN:** `kun-thom-wreath-embeds-in-leavitt-unit-group`, with Attempts covering the lemma of Section 1.3 and the obstacles of Section 1.4.
- **ROUTE (conditional):** `leavitt-nonhyperlinear-via-kun-thom-wreath-embedding` into `leavitt-steinberg-hs-stable`.
- **Scope note** on `hs-stable-vertex-rounding-for-every-model`.

No novelty is claimed for the lemma in Section 1.3. It is a standard determinant argument.
