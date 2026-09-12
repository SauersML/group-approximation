# No exact second factor with a faithful trace makes an MF tensor product infinite

Lane `uct-nuclear-proper-isometry`, 2026-09-12. Target: the open premise
`nuclear-factor-with-infinite-mf-tensor-exists` of the route
`nuclear-non-uct-via-infinite-mf-tensor` into `nuclear-algebra-without-uct-exists`.

**Answer: the premise is false.** If `A` is MF and `C` is exact with stably finite
unitization, then `A ⊗_min C` is stably finite. A nuclear `C` with a faithful
tracial state meets both hypotheses. So no MF algebra has an infinite spatial tensor
product with such a `C`. The route dies for every nuclear second factor, not only
for second factors containing `π̄(SL(3,Z))`.

Credit: this is a small variant of the Blackadar--Kirchberg permanence argument
already on main (`mf-min-tensor-exact-mf-proof`, steps 1--6), with the MF step
replaced by a blockwise finiteness step. It is very likely known. No novelty is
claimed. It uses no UCT, no quasidiagonality theorem and no classification input.

## 1. Statement

**Claim** `mf-min-tensor-exact-stably-finite-is-stably-finite`. Let `A` be an MF
C\*-algebra, so `A ⊂ Q := ∏_n M_{k_n} / ⊕_n M_{k_n}`. Let `C` be an exact
C\*-algebra whose unitization `C̃` (`C` itself when unital) is stably finite. Then
`A ⊗_min C` is stably finite.

**Corollary.** If `C` is nuclear and has a faithful tracial state, then
`A ⊗_min C` is stably finite for every MF algebra `A`. This refutes
`nuclear-factor-with-infinite-mf-tensor-exists`.

## 2. Proof

**Step 1, corona embedding (exactness of `C` only).** Steps 1--6 of
`mf-min-tensor-exact-mf-proof` give injective \*-homomorphisms

`A ⊗_min C ⊂ Q ⊗_min C = (∏M_{k_n} ⊗_min C)/(⊕M_{k_n} ⊗_min C) ↪ ∏_n M_{k_n}(C) / ⊕_n M_{k_n}(C)`.

- The middle equality is Kirchberg's definition of exactness of `C`.
- `∏M_{k_n} ⊗_min C ⊂ ∏_n M_{k_n}(C)` is spatial.
- The central cut-offs `P_N ⊗ 1` show that
  `(∏M_{k_n} ⊗_min C) ∩ ⊕_n M_{k_n}(C) = ⊕M_{k_n} ⊗_min C`.

None of this uses MF-ness or any finiteness of `C`. Moreover
`M_{k_n}(C) ⊂ M_{k_n}(C̃)`, and a sequence in `∏_n M_{k_n}(C)` is norm-null in one
product exactly when it is in the other. So
`∏_n M_{k_n}(C)/⊕ ↪ D := ∏_n M_{k_n}(C̃) / ⊕_n M_{k_n}(C̃)`, a unital algebra.

**Step 2, almost-isometries straighten blockwise.** Let `E_n` be finite unital
C\*-algebras and `E = ∏_n E_n / ⊕_n E_n`. Suppose `v ∈ E` has `v*v = 1`.
- Lift `v` to a bounded sequence `(V_n)` with `δ_n := ‖V_n*V_n − 1‖ → 0`.
- For `δ_n < 1/2` put `W_n := V_n (V_n*V_n)^{-1/2}`. Then `W_n*W_n = 1` and
  `‖W_n − V_n‖ ≤ ‖V_n‖ · ‖(V_n*V_n)^{-1/2} − 1‖ → 0`.
- `E_n` is finite, so `W_n W_n* = 1`.
- Then `‖V_n V_n* − 1‖ ≤ ‖V_n − W_n‖ (‖V_n‖ + ‖W_n‖) → 0`, so `v v* = 1`.

So `E` is finite.

**Step 3, stable finiteness of `D`.** `M_m(D) ≅ ∏_n M_{m k_n}(C̃) / ⊕_n M_{m k_n}(C̃)`,
and every `M_{m k_n}(C̃)` is finite because `C̃` is stably finite. By Step 2, `M_m(D)`
is finite for every `m`, so `D` is stably finite.

**Step 4, pass to `A ⊗_min C`.** By Step 1, `A ⊗_min C` is a C\*-subalgebra of the
stably finite unital algebra `D`.
- If `A ⊗_min C` is unital with unit `e`, it is a unital subalgebra of the corner
  `eDe`. Corners of stably finite unital algebras are stably finite: if
  `w*w = e ⊗ 1_m` in `M_m(eDe)`, then `w + (1 − e) ⊗ 1_m` is an isometry in
  `M_m(D)`, hence a unitary, so `ww* = e ⊗ 1_m`.
- If `A ⊗_min C` is not unital, `1_D ∉ A ⊗_min C`, so its unitization is
  `A ⊗_min C + ℂ1_D ⊂ D`, a unital subalgebra.

Either way `A ⊗_min C` is stably finite. ∎

**Step 5, the corollary's hypotheses.** Nuclear algebras are exact. Let `τ` be a
faithful tracial state on `C`.
- **Extension to `C̃`.** Put `τ̃(λ1 + c) = λ + τ(c)`, a tracial state on `C̃`. In
  the GNS representation `π` of `τ̃`, the cyclic vector `ξ` satisfies
  `τ̃(y* x* x y) = τ̃(x y y* x*) ≤ ‖y‖² τ̃(x* x)`. So `τ̃(x*x) = 0` forces
  `π(x) π(C̃) ξ = 0`, that is `π(x) = 0`.
- **`π` is faithful on `C̃`.** It is faithful on `C` because `τ` is faithful. If
  `π(λ1 + c) = 0` with `λ ≠ 0`, then `−c/λ` would be a unit for `C ≅ π(C)`.
- **So `τ̃` is faithful**, and `tr_m ⊗ τ̃` is a faithful tracial state on `M_m(C̃)`.
- **So `C̃` is stably finite.** An isometry `w` in `M_m(C̃)` has
  `(tr_m ⊗ τ̃)(1 − ww*) = 0`, so `ww* = 1`.

## 3. What this decides

- **`nuclear-factor-with-infinite-mf-tensor-exists`: REFUTED.** The route
  `nuclear-non-uct-via-infinite-mf-tensor`, which requires it, is invalidated by
  the compiler's refutation rule. The UCT problem is untouched in both directions.
- **Ozawa's example with any exact second factor is dead.** Every separable exact
  `C ⊂ R` carries the faithful trace `τ_R|_C`. So `A ⊗_min C` is stably finite for
  every MF `A`, and Ozawa's proper isometry lies in `A ⊗_min C` only for non-exact
  `C ⊂ R`. The same holds inside any finite von Neumann algebra with a faithful
  normal trace. This settles the one question
  `research/artifacts/uct-ozawa-leg-exactness-2026-09-12.md` §4 left open ("some
  other second factor `C ⊂ R`, containing no copy of `π̄(G)`, ... with `C` exact").
  The answer is no, for every such `C`.
- **Relation to `kazhdan-fd-block-representation-algebras-are-not-exact`.** That
  node stays an independent and stronger statement about `D = C*(⊕_k π_k(G))`
  itself, which is non-exact whatever isometry is used. For the route, the present
  theorem makes it unnecessary: exactness fails for any second factor that works.
- **Why exactness was the obstruction every time.** A finiteness certificate with an
  MF partner passes through the matrix corona over `C`, and the corona inherits
  stable finiteness block by block. `R` escapes only because Step 1 fails for
  non-exact `R`: the map `(∏M ⊗_min R)/(⊕M ⊗_min R) → Q ⊗_min R` has a kernel, and
  a quotient of a stably finite algebra can be infinite.
- **No UCT circularity.** The anticipated kill went through Tikuisis--White--Winter
  (faithful amenable traces on UCT algebras are quasidiagonal). That needs the UCT
  and would be circular for this problem. The argument above uses only Kirchberg's
  definition of exactness, polar decomposition and blockwise finiteness, so the
  refutation is unconditional.

## 4. What survives, and what does not

- **Stronger infiniteness notions.** Proper infiniteness, or an infinite projection
  in `M_m(A ⊗_min C)`, are special cases of failing stable finiteness. They are
  excluded too.
- **Non-MF-ness of the tensor product.** "Some MF `A` has `A ⊗_min C` not MF" is
  equivalent to "`C` is not MF". One direction takes `A = ℂ`; the other is
  `mf-min-tensor-exact-mf-is-mf`. So it is a restatement of the target, not a
  certificate.
- **Non-MF partner.** If `A` is only stably finite and `A ⊗_min C` is infinite,
  nothing follows about `C`, because `mf-min-tensor-exact-mf-is-mf` needs `A` MF.
- **Consequence.** A non-UCT witness through quasidiagonality has to give a
  norm-level obstruction to matrix models of a nuclear `C` with a faithful trace
  directly. Tensor-infiniteness certificates cannot provide one.

## 5. Checks

- **Ozawa's `A ⊗_min R` is infinite.** Consistent, because `R` is not exact.
- **The earlier lemma.** For exact MF `C`, `C̃` is MF and hence stably finite, so
  the stable-finiteness conclusion of `mf-min-tensor-exact-mf-is-mf` is a special
  case.
- **Tensor products of MF algebras.** `A ⊗_min B` is stably finite for exact MF
  `B`. Stable finiteness of the second factor alone does not suffice without
  exactness, as `R` shows.
