# bh-verify-master, item 1: the necessity theorem and the ring sufficiency theorem

Adversarial check by lane bh-verify-master, 2026-09-18, read on origin/main at 6481dbd30.
This is a lane check, not an external review.

**Verdict: PASS for both.** No gap found. The steps were re-derived line by line.

## 1a. Necessity: `fp-v-times-subshift-full-groups-force-quantum-rigidity`

Proof: `fp-v-times-subshift-full-groups-force-quantum-rigidity-proof`. Lemma N comes from
`fp-v-times-subshift-full-group-connected-differences-proof`, Section 0.

**Lemma R (a quantum family gives a representation of Γ).**
- *Window.* With the left-invariant word metric, `d(z⁻¹f, z⁻¹f') = |f⁻¹f'| ≤ 2D` on
  `Y = z⁻¹B_D`, so (Q2) makes every operator on `Y` commute.
- *Idempotents.* The window idempotents `P_α` are orthogonal and sum to `I`.
  - (Q3) at `p = z⁻¹` kills every `P_α` whose pattern `α` does not occur in `X`.
  - For each `α` that does occur, shift invariance gives `x'` with `x'(z⁻¹f) = α(f)`. Under the
    convention `(g.x)(h) = x(g⁻¹h)` one can take `x' = (z⁻¹p₀⁻¹).x`.
- *Locality.* After `t` letters the site is `μz` with `|μ| ≤ tℓ`, and the operators used have index
  in `z⁻¹μ⁻¹F_i ⊆ z⁻¹B_(tℓ+r)`. A relator therefore uses only sites in `z⁻¹B_R ⊆ Y` when `D ≥ R`.
- *Scalar reduction.* On `range(P_α)` every operator with index in `Y` acts as the scalar
  `[x'(q) = a]`. So `ψ_E(w)` agrees with `ψ_(x')(w) ⊗ id` there.
- *Transport.* `ψ_(x')(σ)` is the action of `σ` transported through
  `β_(x')(c,z) = (c, z.x')`. The rectangle of the normal form that contains `(c, z.x')` is exactly
  the one with `M_(π_i)(z) = [z.x' ∈ [π_i]] = 1`.
- *Conclusion.* Freeness makes `β_(x')` injective, so relators act trivially. `σσ⁻¹ = 1` gives
  invertibility, and `ψ_E` factors through `Γ`. **Correct.**

**Part 1 (commutation).**
- `g_1 = t_(p⁻¹)⁻¹ e_a t_(p⁻¹)` acts by `h^[x(p)=a]` on the `C` coordinate, since
  `(p⁻¹.x)(1) = x(p)`. Likewise `g_2`. They commute in `F(T)`.
- On the invariant subspace `k[C_0] ⊗ δ_1 ⊗ W_0`, `ψ_E(g_1) = I + (H−1) ⊗ E_a(p)`. This was
  re-derived from the four normal-form tuples of `e_a` and (Q1).
- The commutator is `(H−1)² ⊗ [E_a(p), E_b(q)]`.
- At `c = 0^∞` the points `c`, `hc = 010^∞` and `h²c = 10^∞` are distinct. So `(H−1)²δ_c` has
  coefficient 1 at `δ_c` in every characteristic, and the commutator forces `[E_a(p), E_b(q)] = 0`.
- **Correct.** `D₀ = R` depends only on the presentation.

**Part 2 (finite type).**
- `y ∈ X_N \ X` gives a scalar `N`-quantum family, with `N ≥ R`.
- `ψ_y(v × 1) = v` on `k[C_0 × Λ]`: each `u_j` reads only `z⁻¹B_N`, where `y` agrees with a point
  of `X`.
- The conditioned 3-cycles `τ(f,a,v)` act fibrewise.
- The iterated commutators `c_j ≠ 1` exist because `V` is simple with trivial centre, so no
  nontrivial element centralizes the normal closure of `h`.
- `w_k = 1` in `Γ`, because the pattern `π` occurs nowhere in `X`, in particular not at position 1.
- `ψ_y(w_k) ≠ I` at `z = p⁻¹`, because `c_k` moves an open set and `C_0` is dense.
- **Correct.** The remark that the words `w_k` need no locality bound is right: only the `V` letters
  read far, and they are fixed words.

**Scale monotonicity (Section 4).** Inserting `Σ_b E_b(pf) = I` on `B_(D') \ B_D`, with every factor
inside `pB_(D')` commuting, shows that a `D'`-family is a `D`-family. **Correct.**

## 1b. Ring sufficiency: `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`

Proof: `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products-proof`.
- **The relations translate.** Conjugation by `u_p` turns relations (2)–(4) into (Q1)–(Q3) for
  `E_a(q) = u_q e_a u_q⁻¹`. Relation (3) gives commutation at distance `|q| ≤ 2D`. The product in
  (4) is order-independent by (Q2). **Correct.**
- **Step 1.** Left multiplication on `U` gives a `D`-quantum family, since `x ↦ L_x` is a unital
  algebra map. Rigidity makes the `L_(E_a(q))` commute, and the action is faithful. **Correct.**
- **Step 2.**
  - `LC(A^Λ, k) = ⊗_q k^A` is the universal commutative algebra on Λ-indexed partitions of unity,
    so `ψ` exists and is onto `C`.
  - The kernel of `LC(A^Λ) → LC(X)` is spanned by indicators of cylinders `[p]` missing `X`.
  - The König step is correct. `X` equals the set of configurations all of whose `B_D`-windows
    occur, because `D ≥ r`. Compactness then gives a finite `F' ⊇ F` on which every extension
    contains a forbidden window.
  - Commutativity of `C` turns each extension into a multiple of a conjugated relator (4).
  - `φψ'` is the identity on generators, since `u_q 1_[x(1)=a] u_q⁻¹ = 1_[x(q)=a]` under the node's
    action convention. **Correct.**
- **Step 3.** `U = Σ C u_g`, and the `u_g` are a free left `LC(X,k)`-basis of `B`. So `φ` is
  injective, and it is onto. **Correct.**

## Scope notes

- **What the pair proves.** They are the two halves the route rests on. Finite presentation of the V
  full group implies quantum rigidity, and quantum rigidity implies finite presentation of the crossed
  product. Neither gives the converse on the group side (P2′). The nodes say so correctly.
- **Hypotheses.** Both need `Λ` finitely presented and `X` an SFT. The necessity theorem also needs
  the action free. All three are stated.

## Lesson for general BH

The two load-bearing equivalences are sound, and they are elementary.
- **Where the Z²-crux sits.** "Quantum rigidity of one free minimal SFT" is a statement about
  representations of one explicit finitely presented algebra. It is not a heuristic.
- **Refutations.** A refutation of the master route's crux needs only one noncommuting operator
  family. Wall certificates are the rank-2 case.
- **Positive proofs.** A positive proof may use any representation-theoretic argument on the
  universal algebra `U`, for example an induction supertile by supertile, as Conjecture G2-fp
  proposes.
