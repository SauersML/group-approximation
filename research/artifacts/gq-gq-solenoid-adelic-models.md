# Adelic Cantor models for GL_n(Q): constructions and verdict (lane gq-solenoid, 2026-09-17)

Target: `gl-n-q-embeds-in-fp-simple-group`. The assignment was to build a V-like group of locally affine homeomorphisms
of an adelic Cantor model containing GL_n(Q), and to decide finite generation, finite presentation and simplicity.

**Verdict.**
- Every such group is non-finitely-generated, as is every group containing the linear copy of GL_n(Q) with finitely
  many adelic-affine or adelic-projective pieces per element off a closed nowhere dense set.
- A finitely presented host of this kind is therefore impossible. Simplicity is moot.
- Proof: `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`. It rests on topological freeness plus Mal'cev
  residual finiteness, and O1 finishes it.

## 1. The models

Notation: `A_f` is the ring of finite adeles, and `Ẑ = ∏_p Z_p ⊂ A_f`, which is compact open. `Q ⊂ A_f` sits
diagonally and densely, and `A_f = Q + Ẑ`.

**M1. Affine model `X_1 = A_f^n ∪ {∞}`.**
- `A_f^n` is locally compact, second countable, zero-dimensional, perfect and noncompact. So its one-point
  compactification is a Cantor set: it is compact, metrizable, zero-dimensional and perfect.
- `Aff_n(A_f)`, and in particular `Aff_n(Q) ⊇ GL_n(Q)`, acts by homeomorphisms fixing `∞`. The action of
  `Aff_n(Q)` is faithful, since `Q^n` is dense.
- **Cones.** The compact open subgroups of `A_f^n` are exactly the `gẐ^n`, `g ∈ GL_n(Q)`.
  - A compact open `K` satisfies `NẐ^n ⊆ K ⊆ (1/M)Ẑ^n`.
  - `(1/M)Ẑ^n = (1/M)Z^n + NẐ^n`, so `K = Λ + NẐ^n` with `Λ = K ∩ Q^n` a lattice `gZ^n`. Then
    `K = closure(Λ) = gẐ^n`.
  - So the basic clopen sets are the cosets `a + gẐ^n`. Their traces on `Q^n` are the lattice cosets `a + gZ^n`.
    This is the "all primes at once" analogue of Scott's `2`-adic cosets.
- **Full group `Γ_1`.** Let `Γ_1 = [[Aff_n(Q) | X_1]]` be the homeomorphisms that are piecewise in `Aff_n(Q)` on
  finite clopen partitions.
  - Restricted to `Q^n`, `Γ_1` is the group of bijections of `Q^n` that are affine on finitely many lattice cosets
    and on one complementary "co-compact" piece.
  - It contains `Aff_n(Q)`.
  - Germs are rigid (topological freeness), so the germ at `∞` is a split surjection `Γ_1 -> Aff_n(Q)`.
  - `Aff_n(Q)` is not finitely generated: `det` maps it onto `Q^×`. So `Γ_1` is not finitely generated, by this
    elementary certificate as well.

**M2. Projective model `X_2 = ∏_p P^{m-1}(Q_p)`, `m = n+1`.**
- `X_2` is compact and a Cantor set, as a countable product of Cantor sets. Note `P^{m-1}(Q_p) = P^{m-1}(Z_p)`.
- `GL_n(Q)` embeds in `PGL_m(Q)` by `g ↦ [diag(g,1)]`. The map is injective, since `diag(g,1)` scalar forces
  `g = 1`. `PGL_m(Q)` acts diagonally and faithfully on `X_2`.
- **Minimality.**
  - `∏_p SL_m(Z_p)` is transitive on `X_2`, since a primitive vector extends to a `Z_p`-basis of determinant 1.
  - `SL_m(Q)` is dense in `SL_m(A_f)`, by strong approximation for `SL_m`. The orbit map is continuous, so
    `SL_m(Q)`-orbits are dense.
  - So `PGL_m(Q) ↷ X_2` is minimal and topologically free.
- **Not compactly generated.**
  - The germ groupoid is the transformation groupoid `PGL_m(Q) ⋉ X_2`, because rigid germs determine the element.
  - Compact sets of germs involve finitely many group elements, so the groupoid is not compactly generated.
  - So no finiteness theorem of Matui–Nekrashevych type can apply to `[[PGL_m(Q) | X_2]]`.

**M3. Adelic prefix group `V_Ẑ` on `Ẑ`.**
- The pieces are `z ↦ b + (N'/N)(z − a)`, mapping `a + NẐ` onto `b + N'Ẑ`, for arbitrary positive integers
  `N, N'`.
- `V_Ẑ` contains each Higman–Thompson group `V_d`: the same formulas act on the dense set `Z`.
- **Not finitely generated.** A finitely generated subgroup has pieces from a finitely generated `H ≤ Aff_1(Q)`,
  whose slopes involve finitely many primes. Rigid germs then exclude any element whose germ somewhere has slope `p`
  with `p` outside that finite set. So `V_Ẑ` is the non-finitely-generated union of the prefix groups over finite
  sets of primes.

## 2. Why no adelic variant can be rescued

- `L = Aff_n(A_f)`, and `GL_m(A_f)/A_f^×`, are linear over the commutative ring `A_f` and topologically free on
  `X_1`, `X_2`.
- Let `Γ` be any finitely generated group whose elements are `L`-piecewise, with finitely many pieces per generator
  off a closed nowhere dense set.
- **Then the globally-`L` elements of `Γ` lie in a finitely generated linear group `H ≤ L`**, which is residually
  finite. Divisible `(Q,+) ≤ GL_n(Q)` cannot sit there (root O1).
- **Singularities don't help.** Declaring `0` and `∞`, or any finite set, singular changes nothing. The linear
  elements are still globally in `L`, and part (a) of the claim needs only one regular point.
- **What would have to change.** The copy of `GL_n(Q)` itself would have to be exotic, with its divisible elements
  not globally in `L`. Examples are the genuinely piecewise elements of Kojima–Sheng's `Q ≤ 2V`, or of `Q ≤ T̄ ≤ VA`.
  Infinitely many local pieces near singular points do not rescue the linear copy: `germ-extensions-omit-standard-gl-n-q`
  covers every group that is locally in a finitely generated finitely-piecewise base off a nowhere dense set.
- So an adelic model buys nothing over the classical `2`-adic ones. Its only feature, all primes at once, is exactly
  what finite generation cannot see.

## 3. Sparks (not pursued here)

- **S1. T̄ over the solenoid.** `Q ≤ T̄` uses the covering `R -> S^1` and rotation numbers in `Q/Z`. The adelic
  solenoid `Σ = A/Q` has `Aut(Σ^n) ⊇ GL_n(Q)` and a dense leaf `R^n`. A lift-type group, piecewise on leaves with
  infinitely many periodic pieces, could realize divisibility by lifts that are not globally affine, as in `T̄`. For `gq-tbar-lift-n`.
- **S2. Where divisibility must live.** Let `Γ ≤ PW_X(L)` be finitely generated, with `L` commutative-linear and
  topologically free, and let `D ≅ (Q,+)` lie in `Γ`.
  - The elements of `D` that are globally in `L` form a subgroup of the residually finite group `H`. So they form
    a proper, non-divisible subgroup of `D`.
  - All other elements of `D` are genuinely piecewise.
  - How their piece structure must grow along a divisibility chain, like the growth in Kojima–Sheng's `Q ≤ 2V`, is
    the natural next question. The same pieces are where the distortion required by root O4 would have to live.
  - For `gq-germ-necessary` and `gq-obstruction-miner`.
