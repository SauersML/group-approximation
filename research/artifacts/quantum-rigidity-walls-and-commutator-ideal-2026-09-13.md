# Quantum rigidity of SFTs: walls are exactly the first-order obstruction

Lane `ex2-labbe-quantum-rigidity`, 2026-09-13. Unreviewed. Part 1. It supports:
- `sft-wall-rigidity-iff-idempotent-commutator-ideal`;
- `periodic-quantum-tilings-refute-quantum-rigidity`.

Predecessor: `research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md` (Theorem 1 there:
`R_Ω` is finitely presented iff `Ω` is `D`-quantum rigid for some `D >= r`; Theorem 2 there: wall certificates).

## 0. Setting

`k` is a field. `Ω ⊆ A^(Z^2)` is an SFT with forbidden patterns in `B_r` (sup norm), and `D >= r`.
`L_D = L_(B_D)(Ω)` is the set of `B_D`-patterns occurring in `Ω`.

- **The local tiling algebra.** `C_D` is the universal `k`-algebra with generators `P_z^a`
  (`z ∈ Z^2`, `a ∈ A`) and relations
  - (Q1) `P_z^a P_z^b = delta_ab P_z^a`, `sum_a P_z^a = 1`;
  - (Q2) `[P_z^a, P_(z')^b] = 0` for `|z - z'| <= 2D`;
  - (Q3) `prod_(h ∈ B_D) P_(z+h)^(pi(h)) = 0` for `pi ∉ L_D` (the factors commute by (Q2)).
- **Families.** A family on `W` in the predecessor's sense is exactly a `C_D`-module structure on `W`.
- **Crossed product.** `Z^2` acts on `C_D` by `P_z^a -> P_(z+g)^a`. The predecessor's `A_D` is `C_D ⋊ Z^2`:
  `e_a -> P_0^a` and `P_z^a -> u^z e_a u^(-z)` respect the relations and are mutually inverse on generators.
- **Rigidity.** `Ω` is `D`-quantum rigid iff `C_D` is commutative (take `W = C_D` for one direction).
  The commutative quotient is `C_D / J_D = LC(Ω, k)`, where `J_D` is the commutator ideal, by the
  predecessor's Stone duality step (it uses `D >= r`).
- **Difference sets.** For `T_1, T_2 ∈ Ω`, `Δ(T_1, T_2) = {z : T_1(z) != T_2(z)}`. A set `S ⊆ Z^2` is
  *`2D`-connected* if any two points are joined by a chain in `S` with steps of sup-length `<= 2D`.
- **Wall rigidity.** `Ω` is *`D`-wall-rigid* if every `Δ(T_1, T_2)` is `2D`-connected (or empty).
  A split `Δ = Δ_I ⊔ Δ_O` with `d(Δ_I, Δ_O) > 2D` is exactly a wall certificate of the predecessor's
  Theorem 2 (take `I = Δ_I`, `O = Δ_O`, `M` the rest), and conversely.

## 1. Triangular families on `k^2`

**Theorem 1.** Fix `T_1, T_2 ∈ Ω` and put `s_a(z) = [T_1(z) = a]`, `t_a(z) = [T_2(z) = a]`. The
upper-triangular operators
`E_a(z) = [[s_a(z), f_a(z)], [0, t_a(z)]]`
form a family iff `f_a(z) = λ(z) (s_a(z) - t_a(z))` for a function `λ : Δ -> k` that is constant on every
`2D`-component of `Δ = Δ(T_1, T_2)`. The family commutes iff `λ` is constant on `Δ`. So a noncommuting
triangular family with diagonal `(T_1, T_2)` exists iff `Δ` is not `2D`-connected.

*Proof.* The diagonal entries satisfy (Q1)–(Q3) because `T_1, T_2 ∈ Ω`. Only upper-right entries remain.
1. **(Q1) forces the shape.** The upper-right entry of `E_a E_b` is `s_a f_b + f_a t_b`.
   - Off `Δ`, `s = t`. With `a = b`: `2 s_a f_a = f_a`, so `f_a = 0` whether `s_a` is `0` or `1`.
   - At `z ∈ Δ` with `T_1(z) = a != b = T_2(z)`: for `c ∉ {a, b}`, `s_c = t_c = 0` forces `f_c = 0`,
     and `sum_c f_c = 0` gives `f_b = -f_a`. So `f = λ(z)(s - t)` with `λ(z) = f_a(z)`.
   - Conversely `f = λ (s - t)` satisfies (Q1): for `a = b`, `λ(s_a(s_a - t_a) + (s_a - t_a) t_a) = λ(s_a - t_a)`;
     for `a != b`, `λ(s_a s_b - s_a t_b + s_a t_b - t_a t_b) = 0`.
2. **(Q2) is local constancy.** The upper-right entry of `[E_a(z), E_b(z')]` is
   `(s_a - t_a)(z) (s_b - t_b)(z') (λ(z') - λ(z))`. It vanishes identically iff `z ∉ Δ`, or `z' ∉ Δ`, or
   `λ(z) = λ(z')` (take `a = T_1(z)`, `b = T_1(z')`). Imposed for `|z - z'| <= 2D`, this says `λ` is constant
   on `2D`-components.
3. **(Q3) is automatic.** A ball `z + B_D` has sup-diameter `2D`, so `λ` takes one value `λ_0` on
   `Δ ∩ (z + B_D)`. With `s_j, t_j, f_j` the entries at the `j`-th point in the fixed order, the upper-right
   entry of the product is
   `sum_j (prod_(i<j) s_i) λ_0 (s_j - t_j) (prod_(i>j) t_i) = λ_0 (prod s - prod t)`,
   by telescoping. Both products vanish when `pi ∉ L_D`.
4. **Commutation.** By step 2, all `E` commute iff `λ` is constant on `Δ`. QED

The predecessor's two-basis certificate is the case `λ = 0` on `Δ_I` and `λ = -1` on `Δ_O`.

## 2. All families on `k^2`

**Theorem 2.** If some family on `k^2` does not commute, then `Ω` is not `D`-wall-rigid.

*Proof.*
1. **Local shape.** Idempotents are diagonalizable over any field. At each `z`, either one `E_a(z)` is `1`
   (a *scalar site*, letter `τ(z)`), or exactly two are rank-one, with images forming an unordered pair of
   distinct lines `{L, L'}` (a *split site*).
2. **Commutation of split sites.** Two rank-one idempotents on `k^2` commute iff they are simultaneously
   diagonalizable. The first has two distinct one-dimensional eigenspaces `L, L'`, so a common eigenbasis
   must be `{L, L'}`. Hence two split sites commute iff they have the same pair. Scalar sites commute with
   everything.
3. **Components.** Let `N` be the set of split sites. By (Q2), the pair is constant on each
   `2D`-component `C` of `N`; write it `{L_C, L'_C}`. If all components had the same pair, all `E` would be
   diagonal in one basis and commute. So there are components `C_1 != C_2` with different pairs, and
   `d(C_1, C_2) > 2D`.
4. **Two tilings.** On `C`, let `τ_C(z)` and `τ'_C(z)` be the letters on `L_C` and `L'_C`. Let `T_1` read `τ`
   off `N` and `τ_C` on every component, and let `T_2` agree with `T_1` except that it reads `τ'_(C_i)` on
   `C_1` and `C_2`.
5. **Admissibility.** A ball `z + B_D` meets at most one component, because its points are pairwise within
   `2D`. In the basis `{L_C, L'_C}` of that component, or in any basis if it meets none, the operators on the
   ball are diagonal. For `pi ∉ L_D`, (Q3) makes both diagonal entries of the product vanish. So both
   side-configurations have no forbidden pattern on the ball, and `T_1, T_2 ∈ Ω` because `D >= r`.
6. **The certificate.** `Δ(T_1, T_2) = C_1 ∪ C_2` is not `2D`-connected. QED

Theorems 1 and 2 give: `Ω` is `D`-wall-rigid iff every family on `k^2` commutes.

## 3. The commutator ideal

**Lemma 3.1 (points).** Let `Y` be a Stone space and `M != 0` a module over `LC(Y, k)`. Then there is
`y ∈ Y` with `M_y = M / sum_(e(y) = 0) eM != 0`, where `e` runs over idempotents.

*Proof.* Pick `m != 0`. The idempotents of `Ann(m)` form an ideal `I` of the Boolean algebra of clopens, not
containing `1`. By compactness there is `y` where every `e ∈ I` vanishes: otherwise finitely many clopens of
`I` cover `Y`, and their join is `1 ∈ I`. If `m ∈ sum_(e(y)=0) eM`, then `m = e m` for the finite join `e` of
the idempotents used, with `e(y) = 0`. So `1 - e ∈ Ann(m)` and `(1 - e)(y) = 1`, a contradiction. QED

**Lemma 3.2 (splitting).** Let `B` be a `k`-algebra, `M ⊆ B` an ideal with `M^2 = 0`, and `B / M ≅ LC(Y, k)`
with `Y` a Stone space whose clopen algebra is countable. Then the quotient map has an algebra section.

*Proof.* Write `LC(Y, k)` as an increasing union of finite-dimensional subalgebras `F_n ≅ k^(m_n)`, each
minimal idempotent of `F_n` a sum of minimal idempotents of `F_(n+1)`. Complete orthogonal families of
idempotents lift modulo a nil ideal (standard lifting of idempotents). Lift the minimal idempotents of `F_0`.
Given a lift `e` of a minimal idempotent of `F_n`, lift its refinement in `F_(n+1)` to a complete orthogonal
family in the corner `eBe`, modulo the nil ideal `eMe`. The lifts are compatible with refinement and
orthogonal across different atoms, so they define a multiplicative section on the union. QED

**Theorem 3.** `Ω` is `D`-wall-rigid iff `J_D = J_D^2`.

*Proof.*
1. **"If".** Suppose `Δ(T_1, T_2)` is not `2D`-connected. Theorem 1 gives a noncommuting representation
   `ρ : C_D -> T_2(k)` into upper-triangular matrices. The diagonal of `ρ` is commutative, so `ρ(J_D)` is
   strictly upper triangular. Then `ρ(J_D^2) = 0` but `ρ(J_D) != 0`, since `ρ` is noncommutative.
2. **"Only if": the bimodule.** Suppose `J_D != J_D^2` and put `M = J_D / J_D^2`. It is a bimodule over
   `C_D / J_D = LC(Ω, k)`, so a module over `LC(Ω × Ω, k)`. By Lemma 3.1 there are `T_1, T_2 ∈ Ω` and a nonzero
   linear functional `φ` on `M` with `φ(f m g) = f(T_1) φ(m) g(T_2)`.
3. **The representation.** By Lemma 3.2, `C_D / J_D^2 = s(LC(Ω)) ⊕ M` with `s` an algebra section. Put
   `ρ(s(f) + m) = [[f(T_1), φ(m)], [0, f(T_2)]]`. Since `M^2 = 0`, the product rule reduces to
   `φ(s(f) n + m s(g)) = f(T_1) φ(n) + φ(m) g(T_2)`, which is the bimodule property. So `ρ` is a
   representation of `C_D`.
4. **It is noncommutative.** `ρ(J_D) != 0` because `φ != 0`. A representation whose generators commute
   kills every commutator, hence `J_D`. So `ρ` is a noncommuting triangular family with diagonal `(T_1, T_2)`.
5. **The certificate.** By Theorem 1, `Δ(T_1, T_2)` is not `2D`-connected. QED

**Corollary 3.3 (filtered families).** If `Ω` is `D`-wall-rigid, every family with a finite filtration
`0 = W_0 ⊂ ... ⊂ W_m = W` by invariant subspaces whose subquotient families commute is commutative.

*Proof.* The associated graded representation is commutative, so it kills `J_D`. Hence `ρ(J_D)` lowers the
filtration and `ρ(J_D)^m = 0`. So `ρ(J_D) = ρ(J_D^m) = 0`. QED

**Corollary 3.4.** Let `k` be algebraically closed and `Ω` `D`-wall-rigid. Every noncommuting
finite-dimensional family has a composition factor of dimension `>= 3`.

*Proof.* An irreducible commuting family is one-dimensional: its idempotents commute with the whole image,
so each acts by `0` or `1`, and every subspace is invariant. If all composition factors had dimension `1`,
Corollary 3.3 would make the family commute. A two-dimensional composition factor is itself a noncommuting
family on `k^2`, which Theorem 2 excludes. QED

**Summary.** For `D >= r` the following are equivalent: (a) `D`-wall-rigidity; (b) every family on `k^2`
commutes; (c) `J_D = J_D^2`; (d) every finitely filtered family with commuting subquotients commutes.
(a)⇔(b) is Theorems 1–2, (a)⇒(c) is Theorem 3, (c)⇒(d) is Corollary 3.3, and (d)⇒(a) is Theorem 1.

## 4. Finite-dimensional modules of the local presentation

**Theorem 4.** Let `Ω` have no periodic point, `D >= r`, and `V != 0` a finite-dimensional `A_D`-module.
1. The family `P_z^a` on `V` does not commute, and `V` has no one-dimensional `C_D`-composition factor.
   So `Ω` is not `D`-quantum rigid, and a rigid `Ω` admits no nonzero finite-dimensional `A_D`-module.
2. If `k` is finite, nonzero finite-dimensional `A_D`-modules are the same as *periodic families*: families
   on a finite-dimensional `W` with `E(z + λ) = E(z)` for `λ` in a finite-index `Λ ≤ Z^2`.
3. If `k` is algebraically closed and `Ω` is `D`-wall-rigid, every composition factor of `V` that carries a
   noncommuting family has dimension `>= 3`, and at least one exists.

*Proof.*
1. **Characters give periodic points.** Let `𝔅` be the image of `C_D` in `End(V)`; conjugation by `u^g`
   preserves it. A one-dimensional composition factor gives a character `χ : 𝔅 -> k'` into a field.
   `χ(P_z^a) ∈ {0, 1}` with one `1` per site, and (Q3) makes `T_χ(z) = (the a with χ(P_z^a) = 1)` locally
   admissible, so `T_χ ∈ Ω`. The kernels of characters are among the finitely many maximal ideals of `𝔅`,
   and `Z^2` permutes them. So `ker χ` has a finite-index stabilizer `Λ`, and `T_χ` is `Λ`-periodic. That is
   a contradiction. A commuting family on `V` would have a one-dimensional composition factor.
2. **Periodic families.** If `k` is finite, `GL(V)` is finite, so `u^λ = 1` for `λ` in a finite-index `Λ`,
   and `P_(z+λ) = u^λ P_z u^(-λ) = P_z`. Conversely, a `Λ`-periodic family on `W` gives the module
   `V = Map(Z^2/Λ, W)` with `(e_a ξ)(w) = E_a(w) ξ(w)` and `(u^g ξ)(w) = ξ(w + g)`. This is the predecessor's
   sitewise representation, with finitely supported functions replaced by periodic ones.
3. **Wall-rigid case.** Apply Corollary 3.4 to the noncommuting family on `V`. QED

So a *periodic quantum tiling* of an aperiodic tile set refutes rigidity at its scale `D`, and it is
genuinely contextual: no one-dimensional piece, and for a wall-rigid shift no two-dimensional piece.

## 5. What remains (heuristic, not established)

- **The crux.** Quantum rigidity equals wall rigidity plus `J_D = 0`. For a wall-rigid shift, a failure of
  rigidity is a nonzero *idempotent* commutator ideal. Such a failure has no first-order (extension) part, and
  is detected only by irreducible families of dimension `>= 3`, or by infinite-dimensional modules with no
  finite filtration.
- **Group shifts.** For a group shift over `F_2` and `char k != 2`, families are representations of the
  solution group `Γ_D`. It is generated by involutions `X_z = P_z^0 - P_z^1`, with `X_z, X_(z')` commuting
  for `|z - z'| <= 2D` and the parity relators of `L_D`. Rigidity is `Γ_D` abelian. By the standard
  relative-augmentation formula (recalled, not re-derived), `J_D = J_D^2` iff `[Γ_D, Γ_D]^ab ⊗ k = 0`. So the
  separation question asks for a nonabelian `Γ_D` whose commutator subgroup has `k`-trivial abelianization.
- **Dimension 3.** Frames change through bands of `(2,1)`-type sites. Such a band fixes one line and rotates
  inside the complementary plane. Tracing a loop of such rotations around a hole in `k^3`, returning to a
  frame that shares a line with the start forces the intermediate frames to coincide. The case checked by
  hand is the generic one. So dimension-3 contextual loops look trivial, and the annular mechanism needs
  dimension `>= 4`, as for the magic square.
- **Unbounded annuli.** A contextual annulus of non-scalar sites around a scalar hole, bounded and with scalar
  sites outside, would give letter-configurations differing from `τ` on a finite set. For a minimal SFT that
  forces positive entropy, by the argument of the predecessor's Proposition 4. So for minimal zero-entropy
  shifts, any such mechanism is unbounded.
