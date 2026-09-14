# sk-rigidity-ring, part 1: matrix rings over Cantor crossed products remember strong orbit equivalence; the group step in characteristic 2

Lane `sk-rigidity-ring`, 2026-09-13. Status:
- §1 Theorem R is proved here from four inputs: Theorem K (on main), Ara–Claramunt (on main), and two dimension-group
  imports quoted in part 2. UNREVIEWED.
- §2 records the consequences for the groups and corrects the "height-3 towers" caveat on main.
- §3 records the characteristic-2 group step (a). It stays OPEN, with firewalls.

Notation:
- `k` is a field and `(X,T)` a minimal homeomorphism of a Cantor set, with `T_* f = f ∘ T^(−1)`.
- `R_X = LC(X,k) ⋊_T Z`, the algebraic crossed product: finite sums `Σ f_n u^n` with `u f u^(−1) = f ∘ T^(−1)`.
- `K^0(X,T) = C(X,Z)/(1 − T_*)C(X,Z)`, with cone `K^0(X,T)^+ = {[f] : f ≥ 0}` and unit `[1]`.

## 1. Theorem R

**Theorem R.** Let `(X,T)` and `(Y,S)` be minimal homeomorphisms of Cantor sets, let `k, k'` be fields and `m ≥ 1`.
Suppose `M_m(R_X) ≅ M_m(R_Y)` or `M_m(R_X) ≅ M_m(R_Y)^op` as rings, where `R_X = LC(X,k) ⋊ Z` and
`R_Y = LC(Y,k') ⋊ Z`. Then `(K^0(X,T), K^0(X,T)^+, [1]) ≅ (K^0(Y,S), K^0(Y,S)^+, [1])`. So `(X,T)` and `(Y,S)` are
strongly orbit equivalent, by Giordano–Putnam–Skau (part 2, (I1)).

*Proof.*

**(R1) Anti-isomorphisms reduce to isomorphisms.** Put `ι(Σ f_n u^n) = Σ u^(−n) f_n`. For `a = f u^p` and `b = g u^q`,
`ab = f (g∘T^(−p)) u^(p+q)`, so `ι(ab) = u^(−p−q) f (g∘T^(−p))`. Using `g u^(−p) = u^(−p)(g∘T^(−p))`,
`ι(b)ι(a) = u^(−q) g u^(−p) f = u^(−q−p) (g∘T^(−p)) f`. Locally constant functions commute, so `ι(ab) = ι(b)ι(a)`,
and `ι` is an additive involution. So `ι` is an anti-automorphism of `R_Y`. Entrywise `ι` followed by transpose is a
ring isomorphism `M_m(R_Y)^op → M_m(R_Y)`. It suffices to treat a ring isomorphism `ψ: M_m(R_X) → M_m(R_Y)`.

**(R2) The ring invariant.** For a unital ring `A`, `K_0(A)` with the cone `K_0^+(A)` (classes of idempotent matrices)
and the unit `[1_A]` is invariant under ring isomorphism. Morita invariance gives
`(K_0(M_m A), K_0^+, [1]) ≅ (K_0(A), K_0^+, m[1_A])`. So `ψ` gives an isomorphism of groups
`φ: K_0(R_X) → K_0(R_Y)` with `φ(K_0^+(R_X)) = K_0^+(R_Y)` and `φ(m[1]) = m[1]`.

**(R3) The group.** By `subshift-crossed-product-k0-is-coinvariant-group` (Theorem K), the inclusion `LC(X,k) ⊆ R_X`
induces `K_0(R_X) ≅ K^0(X,T)`, with `[χ_U] ↦ [χ_U]`. Theorem K is stated for `k = F_q`. Its proof uses only that
`LC(X,k)` is a directed union of finite products `k^P` and that `K_(−1)(k) = 0`, so it holds for every field `k`.

**(R4) The cone.** Under (R3), `K_0^+(R_X) = K^0(X,T)^+`.
- (⊇) A nonnegative `f ∈ C(X,Z)` is `Σ n_i χ_(U_i)` with disjoint clopen `U_i` and `n_i ≥ 0`. It is the class of the
  diagonal idempotent that repeats `χ_(U_i)` `n_i` times.
- (⊆) Let `e ∈ M_N(R_X)` be a nonzero idempotent.
  - Every invariant probability measure of a minimal system has full support. For each ergodic one `μ`,
    `cantor-z-crossed-product-embeds-in-continuous-factor` (Ara–Claramunt) gives a faithful Sylvester matrix rank
    function `rk_μ` with `rk_μ(χ_U) = μ(U)`.
  - A Sylvester rank function is additive on orthogonal idempotents and constant on equivalence classes of idempotent
    matrices. So it induces a homomorphism `s_μ: K_0(R_X) → R` with `s_μ[χ_U] = μ(U)` and `s_μ[e] = rk_μ(e) > 0`.
  - The classes `[χ_U]` generate `K_0(R_X)` by (R3). So `s_μ([f]) = ∫ f dμ` for all `f`, and `∫ a dμ > 0` for
    `a = [e]` and every ergodic `μ`.
  - `μ ↦ ∫ f dμ` is affine and weak* continuous on the compact convex set `M(X,T)`, whose extreme points are the
    ergodic measures. So its minimum is attained at an ergodic measure (Bauer), and `∫ a dμ > 0` for all `μ ∈ M(X,T)`.
  - By part 2, (I2) (states of `K^0(X,T)` are exactly the maps `[f] ↦ ∫ f dμ`) and (I3) (in a simple dimension group,
    an element strictly positive on every state is positive), `a ∈ K^0(X,T)^+`.

**(R5) The unit.** `K^0(X,T)` is torsion-free.
- Suppose `n f = g − g∘T^(−1)` with `n ≥ 1` and `f, g ∈ C(X,Z)`. Then `g mod n` is a continuous invariant function
  `X → Z/n`, hence constant by minimality. So `g = c + n h` with `c ∈ Z` and `h ∈ C(X,Z)`.
- Then `n f = n(h − h∘T^(−1))`, so `f = h − h∘T^(−1)` and `[f] = 0`.
- By (R2)–(R4), `φ` is an isomorphism of ordered groups with `m(φ[1_X] − [1_Y]) = 0`. So `φ[1_X] = [1_Y]`.

**(R6) Conclusion.** `φ` is an isomorphism of unital ordered groups `(K^0(X,T), K^0^+, [1]) → (K^0(Y,S), K^0^+, [1])`.
Part 2, (I1) gives strong orbit equivalence. ∎

Model tests and scope:
- **Calibration.** Flip conjugacy `h T h^(−1) = S^(±1)` gives `R_X ≅ R_Y`, through `f ↦ f∘h^(−1)` and `u ↦ u^(±1)`.
  Theorem R then returns strong orbit equivalence, which is weaker than flip conjugacy, as it must be.
- **What K-theory cannot see.** Strong orbit equivalence classes contain systems of different entropy (part 2, (I1)
  context). So no argument through `(K_0, K_0^+, [1])` alone upgrades Theorem R to flip conjugacy. That upgrade would
  need a diagonal-preserving reconstruction; whether an arbitrary ring isomorphism `R_X ≅ R_Y` can be moved onto the
  diagonal is not claimed.
- **Unit caveat on main.** The Attempts of `subshift-elementary-group-isomorphism-forces-orbit-equivalence` say the
  unit `3[1]` yields only strong orbit equivalence of the height-3 Kakutani towers. (R5) removes the caveat: the
  isomorphism is the same map, and torsion-freeness forces `[1] ↦ [1]`.

## 2. Consequences for the groups

**Corollary R1 (q odd).** Let `q` be odd and `X, Y` infinite minimal subshifts. If `GL_3(R_X) ≅ GL_3(R_Y)`, then `X`
and `Y` are strongly orbit equivalent. *Proof.* `subshift-gl3-iso-gives-matrix-ring-iso-odd-q` (Zel'manov) gives
`M_3(R_X) ≅ M_3(R_Y)` or its opposite. Apply Theorem R with `m = 3`. ∎

**Corollary R2 (standard isomorphisms, every q).** Suppose an isomorphism `EL_3(R_X) → EL_3(R_Y)` is the restriction
of a ring isomorphism or anti-isomorphism `M_3(R_X) → M_3(R_Y)`, composed with conjugation by an element of
`GL_3(R_Y)`. Then `X` and `Y` are strongly orbit equivalent.

This is the reduction for the note's groups: for `q = 2`, "`G_X ≅ G_Y` implies strong orbit equivalence" follows once
every isomorphism of these groups is standard. That is §3.

## 3. The group step (a) in characteristic 2: OPEN

Target: for `q = 2`, every isomorphism `EL_3(R_X) → EL_3(R_Y)` is standard (induced as in Corollary R2).

Literature status:
- Zel'manov 1985 and Golubchik–Mikhalev 1981/83 assume `1/2`.
- Golubchik 1992 (Contemp. Math. 131, "`GL_n`, `n ≥ 4`, over an associative ring") is recalled secondarily as covering
  `n, m ≥ 4` over arbitrary associative rings (part 2, (I4)). Primary source not read. It concerns `GL_n` and needs
  `n ≥ 4`.
- Golubchik 1995 (Fund. Prikl. Mat. 1:1, 311–314) treats automorphisms of `PH` that are the identity on `PE_n(R)`, for
  orders in regular rings. That is not an isomorphism theorem for `E_3` (abstract, part 2, (I5)).

Firewalls:
- **F-GL (E_3 is not GL_3).** For `k = F_2`, the ABC fibration gives
  `0 → coker(1−T_*: K_1(LC(X,F_2)) → K_1(LC(X,F_2))) → K_1(R_X) → ker(1−T_*: C(X,Z) → C(X,Z)) → 0`.
  The left term is 0, since `K_1(LC(X,F_2)) = LC(X,F_2^×) = 0`. The right term is `Z` (constants, by minimality). So
  `K_1(R_X) ≅ Z`, generated by `[u]`. So `diag(u,1,1) ∉ EL_3(R_X)`. Theorems about groups between `GL_n` and its
  elementary subgroup apply only once an isomorphism of the `EL_3` is known to extend.
- **F-MIN (no minimal idempotents).** `R_X` has no minimal idempotents (every nonempty clopen set splits). Rank-one
  and residual-space methods (O'Meara, Hahn) have no starting point.
- **F-EA (exotic elementary abelian 2-subgroups).** Towers of height `h` put `GL_(3h)(F_2)` inside `EL_3(R_X)`. There
  `N_1 = E_12 + E_34` and `N_2 = E_13 + E_24` satisfy `N_1² = N_2² = 0`, `N_1 N_2 = N_2 N_1 = E_14 ≠ 0` and
  `((1+N_1)(1+N_2))² = 1`. So `⟨1+N_1, 1+N_2⟩ ≅ C_2²` lies in no unipotent radical
  `U_P = {g : (g−1)R^3 ⊆ P, (g−1)P = 0}` (products vanish in `U_P`). Maximal elementary abelian 2-subgroups do not
  single out the radicals `U_P`.

A usable substitute for Zel'manov's involutions (the idea for a future lane):
- In characteristic 2, if `x^3 = 1` in a ring, then `ε(x) = 1 + x + x²` is an idempotent. Indeed
  `ε² = 1 + x² + x^4 = 1 + x + x²`, and `ε` projects onto `ker(x − 1)` along `ker(1 + x + x²)`.
- For a group isomorphism `φ` into the units of a characteristic-2 ring, `ε(φ(x))` is again an idempotent. This
  replaces Zel'manov's `(1 − σ)/2`.
- Every diagonal idempotent arises: `E_33 = ε(diag(A,1))` with `A = [[0,1],[1,1]] ∈ GL_2(F_2)` of order 3 and no fixed
  vector. Locally constant versions give `χ_U E_33 + χ_(X∖U) E_ii`.
- What is missing is the rest of Zel'manov's machinery in characteristic 2: additivity of `x ↦ φ(1+x) − 1` on the
  Peirce spaces `ε_i M_3 ε_j`, and a quadratic Jordan specialization theorem. No such theorem was located.
