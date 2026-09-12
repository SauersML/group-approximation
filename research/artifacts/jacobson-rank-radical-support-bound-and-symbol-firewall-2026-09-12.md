# The Jacobson rank radical: the support bound is free, the cell is a lamplighter, and a symbol firewall

Lane `w4-jacobson-radical`, 2026-09-12, wave 4. Target: the open claim
`binary-jacobson-el3-rank-radical-is-the-finitary-kernel`, in its rank-four form (every
characteristic-two rank model of `EL_4(J)` or `EL_5(J)` kills `x_13(Q)`), which carries the payoff.
It supports `jacobson-compression-cell-is-a-commuting-lamplighter` and
`jacobson-amenable-symbol-subgroups-are-amenable`.

Summary.
* **Section 1.** Block 2 of the target node is not a block. In normalized rank a head-retaining
  model already satisfies the uniform finite-support hypothesis of the rank-weighted transport
  theorem, with constant `4/c_0`, and every cutoff step of that proof becomes exact. What is left is
  one step, commutant transport along compressors, and the head dies in a model exactly when that
  step holds for it.
* **Section 2.** The commuting element of the manuscript's compression cell lies in a finite simple
  group `K_0 = GL_3(F_2)` in the commutant of the Kazhdan subgroup `H`, whose compressor conjugate
  `K_1` sits inside `H`. The conjugates `u^j K_0 u^(-j)` pairwise commute.
* **Section 3.** Every subgroup of `EL_n(J)` with amenable symbol image is amenable. The whole cell
  (compressor, `K_0`, all finitary matrices, the constants), and separately the "tilted constants"
  built from `S` and `T`, lie in such subgroups and retain the head. So faithful models exist in
  every approximation row, and a proof must evaluate the model on elements whose symbols generate a
  nonamenable group.

## 0. Setting

* `J = F_2<S,T | TS = 1>` acts on `l(N)` with basis `delta_j`: `S delta_j = delta_(j+1)`,
  `T delta_j = delta_(j-1)`, `T delta_0 = 0`. Put `Q = 1 - ST`, the projection onto `delta_0`, and
  `e_ab = S^a Q T^b = delta_a (x) delta_b*`. Then `QS = 0`, `TQ = 0` and `e_ab e_cd = [b = c] e_ad`.
* `E_4 = EL_4(J)`, with root elements `x_ij(r)`. `H = EL_3(J)` occupies coordinates `1, 2, 3`. It has
  property (T), since `J` is finitely generated.
* **The compression cell** (manuscript Lemma `lem:ring-compression-cell`, Lean
  `manuscriptRankFourCompressionCell`).
  * `u in E_4` satisfies `u x_ij(a) u^(-1) = x_ij(SaT)` for `1 <= i != j <= 3` and `a in J`. So
    `u H u^(-1) <= H`.
  * `c = diag(1, 1, 1, 1 + QT)` lies in `C_(E_4)(H)`.
  * `u c u^(-1) = x_12(Q)`, and the head is `[x_12(Q), x_23(1)] = x_13(Q)`.
* **Symbol.** `S -> z`, `T -> z^(-1)` gives `J -> F_2[z, z^(-1)]` with kernel `F = span{e_ab}`
  (`binary-jacobson-mark-dichotomy-holds-from-rank-two`), hence
  `pi : E_4 -> EL_4(F_2[z, z^(-1)])`.
  * `L := ker pi` consists of matrices `g` with `g - 1` in `M_4(F)`. Each such `g - 1` has finitely
    many nonzero entries, so finitely many of them preserve a finite coordinate span and fix every
    other basis vector. So `L` is locally finite.
  * `L` contains every finitary elementary matrix: `x_ij(e_ab)` for `i != j`, and
    `1 + E_((i,a),(i,b)) = [x_ik(e_ac), x_ki(e_cb)]` for `a != b`. So `L = GL_fin(N x {1,...,4}, F_2)`.
  * `pi(u) = diag(z, z, z, z^(-3))`, since the off-diagonal entries of `u` lie in `F`.
* A **rank model** is a homomorphism `sigma : E_4 -> M^x` into a rank ultraproduct over `F_2`, with
  rank function `rk`. Put `c_0 = rk(sigma(x_13(Q)) - 1)`. The model is *head-retaining* if `c_0 > 0`.

## 1. The support bound is automatic in normalized rank

**Proposition 1.** Let `G` be a group, `H <= G`, `A` a locally finite normal subgroup, `a in A`, and
`sigma : G -> M^x` a homomorphism into a rank ultraproduct over any field, with
`c_0 = rk(sigma(a) - 1) > 0`. Suppose `rk(sigma(b) - 1) >= kappa c_0` for all `b in A \ {1}`, for
some `kappa > 0`.

1. **Support bound.** For every finite `K <= A` and every `b in K \ {1}`,
   `rk(1 - e_K) <= (kappa c_0)^(-1) rk(sigma(b) - 1)`, where `e_K M = Fix_r(sigma(K))`. So
   hypothesis (1) of `uniform-finite-support-rank-gap-upgrades-compression-collapse` holds in `sigma`
   with `C = (kappa c_0)^(-1)`, uniformly over all finite stages.
2. **No cutoffs.** With `q(g) := rk(sigma(g) - 1)`: `q` is subadditive, inverse-invariant and
   conjugation-invariant, `{q = 0} = ker sigma`, and `q(a) = c_0 > 0`. These are the rank forms of
   steps (5)-(10) of `research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md`,
   with the cutoff `e_n` replaced by `1` and every error term equal to `0`.
3. **The one remaining step.** `sigma(D_G(H)) = 1` iff
   `sigma(u) sigma(C_G(H)) sigma(u)^(-1) <= C_M(sigma(H))` for every `u` with `u H u^(-1) <= H`.
4. **Jacobson instance.** For `E_4`, `A = L`, `a = x_13(Q)` and a head-retaining `sigma`:
   * `kappa = 1/4`;
   * the normal closure of the head in `E_4` is `L`;
   * `sigma` kills `L` iff it kills the head iff `sigma(u) sigma(c) sigma(u)^(-1) = sigma(x_12(Q))`
     commutes with `sigma(x_23(1))`. That is the transport in (3) for the cell's own `u`, `c` and
     `h = x_23(1)`, and transport for every compressor implies it.

*Proof.*
1. `rk(1 - e_K) <= 1` and `rk(sigma(b) - 1) >= kappa c_0`.
2. `xy - 1 = (x - 1)y + (y - 1)`, `x^(-1) - 1 = -x^(-1)(x - 1)`, and conjugation preserves rank. The
   relations of `G` hold exactly in `M`.
3. `sigma([g, h]) = 1` iff `sigma(g)` and `sigma(h)` commute. The generators of `D_G(H)` are
   `[u z u^(-1), h]` with `z in C_G(H)`, `h in H`.
4. **`kappa = 1/4`.** Every nontrivial element of `L` lies in some `GL_m(F_2)` with `m >= 4`, where
   all transvections are conjugate. Lemma 3 of
   `research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md` gives
   `rk(sigma(b) - 1) >= c_0/4`.

   **Normal closure.** `L = GL_fin(N x {1,...,4}, F_2)` is generated by its transvections, and they
   are all conjugate in `L` to `x_13(Q)`. So the normal closure of the head is `L`.

   **Equivalence.** `sigma` kills the head iff it kills `L`. Since
   `x_13(Q) = [u c u^(-1), x_23(1)]`, this happens iff `sigma(u c u^(-1))` commutes with
   `sigma(x_23(1))`.

QED

**Reading.**
* **Block 2.** The target lists a failure of `binary-finitary-transvection-uniformly-controls-active-rank`
  over `F_2` (natural modules, where transvections move `1/m` of the dimension) as a second block.
  * In the operator-norm proof that bound confines the active part of `A` to rank `C r_n`, so that
    Hilbert norms rescaled by `r_n = rank(T_n - I)` stay bounded.
  * In normalized rank the head's displacement `c_0` is already a positive fraction of the space.
    The constant `4/c_0` works at every stage, whatever the natural-module content of the finite
    representations.
  * So Block 2 is an artifact of rescaling. It is not a block.
* **Block 1 is everything.** Item (3) is Theorem 10 of
  `research/artifacts/rigid-compression-defect-ladder-2026-09-11.md` with `A(L) = C_U(L)`, the
  commutant.
  * (A1), (A2) and (A4) hold.
  * (A3), a faithful size, is absent, and property (T) gives no rank rounding
    (`kazhdan-rank-ultraproducts-can-have-diffuse-commutants`,
    `research/artifacts/rank-row-compression-audit-2026-09-12.md` Section 3).
  * So the Jacobson rank radical is exactly the rank-row transport problem for the one pair
    `(H, u)`, with the extra finitary structure of Section 2.

## 2. The cell is a commuting lamplighter

Put `K_1 = <x_ij(Q) : 1 <= i != j <= 3>`.

**Proposition 2.**
1. `K_1 = GL_3(F_2)`, acting naturally on `span{delta_0^(1), delta_0^(2), delta_0^(3)}`. `K_1 <= H`,
   and `K_1` commutes with `u H u^(-1)`.
2. `K_0 := u^(-1) K_1 u` lies in `C_(E_4)(H)`, and `c in K_0`.
3. The groups `K_j := u^j K_0 u^(-j)`, `j in Z`, pairwise commute.
   * For `j >= 1`, `K_j = <x_ik(e_(j-1,j-1))> <= H`.
   * For `j <= 0`, `K_j <= C_(E_4)(H)`.
   All `K_j` lie in `L`.
4. **Constants.** `EL_3(F_2) <= H` centralizes `K_j` for `j <= 0`. For `j >= 1` it acts on `K_j` as
   conjugation by its index-`(j-1)` restriction. `u^(-1) x_23(1) u = w_0 x_23(1)`, with
   `w_0 = u^(-1) x_23(Q) u in K_0`.
5. **In models.** In every rank model, `sigma(K_0)` is a genuine representation of `GL_3(F_2)`
   commuting with `sigma(H)`. `sigma(K_0) != 1` iff `sigma(K_1) != 1` iff the head is retained.

*Proof.*
1. **`K_1`.**
   * `x_ij(Q) = 1 + E_ij (x) (delta_0 (x) delta_0*)` are the elementary matrices on that span, and
     they generate `SL_3(F_2) = GL_3(F_2)`.
   * `u H u^(-1)` is generated by `x_kl(SaT)`.
   * `Q SaT = (1 - ST) SaT = 0` and `SaT Q = 0`, using `TS = 1`. So both products of the coefficients
     vanish, and `(1 + Q E_ij)(1 + SaT E_kl) = 1 + Q E_ij + SaT E_kl` in either order.
2. Conjugate (1) by `u^(-1)`. `c in K_0` because `u c u^(-1) = x_12(Q) in K_1`. `L` is normal.
3. **Pairwise commuting.**
   * For `j >= 1`, `u^(j-1) x_ik(Q) u^(1-j) = x_ik(S^(j-1) Q T^(j-1)) = x_ik(e_(j-1,j-1))`, and
     `K_j <= u^(j-1) H u^(1-j) <= H`.
   * For `j <= 0`, `K_j <= C(u^j H u^(-j))`, and `H <= u^j H u^(-j)`, since `u^(-j) H u^j <= H`. So
     `K_j <= C(H)`.
   * For `i < j`, conjugate by `u^(-i)`. `K_0` and `K_(j-i)` commute, because `K_(j-i) <= H` and
     `K_0 <= C(H)`.
4. **Constants.**
   * For `j <= 0` this follows from (3).
   * For `j >= 1`, write `x_ik(1) = x_ik(e_(j-1,j-1)) x_ik(1 - e_(j-1,j-1))`. The second factor has
     coefficient products `0` with `e_(j-1,j-1)`, so it commutes with `K_j`, and with the
     index-`(j-1)` parts of the other root elements.
   * The identity for `u^(-1) x_23(1) u` is the cell identity `u x_23(1) u^(-1) = x_23(ST)` together
     with `x_23(1) = x_23(Q) x_23(ST)`.
5. **Models.** Relations hold exactly in `M`, and `GL_3(F_2)` is simple. The head `x_13(Q)` lies in
   `K_1`.

QED

**Reading.** The operator-norm proof shows `sigma(K_1)`, the transported commutant cell, is central
in `sigma(H)`. `K_1` is a nonabelian simple subgroup of `H`, so `sigma(K_1) = 1`. In the rank row
that is item (3) of Proposition 1 applied to one finite simple group `K_0`. So no rounding of
`sigma(K_0)` is needed. What is needed is to transport commutation with `sigma(H)` along `sigma(u)`.
