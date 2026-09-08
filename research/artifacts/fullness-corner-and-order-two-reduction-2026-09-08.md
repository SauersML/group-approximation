# Dropping ambient fullness: corner certificate and order-two reduction

2026-09-08.  Ingestion record for a forwarded dossier
("Fullness-Corner-Theorem-and-Order-Two-Reduction").  Every algebraic
identity below was re-derived here before any node was written.  The
dossier's own analytic input is the repository's full-defect theorem; it
supplies no new analytic content, and none is claimed by the nodes.

## What the dossier proves

1. **Corner certificate.**  A countable unital ring `R` carrying a nonzero
   idempotent `p` and `x_0,x_1,y_0,y_1 in pRp` with `y_i x_j = delta_(ij) p`
   has `EL_n(R)` non-MF for every `n >= 2`, and every MF-target
   homomorphism kills the corner-embedded `EL_n(pRp)`.  This is strictly
   weaker than the ambient fullness hypothesis `R(1-st)R = R`, which is the
   case `p = 1`.
2. **Strictness witness.**  `R = F_2<S,T> + M_fin(N, L_{F_2}(1,2))` has a
   nonzero defect `e = 1-ST` of additive order two which is **nonfull**
   (`R/ReR = F_2[z,z^(-1)]`), which admits no full-defect pair at all, and
   whose corner `eRe = L_{F_2}(1,2)` satisfies the certificate.
3. **Method obstruction.**  No `M_d(J_{F_2})`, `d` finite, contains a
   nonzero properly infinite idempotent; the same holds for `A_2`.  So the
   corner certificate cannot reach the binary Jacobson endpoint or the
   universal order-two ring, even after finite matrix amplification.
4. **Universal order-two reduction.**  For each fixed `n >= 2`, the
   universal additive-order-two question is equivalent to non-MF of
   `EL_n(A_2)` for the single ring
   `A_2 = Z<S,T | TS=1, 2(1-ST)=0>`, and equivalent to marked collapse of
   `e_12(1-ST)` there.
5. **Rank extension.**  The binary Jacobson finitary-kernel, faithful-mark
   and MF-radical-dichotomy statements hold for every `n >= 2`, using the
   two-outer-row commutator identity
   `[I+Q_ac E_12, I+Q_cb E_21] = I + Q_ab E_11`.
6. **Normal forms.**  A defect of finite additive order `m` forces
   `m F_Z <= K <= m J_Z` on the kernel of `J_Z ->> R_0`, and
   `R_0 = J_(Z/m) x_((Z/m)[z,z^(-1)]) D/Lambda`; infinite additive order
   forces `K = 0`, i.e. `J_Z` embeds.

## Reconciliation with the graph as it stands today

`finite-additive-order-one-sided-defects-are-mf-invisible` (established
2026-09-08 by `torsion-defect-universal-rank-transport-proof`) already
answers the dossier's item 4 **affirmatively for every `n >= 4`**, over the
same universal ring: that route's `R_q = Z<S,T | TS=1, q(1-ST)=0>` is
literally `A_2` at `q = 2`.  Its proof consumes property (T) of
`E_3(R_q)` through Ershov--Jaikin-Zapirain.

So the dossier's "unresolved analytic endpoint" is unresolved only at
**ranks two and three**.  That restriction is not cosmetic:

* `elementary-rank-descent-to-two` needs a properly infinite unit, which
  `A_2` does not have, and by the dossier's own Theorem 3 argument it does
  not acquire one in any finite matrix amplification.  So the standing
  rank-descent route is unavailable for exactly this ring.
* The dossier's Theorem 4 keeps its content there, and adds something the
  rank-transport node does not assert at any rank: statement 3, the
  **marked** collapse of `e_12(1-ST)`, transported to every ring in the
  class through the defining ring map.

The nodes landed from this dossier therefore state the open endpoint as
`order-two-universal-non-mf-at-ranks-two-and-three`, and record the
`n >= 4` case as already established elsewhere rather than restating it.

`finite-modulus-finitary-kernels-have-uniform-support-rank` already
identifies the defect ideal of `R_q` as `M_fin(Z/q)` and exhibits a normal
locally finite subgroup of `E_4(R_q)`; it explicitly does not describe the
symbol quotient and does not identify the whole kernel.  The node
`order-two-universal-ring-has-finitary-symbol-sequence` supplies exactly
those two missing pieces, at every rank `n >= 2`.

## What was re-derived here

* `y_1 f x_1 = y_1x_1 - (y_1x_0)(y_0x_1) = p` for `f = p - x_0y_0`, so the
  certificate produces a **single-element** fullness witness inside `pRp`.
  This is the `(2) => (1)` half of
  `full-idempotent-ring-has-properly-infinite-unit`, applied to `B = pRp`
  rather than to `R`.
* `U |-> U + (1-p)I_n` is a group homomorphism `GL_n(pRp) -> GL_n(R)` with
  inverse `U^(-1) + (1-p)I_n`, injective because `p` is recovered as the
  image of the unit of the corner, and it carries `p I_n + aE_ij` to
  `I_n + aE_ij`.  Cross terms vanish entrywise because every entry of `U`
  absorbs `p` on both sides.
* `E_00(b) = S^0 E_00(b) e T^0` and `E_ij(b) = S^i E_00(b) e T^j`, giving
  `ReR = M_fin(N,B)` in the strictness witness; the quotient computation
  uses that a scalar Laurent polynomial acting on all far basis vectors is
  a finite matrix only if every coefficient vanishes.
* The centre of that ring is `F_2 1`, so the example is not a product in
  disguise: commuting with all matrix units forces `bI`, and the eventual
  Laurent form forces `b in F_2`.
* Diagonal-partial-sum argument for faithfulness of the shift
  representation of `J_C` (`C = Z` or `Z/m`), the resulting monomial basis
  `S^iT^j`, and the coefficient extraction `Q T^i a S^j Q = cQ`.
* `Q_(ij)Q_(kl) = delta_(jk) Q_(il)` for `Q_(ij) = S^i Q T^j`, and the
  two-outer-row commutator `[I+Q_(ac)E_12, I+Q_(cb)E_21] = I+Q_(ab)E_11`,
  which needs `A^2 = (B')^2 = B'A = 0` and gives `I + AB'`.
* Split injection `V (+) V -> V` over a field forces `V = 0`, applied
  first to `bar p K^d` for `K = F_2(z)` (resp. `Q(z)` for `A_2`), then to
  the finite-dimensional corner that survives once `bar p = 0`.
* `A_2 -> J_{F_2} x D` has kernel exactly `2 F_Z`, using torsion-freeness
  of `D = Z[z,z^(-1)]`; surjectivity onto the fibre product by correcting
  a lift's symbol inside `2 J_Z`.
* Residual finiteness of `EL_n(F_2[z,z^(-1)])` and `EL_n(Z[z,z^(-1)])`:
  clear denominators to a polynomial, pick a monic irreducible dividing
  neither `z` nor that polynomial (Euclid), specialize entrywise.
* Simplicity of `L_n = GL_fin(N x {1..n}, F_2)` from
  `[g,u] = I + (g-I)v e_k^*` at a fresh coordinate `k`.
* Proposition 5: `me = 0` gives `m F_Z <= K`; `ce = 0` for every integer
  matrix coefficient `c` of `a in K` gives `m | c` and so `K <= m J_Z`;
  `[mJ_Z, J_Z] <= m F_Z <= K` gives centrality of `mJ_Z/K` in `R_0`.

## Two scope corrections applied while wiring

* The dossier states its supplied theorem (F) at `n >= 2`.  The
  repository's `n >= 2` form is `full-defect-ring-non-mf-at-rank-two`;
  `full-complementary-idempotent-elementary-full-mf-radical` is the
  `n >= 4` form and is the analytic input to it.  The corner nodes require
  the rank-two node, not the rank-four one.
* The dossier's "ideal-level" remark (every `e_ij(a)`, `a in RpR`, is
  killed) is stated only for `n >= 3`, because it uses a third index.
  That restriction is carried into the node; the non-MF conclusion and the
  embedded-corner collapse are unrestricted above rank one.

## Not asserted

No new analytic theorem.  No Lean certification: nothing in this region
carries a formalization marker, and the manuscript's Lean markers for the
full-defect theorem record rank four and do not transfer.  No priority
claim for the algebraic consequences or the reduction.  The dossier
reports exact symbolic checks (256 matrix-unit products, 48 two-row
commutators, integer coefficients, no truncation of the shift
representation); those runs are quoted, not reproduced here, and no node
depends on them.
