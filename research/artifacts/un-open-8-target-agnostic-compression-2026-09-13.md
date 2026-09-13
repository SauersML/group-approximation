# One compression lemma, read by the target

Lane `un-open-8`, 2026-09-13. Written proofs, unreviewed. Credits: the compression mechanism and the rank-four
compression cell are the non-MF manuscript's (`non_mf_groups_exist.tex`, eq. (intrinsic-defect) l.167, Lemma
l.866, Thm l.478, Cor l.581, Thm l.646). The finite-dimensional invisibility of one specific defect is
`unsquared-defect-finite-model-invisible`. The Hilbert–Schmidt failure is `un-hyperlinear-paradox` §3.

## 0. The principle

For `L <= G` the intrinsic defect is `D_G(L) = << [ucu^-1, l] : uLu^-1 <= L, c in C_G(L), l in L >>_G`.

- **Lemma C.** A homomorphism kills a defect as soon as the target contains a *rigid support* for `L`: a
  subgroup that the compressor conjugates onto itself.
- **Rigidity** is where the targets differ:
  - finite groups: counting;
  - linear groups: algebraic dimension;
  - ring models: rank;
  - MF targets: Kazhdan projections in a finite C*-algebra (needs (T); gives only a Hilbert–Schmidt form).
- It fails for tracial targets.
- **The two papers** are two readings of Lemma C:
  - **non-MF paper:** a full defect exists, so the rigid targets see nothing.
  - **Pestov 9.1:** the ring is directly finite, so no ring defect exists and exact matricial models can exist.

## 1. Lemma C

**Lemma C.** Let `ψ: G -> H` be a homomorphism, `L <= G`, `u in G` with `uLu^-1 <= L`, `c in C_G(L)`, `l in L`.
Suppose `S <= H` satisfies:
- (S1) `ψ(L) ⊆ S`;
- (S2) every element of `H` commuting with `ψ(L)` commutes with `S`;
- (S3) `ψ(u) S ψ(u)^-1 = S`.

Then `ψ([ucu^-1, l]) = 1`.

*Proof.* `ψ(c)` commutes with `ψ(L)`, hence with `S` by (S2). So `ψ(ucu^-1) = ψ(u)ψ(c)ψ(u)^-1` commutes with
`ψ(u)Sψ(u)^-1 = S` by (S3). Since `ψ(l) in S` by (S1), `ψ([ucu^-1,l]) = [ψ(ucu^-1), ψ(l)] = 1`. ∎

**Consequence.** If a support satisfying (S1)–(S3) exists for every compressor of `L`, then `ψ` kills every
generator of `D_G(L)`, hence `D_G(L)`, because `ker ψ` is normal.

## 2. Rigid targets

**(F) Finite targets.** `H` finite, `S = ψ(L)`. (S1) and (S2) are trivial. For (S3), `ψ(u)Sψ(u)^-1 = ψ(uLu^-1) ⊆ S`
and both sides have `|S|` elements. No property (T) is used.

**(Z) Linear targets.** `H = GL_d(K)` for any field `K`. Let `S` be the Zariski closure of `ψ(L)` in `GL_d(K̄)`, and
let `H` act inside `GL_d(K̄)`.
- (S1) holds by construction.
- (S2): for fixed `h`, `{g : gh = hg}` is Zariski closed. If it contains `ψ(L)`, it contains `S`.
- (S3): conjugation by `ψ(u)` is a variety automorphism, so `ψ(u)Sψ(u)^-1` is the closure of
  `ψ(uLu^-1) ⊆ ψ(L)`, hence contained in `S`. It is a closed subgroup isomorphic to `S` as a variety, with the same
  dimension and the same number of irreducible components.
  - Each component of `ψ(u)Sψ(u)^-1` is irreducible closed of dimension `dim S` inside `S`, so it is a component of `S`.
  - Distinct components of `ψ(u)Sψ(u)^-1` are distinct components of `S`, and there are equally many.
  - So `ψ(u)Sψ(u)^-1 = S`.

No property (T) is used.

**(R) Ring targets (towers).** A unital ring homomorphism `φ: R -> Q` into a directly finite ring maps `ts = 1` to
`φ(t)φ(s) = 1`. So `φ(s)φ(t) = 1` and `φ(1 - st) = 0`, and `φ` kills the ideal `ReR`. Every `M_N(F)` over a
field is directly finite (rank), and so is every algebraic ultraproduct `prod_omega M_(d_k)(F_k)`. Hence
exact matricial models (Pestov's towers) exist only for rings whose defect ideals all vanish in the model.

**(M) MF targets, the manuscript.** For an operator norm asymptotic representation `(V_n)` of `G` and
`L` with (T), take:
- `H`: the unitary group of the adjoint norm corona `B = prod B(M_(d_n)) / ⊕`, a norm matrix corona, hence finite;
- `S`: the Hilbert–Schmidt asymptotic commutant `C_2(V,L)`, the range of the Kazhdan projection `P` of `L` in `B`.

(S3) is tex Thm l.478: `U^*PU <= P`, and finiteness forces equality. The conclusion is Cor l.581: every
`d in D_G(L)` has `||V_n(d) - 1||_HS -> 0`. That is a Hilbert–Schmidt statement, not an exact one. The exact kill
needs a normal (T) subgroup `K <= D_G(L)` and Thm l.646.

**(Tr) Tracial targets: no rigid support.** For a homomorphism into `U(M^omega)`, the left Kazhdan projection of
`L` lies in the finite algebra `M^omega`, but the commutant support needed in (M) lives in `B(L^2(M^omega))`,
which is not finite. Then (S3) has no counting argument, and this is exactly the gap recorded in
`un-hyperlinear-paradox` §3 (open: `hyperlinear-groups-kill-rigid-compression-defects`).

| target | rigid support `S` | rigidity input | conclusion | (T) needed |
|---|---|---|---|---|
| finite group | `ψ(L)` | counting | `ψ(D_G(L)) = 1` | no |
| `GL_d(K)` | Zariski closure | dimension, components | `ψ(D_G(L)) = 1` | no |
| directly finite ring model | — (ring level) | rank | `φ(ReR) = 0` | no |
| MF group (norm corona) | range of Kazhdan projection in adjoint corona | stable finiteness of corona | HS-invisible; exact on normal (T) `K <= D` | yes |
| tracial ultraproduct | none known | — | open | — |

**Corollary (linear groups have no compression defects).** Taking `ψ = id`: if `G` is finite or linear over a
field, then `D_G(L) = 1` for every `L <= G`.

Model test: in `GL_2(Q)`, take `L` the integer upper unitriangular matrices and `u = diag(2,1)`, so `uLu^-1 = 2Z`,
a proper compression. Every `c in C_G(L)` lies in `Q^x · (upper unitriangular over Q)`, so `ucu^-1` again
commutes with `L`, and the defect is trivial as predicted.

## 3. Corollary 1: one-sided defect ideals die in every linear image

**Theorem.** Let `R` be a unital ring, `s,t in R` with `ts = 1`, `e = 1 - st`, and `N >= 4`. Every homomorphism
from `EL_N(R)` to a finite group or to `GL_d(K)` (any field `K`, any `d`) is trivial on `E_N(R, ReR)`. If `R` is
simple and not directly finite, then every such homomorphism is trivial. No finite generation and no property (T)
is assumed.

*Proof.*
1. **The cell.** tex Lemma l.866 (printed) gives, in `EL_4(R)` with `L = EL_3(R)` on coordinates `1,2,3`, elements
   `u, c` with `uLu^-1 <= L`, `c in C(L)` and `[ucu^-1, e_23(1)] = e_13(e)`.
2. **Embedding.** Embed `EL_4(R)` in `EL_N(R)` on the first four coordinates; the same `u, c, L` still satisfy the
   compressor and centralizer relations. By §2 (F)/(Z) and Lemma C, `ψ(e_13(e)) = 1`.
3. **Normal closure.** The Steinberg relations `[e_ij(x), e_jk(y)] = e_ik(xy)` for distinct `i,j,k` hold in `EL_N(R)`.
   From `e_13(e)` in `ker ψ`:
   - `[e_13(e), e_32(b)] = e_12(eb)`;
   - `[e_31(a), e_12(eb)] = e_32(aeb)`.

   So `e_32(aeb) in ker ψ` for all `a,b`.
4. **All roots.** Conjugating by `w_ij = e_ij(1)e_ji(-1)e_ij(1) in EL_N(R)` moves `e_32(y)` to `e_ij(±y)` for every
   `i != j`. Additivity `e_ij(y)e_ij(y') = e_ij(y+y')` gives `e_ij(x) in ker ψ` for all `x in ReR`.
5. **Conclusion.** `E_N(R, ReR)` is the normal closure of these elements, so it lies in `ker ψ`. If `R` is simple
   and `e != 0`, then `ReR = R` and `E_N(R,R) = EL_N(R)`. ∎

## 4. Calibration

| ring `R` | defect ideal `ReR` | linear/finite images of `EL_N(R)`, `N >= 4` | MF images | exact matricial models |
|---|---|---|---|---|
| `L_k(1,2)` | `R` | trivial (§3) | trivial (tex Cor l.1016) | none |
| `LC(X,F_q) ⋊ Z`, X minimal infinite | no defects (directly finite) | §3 vacuous; `EL_N/Z` is infinite f.g. simple, so it is not linear | LEF (Pestov) | yes (towers) |
| algebraic Toeplitz `k<s,t : ts=1>` | finitary matrices `M_fin(k)` | kill `E_N(R, M_fin k)`; `EL_N(k[z,z^-1])` survives | nontrivial MF quotient (un-calibration F4) | kill `M_fin(k)` |
| integral Jacobson `Z<s,t : ts=1>` | `M_fin(Z)` | kill finitary `SL` over `Z` (§3) | all-or-nothing, undecided (`integral-jacobson-mf-radical-is-all-or-nothing`) | kill `M_fin(Z)` |
| `F_q[Γ]` | zero iff directly finite (Kaplansky, known for sofic Γ) | §3 applies iff a defect exists | — | only if LEF (un-calibration) |

The Jacobson row separates the levels: finite and linear targets provably kill the finitary part with no (T),
while at the MF level the same statement is undecided. The (T) upgrade is genuinely needed only for MF.

## 5. What is not claimed

- No converse: vanishing defects do not produce models (un-calibration F3).
- At the MF level Lemma C gives only the Hilbert–Schmidt statement; the exact kill needs the normal-Kazhdan theorem.
- Nothing is claimed for tracial targets.
