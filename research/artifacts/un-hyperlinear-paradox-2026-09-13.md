# Soficity and hyperlinearity on the paradox side of the UN program

Lane `un-hyperlinear-paradox`, 2026-09-13. Written proofs, unreviewed. Credits: the nonsoficity input is the
established Lean theorem `GroupApproximation.CompleteMatrixFamily.elementary_not_isSofic` (`GroupApproximation/Leavitt/AryEndpoints.lean`,
node `d-ary-leavitt-groups-nonsofic-over-finite-fields`); the corner trick is the one in
`projective-leavitt-units-nonsofic-by-corner-embedding` and `halvable-corner-makes-elementary-groups-nonsofic`.

## 0. Summary

- (S1) For every field `k` and `d >= 2`, `R_∂ = LC(∂F_d, k) ⋊ F_d` contains an explicit unital `d`-ary Leavitt
  family: `t_i s_j = delta_ij`, `sum_i s_i t_i = 1`. No pure infiniteness theory and no `K_0` computation is used.
- (S2) Over a finite field, every `EL_N(R_∂)/C` (`N >= 2`, `C` central scalars) is nonsofic. In particular the
  boundary mirror of the Pestov group, `S_∂ = EL_N(R_∂)/Z` (`boundary-action-elementary-simple-kazhdan-not-mf`), is
  nonsofic, not only non-MF.
- (S3) Where one-sided Kazhdan transport fails in Hilbert–Schmidt norm, exactly (§3). The HS analogue of the
  compression criterion is the open win-win `hyperlinear-groups-kill-rigid-compression-defects`; nothing in the
  paradox-side construction goes beyond it.
- Status of hyperlinearity: OPEN, and at least as hard as hyperlinearity of Leavitt elementary groups (§4).

## 1. The Leavitt family in the boundary crossed product (S1)

**Setup.** `F_d = <c_1, ..., c_d>` acts on `∂F_d` (infinite reduced words) by left multiplication and reduction.
For a reduced word `w`, `C(w)` is the clopen cylinder of words beginning with `w`; `P_U` is the indicator of a
clopen `U`. The algebraic crossed product has `u_g P_U u_g^(-1) = P_(gU)`, equivalently `P_U u_g = u_g P_(g^(-1)U)`.

**Three set identities.** For letters `c, c'` in `{c_i^(±1)}`:
- (I1) `c · C(c^(-1)) = ∂F_d \ C(c)`;
- (I2) if `c' != c^(-1)`, then `c · C(c') = C(cc') ⊆ C(c)`;
- (I3) `∂F_d` is the disjoint union of the `2d` cylinders `C(c)`.

**The family.** For `i = 1..d` put `c = c_i`, `P^+ = P_(C(c))`, `P^- = P_(C(c^(-1)))` and

```text
s_i = P^+ + u_(c^(-1)) (1 - P^+),        t_i = P^+ + u_c P^- .
```

On points: `s_i` fixes `C(c)` and sends `x ∉ C(c)` to `c^(-1)x ∈ C(c^(-1))`, a bijection
`∂F_d -> C(c) ⊔ C(c^(-1))`; `t_i` is its inverse on that range and kills the rest. The algebraic checks are below.

**`t_i s_i = 1`.** The four products are:
- `P^+ P^+ = P^+`;
- `P^+ u_(c^(-1)) (1-P^+) = u_(c^(-1)) P_(C(cc)) (1-P^+) = 0`, by (I2) with `c' = c`;
- `u_c P^- P^+ = 0`;
- `u_c P^- u_(c^(-1)) (1-P^+) = u_c u_(c^(-1)) P_(c·C(c^(-1))) (1-P^+) = P_(∂ \ C(c)) (1-P^+) = 1 - P^+`, by (I1).

The sum is `1`.

**`s_i t_i = P^+ + P^-`.** The four products are:
- `P^+ P^+ = P^+`;
- `P^+ u_c P^- = u_c P_(c^(-1)·C(c)) P^- = u_c P_(∂ \ C(c^(-1))) P^- = 0`, by (I1) for `c^(-1)`;
- `u_(c^(-1)) (1-P^+) P^+ = 0`;
- `u_(c^(-1)) (1-P^+) u_c P^- = u_(c^(-1)) u_c P_(c^(-1)·(∂\C(c))) P^- = P^- P^- = P^-`, by (I1).

**`t_i s_j = 0` for `i != j`.** Put `c = c_i`, `e = c_j`, so `c != e^(±1)`. The four products are:
- `P_(C(c)) P_(C(e)) = 0`;
- `P_(C(c)) u_(e^(-1)) (1-P_(C(e))) = u_(e^(-1)) P_(C(ec)) (1-P_(C(e))) = 0`, since `C(ec) ⊆ C(e)` by (I2);
- `u_c P_(C(c^(-1))) P_(C(e)) = 0`;
- `u_c P_(C(c^(-1))) u_(e^(-1)) (1-P_(C(e))) = u_c u_(e^(-1)) P_(C(ec^(-1))) (1-P_(C(e))) = 0`, again by (I2).

**`sum_i s_i t_i = sum_i (P_(C(c_i)) + P_(C(c_i^(-1)))) = 1`**, by (I3).

Nothing here uses the coefficient field, so (S1) holds over any unital coefficient ring. By
`leavitt-algebras-l-k-1-n-are-simple`, the induced unital map `L_k(1,d) -> R_∂` is injective.

**Model tests.**
- `d = 1` (`Z` on its two ends): the same formulas give `t s = s t = 1`, a unit and no paradox. That is correct,
  since the boundary of `Z` carries invariant measures.
- The Pestov ring `LC(X, F_q) ⋊ Z` carries no `d`-ary family with `d >= 2`: its rank function from the invariant
  measure would give `rk(1) = d · rk(1)`, so `rk(1) = 0`. That is consistent with its LEF group.
- The Cuntz groupoid (`L_k(1,2)` itself) carries the tautological binary family.

## 2. Nonsoficity of the boundary groups (S2)

**Input.** `d-ary-leavitt-groups-nonsofic-over-finite-fields` (ESTABLISHED, Lean): for a finite field `k` and a
nontrivial countable `k`-algebra `A` carrying a `d`-ary Leavitt family, `d >= 2`, every `EL_(m+1)(A)` with
`m >= 1` is nonsofic. `R_∂` is countable (finite `k`, countable `F_d`, countably many clopens) and nontrivial, so
`EL_N(R_∂)` is nonsofic for `N >= 2`.

**Corner lemma.** Let `R` carry a unital Leavitt family with `d >= 2`, put `e = s_1 t_1` (so `1 - e != 0`), and let
`k^x I_N` denote the central scalar matrices.
1. `theta : R -> eRe`, `x ↦ s_1 x t_1`, is a unital ring isomorphism with inverse `y ↦ t_1 y s_1`.
   - `theta(x) theta(y) = s_1 x (t_1 s_1) y t_1 = theta(xy)`;
   - `t_1 (s_1 x t_1) s_1 = x`;
   - `s_1 (t_1 y s_1) t_1 = e y e = y` for `y ∈ eRe`.
2. `Phi : EL_N(eRe) -> EL_N(R)`, `X ↦ X + (1-e) I_N`, is an injective homomorphism. Entries of `X` lie in `eRe`, so
   `X (1-e)I_N = 0`, and `Phi(e_ij(r)) = e_ij(r)`.
3. `Phi(EL_N(eRe)) ∩ k^x I_N = {I_N}`. If `X + (1-e)I_N = λ I_N`, compressing by `1 - e` gives
   `(λ - 1)(1 - e) = 0`, so `λ = 1`.
4. `psi = Phi ∘ EL_N(theta) : EL_N(R) -> EL_N(R)` is injective and meets the central scalars trivially. So for
   every subgroup `C ≤ EL_N(R) ∩ k^x I_N`, `psi(EL_N(R))` maps injectively into `EL_N(R)/C`.

**Theorem (S2).** Let `k` be finite, `d >= 2`, `N >= 2` and `C ≤ EL_N(R_∂) ∩ k^x I_N`. Then `EL_N(R_∂)/C` contains
an isomorphic copy of `EL_N(R_∂)`, so it is nonsofic, because subgroups of sofic groups are sofic.
- By `steinberg-elementary-groups-are-simple-mod-centre` (reviewed PASS), the boundary groupoid is minimal and
  effective, and `Z(EL_N(R_∂)) ⊆ k^x I_N` for `N >= 3`. So `S_∂ = EL_N(R_∂)/Z` is nonsofic.
- With `boundary-action-elementary-simple-kazhdan-not-mf` (unreviewed), `S_∂` is an infinite, finitely generated,
  simple Kazhdan group that is nonsofic and has no nontrivial MF quotient.

**The mirror, sharpened.** `S = EL_3(LC(X,F_q)⋊Z)/Z` is LEF, hence sofic. `S_∂` differs only in the dynamics
(measure versus paradox), and it lands on the opposite side of BOTH the MF and the sofic dividing lines. Both
failures come from one ring fact, the unital Leavitt family.

**Firewall for sofic-type constructions.** Over finite `k`, Păunescu-style partial-action models, permutation
models, random lifts and any other sofic approximation of `S_∂` or `EL_N(R_∂)` are impossible by (S2). Any
approximation of these groups must be non-permutational: HS unitary models, or linear models over infinite fields.

**Char 0 boundary.** The Lean theorem assumes a finite field. For `k = Q`, soficity of `EL_N(LC(∂F_d,Q)⋊F_d)` is not
decided on main. Reduction mod `p` does not transfer it: `EL_N(L_Z(1,2)) -> EL_N(L_(F_p)(1,2))` is only a
quotient map, and soficity passes to subgroups, not to extensions of nonsofic quotients.

## 3. Where one-sided Kazhdan transport fails in Hilbert–Schmidt norm (S3)

The paper already records the failure. Quoted verbatim from `non_mf_groups_exist.tex`:
- footnote near l.204: "A Hilbert--Schmidt bound on the multiplicative defect does not give an operator norm bound
  on the conjugation maps, so this argument does not apply to sofic or hyperlinear approximations; the sofic group
  of Section~\ref{sec:amenable-nonqd} shows that its conclusion fails there."
- l.1844ff: "So the collapse of Corollary~\ref{cor:defect-hs} fails for asymptotic representations in normalized
  Hilbert--Schmidt norm, although $\varepsilon$ is a central involution of $W$ inside $\mathfrak D_W(\Gamma)$:
  Theorem~\ref{thm:transport} needs operator norm control of the conjugation maps, and no version of
  Theorem~\ref{thm:compression-criterion} for sofic or hyperlinear approximation follows from these hypotheses."

**The exact failing step** in the proof of Thm l.478 is the first one:
`||Ad(A) - Ad(B)|| <= 2 ||A - B||_op`, "so the maps `Ad(V_n(g))` are asymptotically multiplicative in operator norm
and `sigma~(g) = [Ad(V_n(g))]_n` is a homomorphism" into the norm corona of `B(M_(d_n), ||·||_2)`.
- For HS asymptotic representations, `||V_n(gh) - V_n(g)V_n(h)||_2 -> 0` gives no operator-norm control of
  `Ad(V_n(·))` on `(M_d, ||·||_2)`.
- Calibration: `D_d = diag(-1,1,...,1)` has `||D_d - 1||_2 -> 0`, while `Ad(D_d)` negates every matrix unit
  `E_1j` (`j != 1`), so `||Ad(D_d) - id|| = 2`.
- So `sigma~` does not exist, and neither does the Kazhdan projection image `P` on which the rest of the argument
  runs.

**The tracial substitute and where it stops.**
- A hyperlinear model gives a genuine homomorphism `sigma : G -> U(prod_U M_n)`. `Ad sigma` is a unitary
  representation on `L^2(prod_U M_n)`, so the Kazhdan projection `P` of `L` exists.
- For `uLu^(-1) <= L`, the order lemma gives `U^* P U <= P` with `U = Ad sigma(u)`.
- The equality step used stable finiteness of the norm corona. Its tracial analogue would need a finite algebra
  containing `P` and `U`, but `P, U` live in `B(L^2(M))` for a II_1 factor `M`, which is not finite. Equality can
  fail, and the sofic group `W` of l.1794 shows the conclusion does fail.
- The group-level statement that would replace it is the open `hyperlinear-groups-kill-rigid-compression-defects`,
  equivalent by `rigid-compression-defect-normalization-dichotomy` to normalization of relative commutants in
  `prod_U M_n`. Its Attempts already record the dimension-count obstruction (no faithful conjugation-invariant size
  on relative commutants of infinite index). This lane adds no new route there and claims none.

**Consequence.** The paper's mechanism obstructs operator-norm models. Its HS shadow is exactly that win-win claim,
and the paradox-side groups add configurations to it: `EL_4(R_∂)` has the compressor `u`, the centralizing `c` and
the defect `e_13(1 - s_1 t_1) != 1` of Thm l.918's proof. They add no new HS obstruction.

## 4. Hyperlinearity: open, and no easier than the Leavitt case

`L_k(1,2) ↪ R_∂` for `d = 2` (§1), and the corner lemma of §2 applies with `R_∂` replaced by any unital subring
carrying the family. So `EL_N(L_k(1,2))` embeds in `EL_N(R_∂)/C` for every `C ≤ k^x I_N`:
- `L_k(1,2) -> R_∂ -> e R_∂ e` via `theta`, then `Phi`;
- the image meets the scalars trivially.

A hyperlinear `S_∂` (`d = 2`) would make `EL_N(L_k(1,2))` hyperlinear. For `k = F_2` and suitable `N`, that is the
open `binary-leavitt-unit-group-hyperlinear`. Over finite `k` it would also be a hyperlinear nonsofic simple Kazhdan
group, answering Pestov Question 3.4 negatively (`hyperlinear-nonsofic-group`). Each direction is famous-level.

**Sharpest next target.** None on the paradox side beyond the existing win-win. The new information is that the UN
dichotomy is sharper than MF: over finite fields the paradox side is nonsofic, while the measure side (towers) is
LEF. The remaining UN question in this direction is the middle: stably finite simple rings with no exact towers
(the Labbé ring), where soficity of EL_N is undecided.
