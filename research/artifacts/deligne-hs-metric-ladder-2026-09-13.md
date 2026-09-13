# The Deligne mark across metrics, and what the normalized case needs (lane ex-nh-deligne-hs, 2026-09-13)

Status: unreviewed commentary, except where a node is named as the source of a result.

Notation. `Gamma_g = Sp_(2g)(Z)`, `Gamma~_g` its preimage in the universal cover of `Sp_(2g)(R)`,
`z` the covering generator, `E_n^(g) = Gamma~_g/<z^n>`, `alpha_t = exp(2 pi i t b_g)` for an integral
covering cocycle `b_g`. The graph's witness is `E_3 = E_3^(2)`.

## 0. Summary

1. **Finite residual.** At every genus it is `<z^2>`
   (`deligne-covers-of-sp2g-z-have-finite-residual-2z`). So the triple cover hides its whole
   kernel from finite quotients.
2. **Frobenius collapse.** At `g >= 3`, every Schatten-p asymptotic homomorphism with `p <= 2` kills
   the mark, and every nontrivial sector has a dimension-free Frobenius gap
   (`deligne-symplectic-covers-are-not-schatten-approximated`). This is new for finite covers and odd
   orders.
3. **Genus monotonicity.** Every obstruction propagates upward in genus
   (`deligne-cover-hyperlinearity-is-monotone-in-genus`). The graph's genus-two witness is the
   strongest instance, and the weakest is `deligne-stable-triple-cover-is-not-hyperlinear`.
4. **The normalized problem.** It is exactly the gap between the established floor `delta d^(-1/2)`
   and a floor independent of `d`.
5. **Operator norm.** At `g >= 3`, BDL Conjecture 1.8 for `Gamma~_g` would make every `E_n^(g)`,
   `n >= 3`, not MF (Section 5). Nothing comparable is available for normalized HS.

## 1. The ladder of metrics for the triple cover

| model metric | status for `z` in `E_3^(g)` | source |
| --- | --- | --- |
| exact finite-dimensional | killed, every `g >= 2` | Deligne, via Malcev |
| unnormalized Schatten `p <= 2` | killed, `g >= 3`; open at `g = 2` | BLSW descent plus order-3 rounding |
| unnormalized Schatten `p > 2` | not covered by the sources read | Lubotzky--Oppenheim treat l-adic groups |
| operator norm (MF) | open; conditional at `g >= 3` (Section 5) | BDL Proposition 1.5, Conjecture 1.8 |
| normalized HS (hyperlinear) | open | Dogon; the sector equivalences of the graph |
| Hamming (sofic) | open | Gohla--Thom need a cosystolic inequality, known only p-adically |
| rank over a field | open; scalar data rigid | `deligne-rank-*` nodes |

Genus two sits below every established collapse except the exact one. Frobenius stability fails
for it at the level of method only: `Sp_4(R)` has rank 2, and Bader--Sauer give `(T_1)` there.

## 2. Why the Frobenius proof stops at the normalized norm

**The mechanism.** De Chiffre--Glebsky--Lubotzky--Thom correct an almost representation `phi` by
`phi e^(ib)`, where `b` solves the linearized cocycle equation with `||b|| <= K ||defect||`. `[T_2]`
supplies `b` in *any* unitary representation, including the adjoint action on `M_d` with the
normalized trace inner product. The new defect is bounded by a quadratic term:
- in Frobenius norm, `||b||_2^2 + ||b||_2 ||defect||_2`, using `||XY||_2 <= ||X||_2 ||Y||_2`;
- in normalized HS, only `||b||_op ||b||_HS`, because `||XY||_HS <= ||X||_op ||Y||_HS`.

`b` has no operator-norm bound. A few eigenvalues of size `O(1)` cost almost nothing in `||.||_HS`,
yet they spoil the quadratic step. This is the whole difference.

**Exponent form.** Let `sigma_t(d)` be the least maximal normalized relator defect of an
`alpha_t`-projective tuple in `U(d)` on a fixed finite window.
- **Upper bound.** The one-dimensional gauge models give `sigma_t(d) <= C |t|`.
- **Lower bound at `g >= 3`, for every `t` not in `(1/2)Z`.** There is `delta_t > 0` with
  `sigma_t(d) >= delta_t d^(-1/2)` for all `d`.
  - Frobenius stability of `Gamma~_g` puts a genuine `rho~` Frobenius-close to the tuple, with
    `rho~(z)` close to `e^(2 pi i t)`.
  - Malcev gives `rho~(z^2) = 1`.
  - Hence `d^(1/2) |1 - e^(4 pi i t)| <= 2 epsilon`. Choosing `epsilon = |1 - e^(4 pi i t)|/3`
    gives the uniform gap.
- **Frobenius parameter set.** So at `g >= 3` the set of Frobenius-realizable parameters is exactly
  `(1/2)Z/Z`. The HS parameter set `E_CE^(g)` is some closed subgroup containing it.
- **What hyperlinearity needs.** Hyperlinearity of `E_3^(g)` is `liminf_d sigma_(1/3)(d) = 0`. A
  hyperlinear microstate family needs `d >= (delta/eta)^2` at defect `eta`, with defects spread
  over asymptotically full rank.
- **What would be new.** A floor `c d^(-b)` with `b < 1/2` for all tuples would be new and weaker
  than the goal.

**Small twists (linear response).**
- **Near genuine representations.** Let a model be within normalized-HS distance `eta` of a genuine
  representation `rho`, with `U = rho e^(iA)`.
  - The traces of the relators give `|(delta a)(r) - 2 pi t b(r)| <= defect + O(eta^2 + t^2)` for
    `a = tr A`, when `A` is operator-small.
  - Since `[b_g]` is nonzero in `H^2(Gamma_g; R)`, the defect is at least `c|t|`.
- **Operator-norm smallness is essential.** With only HS-smallness, a fraction `~|t|` of eigenvalues
  can wind once around the circle along relator loops. That costs HS distance `~|t|^(1/2)`. So a
  model with defect `o(|t|)` must stay `|t|^(1/2)`-far from genuine representations.
- **Combined with Section 2 at `g >= 3`.** Assume Frobenius stability with a *linear* estimate:
  distance at most `K` times the Frobenius defect below some `delta_0`. This is not verified here,
  since BLSW's descent may lose rates. Then every tuple with `d <= delta_0^2/eta^2` has
  `eta >= |1 - e^(4 pi i t)|/(2K)`. So models with defect `o(|t|)` would need dimension `>> t^(-2)`.
- **Equivalence.** By the closed-subgroup theorem, `o(|t|)` models exist iff `Gamma~_g` is
  hyperlinear, iff every finite cover is.

## 3. What input the normalized case needs (answer to the brief)

The one-theorem-across-metrics framework (`kazhdan-commutant-compression-stability-is-finitary`)
spends property (T) as rounding (R), localization (L) and lift (K). Its marks are *compression*
defects of infranormal Kazhdan pairs.
- **No compressors here.** For a lattice `Gamma_g` and `t` in `Sp_(2g)(Q)`,
  `t Gamma_g t^(-1) <= Gamma_g` forces equality by covolume. So the Deligne witness carries no strict
  compressor, and `UCS` is not the right frame. Hecke pairs belong to family D.
- **The Deligne mark is a finite-residual mark.** Malcev kills it in genuine representations. So
  (L) is replaced by Malcev, and (K) is not needed in any tracial row.
- **The single input is sector rounding (R).** Almost representations in the nontrivial sector must
  be close, in the model metric, to genuine representations. The rows:
  - *Exact:* free.
  - *Frobenius, `g >= 3`:* holds (BLSW), which is why the unnormalized collapse is now established.
  - *Operator norm to HS:* BDL's condition (∗). `[T_2]` of `Gamma~_g` makes it an instance of BDL
    Conjecture 1.8.
  - *Normalized HS:* flexible HS stability of the base, restricted to the sector (Dogon).
- **The peer theorem.** `rf-kazhdan-group-not-flexibly-hs-stable` shows that (T) and residual
  finiteness alone do not give HS rounding. Its engine needs exact projective twists tending to `1`.
  `Gamma_g` has none, since the realizable parameters are `(1/2)Z/Z`. So the base can only fail
  rounding through approximate twists, which is hyperlinearity of `Gamma~_g`.
- **Consequence.** In the HS row, rounding restricted to the nontrivial sector is equivalent to the
  goal. No weaker HS input is known.

## 4. Genus monotonicity and the stable witness

The block embedding induces `U(g) -> U(g+1)`, `u -> diag(u, 1)`, an isomorphism on `pi_1`. It lifts
to injections `E_n^(g) -> E_n^(g+1)` preserving the covering generator. Consequences:
- **Direction of transfer.** Non-hyperlinearity and every collapse statement propagate *upward* in
  genus, and approximation properties propagate downward.
- **The stable order.** `E_CE^(g)` decreases in `g`. A decreasing chain of closed subgroups of `R/Z`
  containing `1/2` stabilizes at `(1/M_infinity)Z/Z` or `R/Z`. The triple-cover goal in its weakest
  form is that `3` does not divide `M_infinity` and the chain is not `R/Z`.
- **Where to work.** The better setting has large genus:
  - `[T_2]` for `Gamma~_g`, and Bader--Sauer `(T_(g-1))` for `Gamma_g`;
  - Frobenius stability;
  - character rigidity, as at genus two.

## 5. Conditional operator-norm collapse at g >= 3 (sketch, unreviewed)

Assume BDL Conjecture 1.8 for `Gamma~_g`. Every operator-norm asymptotic homomorphism `phi_k` then
has genuine `psi_k` in the same dimension with `||phi_k(x) - psi_k(x)||_HS -> 0`.

- **A. Pass to `E_6^(g)`.** `<z^6> <= <z^2> = PR(Gamma~_g)`.
  - Compose an asymptotic homomorphism of `E_6^(g)` with the quotient map and round in `Gamma~_g`.
  - Genuine representations have residually finite image, so they kill `PR`, hence factor through
    `E_6^(g)`.
- **B. Pass to `E_3^(g)` through the central `N = <z^3>/<z^6>` of order 2.**
  - Lift an asymptotic homomorphism `phi` of `E_3^(g)` to `E_6^(g)` and round it to `psi`.
  - `phi(z^3) = phi(1) -> I`, so `||psi(z^3) - I||_HS^2 = 4 tr(P) -> 0`, where `P` is the
    `(-1)`-eigenprojection. `P` commutes with `psi`.
  - `psi' = psi(1-P) + P` is a genuine representation killing `z^3`, and
    `||psi' - psi||_HS <= 2 tr(P)^(1/2) -> 0`.
- **C. Order-three Proposition 1.5.**
  - If `||phi_k(z) - 1||_op >= c`, round `phi_k(z)` to an exact order-three `U_k`, as in `(R1)` of
    the Schatten proof.
  - A nontrivial eigenprojection `P_k` of `U_k` asymptotically commutes in operator norm, since the
    spectrum is separated.
  - Compress to `Im P_k` (BDL Proposition 2.4) and round in HS by B. The resulting genuine
    representation has `rho(z)` HS-close to `omega^j I != I`.
  - Malcev contradicts this.

So `Rad_MF(E_3^(g)) = C_3` for `g >= 3`, conditionally on Conjecture 1.8 for `Gamma~_g`. At genus two
`[T_2]` is not available, so the conjecture as stated does not apply.

## 6. Sources read for this note

- **Bader--Lubotzky--Sauer--Weinberger,** arXiv:2303.08943v2, pp. 1--16.
- **Bachner--Dogon--Lubotzky,** arXiv:2508.17392v3, pp. 1--7.
- **Stover,** arXiv:2407.07680v2, pp. 1--4.
- **Graph nodes:**
  - `rf-kazhdan-group-not-flexibly-hs-stable`, `sp4-fd-projective-multiplier-is-finite`;
  - `maslov-ce-parameter-set-is-a-closed-subgroup`, `deligne-sector-gap-is-exactly-nonhyperlinearity`;
  - `dogon-sp2g-weak-ucp-nonhyperlinear`, `kazhdan-commutant-compression-stability-is-finitary`.
