---
rg: 2
id: fpbs-backward-locally-finite-ray-codes-die-proof
kind: route
title: Proof that joint returns of a boundary pair freeze onto one backward endpoint whenever the code relation is backward locally finite, so backward-locally-finite forward-null quasi-geodesic ray codes carry only totally dissipative diagonals, with the spelling-choice lattice code and the zero-entropy dimension-zero proposition
target: fpbs-backward-locally-finite-ray-codes-die
requires:
  - fpbs-finite-to-one-quasigeodesic-ray-codes-die
  - fpbs-quasiconvex-null-lattice-odometer-class-dies
  - fpbs-dini-boundary-class-diagonal-dissipative
---

# Proof

Notation is as in the claim and in `fpbs-finite-to-one-quasigeodesic-ray-codes-die-proof` (cited as [FT]). `o = 1`,
`(a|b)_o` is the Gromov product, `|g| = d(o, g)`. Inputs (G1), (Morse), (GP), (UM), (Rec), (PDR) are those of [FT],
together with:

- **(Line)** There is `C_1 = C_1(delta)` such that for distinct `a, b ∈ dGamma` and any bi-infinite geodesic `(a, b)`,
  `|(a|b)_o - d(o, (a, b))| <= C_1` (Bridson--Haefliger III.H.3.17--3.18).
- **(Morse±)** A bi-infinite `(lambda, c)`-quasi-geodesic lies within Hausdorff distance `M` of any geodesic with the
  same endpoints, `M = M(delta, lambda, c)`.

**Check of [FT].** I re-derived Steps 0--3 of [FT]. The shift identity `P_{(T^#)^t p}(s) = P_p(t)^{-1} P_p(t+s)`,
the endpoint identity (0.1) and the key identity `b_n = w P_p(-t_n)` of Claim A are correct as written (with
`P_p(-t_n) = P_{(y_n,0)}(t_n)^{-1}` when `p = (T^#)^{t_n}(y_n, 0)`). Lemma 1.2 and Step 3 are correct. Nothing in
Steps 0--3 uses that the spelling depends only on the letter, so a Borel spelling `sigma_x` is allowed throughout.
Corollary 3 of [FT] is not used here.

## Step 1. The code relation

**1.1 (analytic, invariant).** `R` is the union over `g ∈ Gamma` of the images of the Borel set `X^#` under the Borel
maps `p -> (g zeta^{-#}(p), g zeta^#(p))`. So `R` is analytic and `Gamma`-invariant. By (UQ) and [FT] Step 0.2,
`R` misses the diagonal. By (0.1) of [FT], `R = Gamma · {(zeta^-(x), zeta(x)) : x ∈ X_0}`: moving along a line
translates both endpoints by the same group element. In particular `R` depends only on the group path at letter
boundaries, not on the spellings.

**1.2 (lines through a ball).** Let `p ∈ X^#`, `w ∈ Gamma`, and put `(theta, eta) = (w zeta^{-#}(p), w zeta^#(p))`.
The line `w P_p` passes through `w`. By (Morse±) the geodesic `(theta, eta)` passes within `M` of `w`, so by (Line)
`(theta|eta)_o <= |w| + M + C_1`.

## Step 2. Freezing without finite fibres

**Proposition 2.1.** Assume (UQ). Let `eta ≠ eta'` be points at which (LF) holds, and let `H ⊂ Gamma` be finite.
Suppose infinitely many distinct `g` satisfy `g eta ∈ H zeta(X_0)` and `g eta' ∈ H zeta(X_0)`. Then one of the
following holds: `R^eta ∩ R^{eta'} ≠ ∅`; `eta ∈ R^{eta'}`; `eta' ∈ R^eta`.

*Proof.* Normalize exactly as in [FT], Proposition 2.1: after passing to a subsequence, fix `h, h' ∈ H` and
`y_n, y'_n` with `b_n zeta(y_n) = eta` and `b'_n zeta(y'_n) = eta'`, where `b_n = g_n^{-1} h`, `b'_n = b_n u`, `u`
fixed, and `b_n -> theta ∈ dGamma`, `b'_n -> theta`.

**Claim A (LF version).** If `theta ≠ eta`, then `theta ∈ R^eta`.

*Proof.* As in [FT] Claim A, (GP) and (Morse) give `R_0 < ∞` and times `t_n >= 0` with
`w_n = b_n P_{(y_n,0)}(t_n) ∈ Ball(o, R_0)`. Pass to a subsequence with `w_n = w`. Let
`p_n = (T^#)^{t_n}(y_n, 0)`. Then `w zeta^#(p_n) = eta` ([FT], Claim A) and `b_n = w P_{p_n}(-t_n)`. The positions
`p_n` may now be pairwise distinct. Put `theta_n = w zeta^{-#}(p_n)`. Then `(theta_n, eta) ∈ R`, i.e.
`theta_n ∈ R^eta`, and by 1.2 `(theta_n|eta)_o <= R_0 + M + C_1 =: r`. By (LF) at `eta`, only finitely many points of
`R^eta` satisfy this bound. Pass to a subsequence with `theta_n = theta*` for all `n`.

Now `b_n` is the point at parameter `-t_n` of the backward half of the `(lambda, c)`-quasi-geodesic line `w P_{p_n}`,
which starts at `w` and converges to `theta*`. The `b_n` are distinct, so `|b_n| -> ∞`, and since
`|b_n| <= |w| + lambda t_n`, `t_n -> ∞`. By (Morse), `b_n` lies within `M` of a geodesic ray `[w, theta*)` at distance
at least `t_n/lambda - c - M` from `w`. So `(b_n|theta*)_o -> ∞`, that is `b_n -> theta*`. Hence
`theta = theta* ∈ R^eta`. `□`

(What changed from [FT]: there the finite fibre froze the position `p_n`. Here only the backward endpoint `theta_n`
is frozen, by (LF). That is all the limit needs, because `b_n` converges to the backward endpoint of its own line
at a rate depending only on `t_n`, `lambda`, `c`, `delta`.)

*Conclusion.* Claim A' (`theta ≠ eta'` implies `theta ∈ R^{eta'}`) is the same. Since `eta ≠ eta'`, the three cases
of [FT] give `theta ∈ R^eta ∩ R^{eta'}`, or `eta ∈ R^{eta'}` (if `theta = eta`), or `eta' ∈ R^eta` (if
`theta = eta'`). `□`

## Step 3. The bad set is null

Let `N = {(eta, eta') : eta = eta', or R^eta ∩ R^{eta'} ≠ ∅, or eta ∈ R^{eta'}, or eta' ∈ R^eta}`. It is analytic
(as in [FT], Lemma 1.2, from the analytic `R` and the diagonal).

**Lemma 3.1.** Assume (NF), and let `lambda_1, lambda_2` be finite nonatomic measures with `lambda_2 << nu`, and
`lambda_1`-a.e. `eta` satisfying (LF). Then `(lambda_1 x lambda_2)(N) = 0`.

*Proof.* Fix `eta` satisfying (LF). Then `R^eta` is countable: each set `{theta : (theta|eta)_o <= r}` meets it in a
finite set, and these sets exhaust `dGamma \ {eta}`. The section `N_eta` is contained in
`{eta} ∪ ⋃_{theta ∈ R^eta} R_theta ∪ R_eta ∪ R^eta`:
- `R^eta ∩ R^{eta'} ∋ theta` means `eta' ∈ R_theta` with `theta ∈ R^eta`;
- `eta ∈ R^{eta'}` means `eta' ∈ R_eta`;
- `eta' ∈ R^eta` is the last set.
By (NF), each `R_theta` is `nu`-null, hence `lambda_2`-null. The union is countable. `R^eta` is countable and
`lambda_2` is nonatomic. So `lambda_2(N_eta) = 0` for `lambda_1`-a.e. `eta`, and Tonelli for the completed product
(UM) gives `(lambda_1 x lambda_2)(N) = 0`. `□`

## Step 4. Proof of Theorem 1

This is [FT] Step 3 with Proposition 2.1 and Lemma 3.1 in place of its Proposition 2.1 and Lemma 1.2.
- *Cover.* Make `xi` Borel off a null set. Choose finite-measure `E_n` increasing to `Z` and finite `H_n` increasing
  to `Gamma`. Since `xi_*(mu_Z|_{E_n}) << nu` is carried by `Gamma zeta(X_0)`, the measurable sets
  `E'_n = E_n ∩ xi^{-1}(H_n zeta(X_0))` increase to a conull set.
- *Pairs avoid `N`.* `lambda_n = xi_*(mu_Z|_{E'_n})` is finite, `<< nu`, hence nonatomic, and (LF) holds
  `lambda_n`-a.e. By Lemma 3.1, `(lambda_n x lambda_n)(N) = 0`, so a.e. `(z, z') ∈ E'_n x E'_n` has
  `(xi z, xi z') ∉ N`, and (LF) holds at `xi z` and `xi z'`.
- *Finite returns.* If `g(z, z') ∈ E'_n x E'_n`, then `g xi(z), g xi(z') ∈ H_n zeta(X_0)`. By Proposition 2.1 (whose
  conclusion is exactly membership in `N`), a.e. pair of `E'_n x E'_n` returns to it under finitely many `g`.
- *Dissipativity.* By (Rec), the conservative part meets each `E'_n x E'_n` in a null set, so it is null. No ergodic
  such `Z` is PDR by (PDR). Maharam extensions and all imp actions over `nu` satisfy `xi_*(mu_Z|_E) << nu`.
- *Restriction.* If the hypotheses hold for the code restricted to a `T`-invariant Borel set `X_1` carrying the code
  measure, run the argument with `X_1`; the relation only shrinks, and (LF), (NF) pass to subsets of `R`. `□`

No invariant measure on `X_0`, no entropy and no property of the spellings was used.

## Step 5. Proof of Proposition 2

*(FT) implies (LF) at every `eta`.* Let `theta ∈ R^eta` with `(theta|eta)_o <= r`. Write
`(theta, eta) = (g zeta^{-#}(p), g zeta^#(p))`. The line `g P_p` is within `M` of the geodesic `(theta, eta)`, which by
(Line) passes within `r + C_1` of `o`. So some vertex `w' = g P_p(t)` lies in `Ball(o, r + C_1 + M + 1)`. With
`p' = (T^#)^t p`, (0.1) gives `(theta, eta) = (w' zeta^{-#}(p'), w' zeta^#(p'))`, so `p' ∈ (zeta^#)^{-1}(w'^{-1} eta)`,
finite by (FT). Finitely many `w'` and finitely many `p'` give finitely many `theta`.

*(CT) implies (NF).* If `eta ∈ R_theta`, then `eta = g zeta^#(p)` with `zeta^{-#}(p) ∈ Gamma theta`, a countable set.
By (CT) countably many `p` qualify, and `g` ranges over the countable `Gamma`. So `R_theta` is countable, hence null
for every nonatomic `nu`. `□`

## Step 6. Proof of Theorem 3 (the spelling-choice lattice code)

*Base code.* By Selberg's lemma pick a torsion-free finite-index `Gamma_0 <= Gamma`. Let `(Omega, +1, G_0)` be the
symmetric lattice odometer code on `Gamma_0` of `fpbs-quasiconvex-null-lattice-odometer-class-dies`, with Haar measure
`m_Omega`, and with (UQ), (MR), (MR±) on a conull invariant `Omega_1` (that node and
`fpbs-transverse-skeleton-ray-codes-are-match-rigid`). By [FT] Corollary 2 (its Step 4), (FT) and (CT) hold on the
positions over a co-countable invariant `Omega_2 ⊂ Omega_1`. By Proposition 2 its code relation `R_0` satisfies (LF) at
every point and (NF) for every nonatomic measure. Let `nu_0` be its `Gamma_0`-class: ergodic, nonatomic and
quasiconvex-null (that node).

*Respelling.* Let `S_0` be the generating set used for `Gamma_0` and `S` a finite generating set of `Gamma` containing
`S_0`. For each `s ∈ S_0` choose `s' ∈ Gamma \ {1, s}` and put `s'' = s'^{-1} s ≠ 1`; enlarge `S` by all `s', s''`. For
`y ∈ Z_2` (2-adic integers) let `j(y) ∈ {0, 1}` be the parity of the 2-adic valuation `v_2(y)` (`j(0) = 0`). On
`X_0 = Omega_2 x Z_2` put `T(x, y) = (x + 1, y + 1)`, letters `G(x, y) = G_0(x)`, and spell the letter `G(x+1, y+1)`
by `sigma_0(G_0(x+1))` if `j(y+1) = 0`, and otherwise by the same word with its first letter `s` replaced by `s' s''`.
This is Borel, aperiodic and `T`-equivariant in the sense required. The measure `rho = m_Omega x m_2` is `T`-invariant;
`(Z_2, +1)` is an odometer and the base system of the lattice odometer code has zero entropy (it is an odometer
with discrete spectrum), so the product `(X_0, T, rho)` has zero entropy.

*Properties.*
1. **(UQ).** The refined path of a position is the old refined path with at most one extra vertex inserted per letter,
   each inserted vertex at `S`-distance `1` from an old vertex, and every letter has at least one old step. So time is
   distorted by a factor in `[1, 2]`, and `d_S <= d_{S_0} <= K d_S` on `Gamma_0`. Hence the new paths are uniformly
   `(lambda', c')`-quasi-geodesic for `S`, with constants depending only on `lambda, c, K`.
2. **Same relation, same class.** The group path at letter boundaries is `G_0(x+1) G_0(x+2) ...`, independent of `y`.
   By 1.1, the code relation of the new code, as a code on `Gamma`, is `R = Gamma · R_0 = ⋃_i k_i R_0` over coset
   representatives `k_1, ..., k_m` of `Gamma / Gamma_0`. Each `k_i` is a homeomorphism of `dGamma = dGamma_0`, so
   `R^eta = ⋃_i k_i R_0^{k_i^{-1} eta}` accumulates only at `eta`, and `R_theta = ⋃_i k_i (R_0)_{k_i^{-1} theta}` is
   countable. So (LF) holds everywhere and (NF) holds for every nonatomic class. The forward endpoint of `(x, y)` is
   `zeta_0(x)`, so the class is `nu = sum_i (k_i)_* nu_0`.
3. **The class passes the size-free filters it did before.** `nu` is nonatomic. It is `Gamma`-ergodic: a
   `Gamma`-invariant set is `Gamma_0`-invariant, so it is `nu_0`-null or conull, and then the same holds for each
   `(k_i)_* nu_0` because `k_i^{-1} A = A`. It is quasiconvex-null: for an infinite-index quasiconvex `L <= Gamma`,
   `L ∩ Gamma_0` is quasiconvex of infinite index in `Gamma_0` with the same limit set, and
   `(k_i)_* nu_0 (g Lambda_L) = nu_0(k_i^{-1} g Lambda_L) = 0` by the quasiconvex-nullity of `nu_0`.
4. **Continuum spelling multiplicity.** Fix `x ∈ Omega_2` and `y ≠ y'` in `Z_2`, and let `k = v_2(y' - y)`. Pick
   `t >= 1` with `y + t ≡ 2^{k+1} mod 2^{k+2}` (infinitely many `t` qualify). Then `v_2(y + t) = k + 1` and
   `v_2(y' + t) = v_2((y + t) + (y' - y)) = k`, so `j(y + t) ≠ j(y' + t)`. Take the least such `t`. The forward
   `S`-words at `((x, y), 0)` and `((x, y'), 0)` agree up to letter `t` and there one reads `s` where the other reads
   `s'`, with `s' ≠ s`. So the uncountably many `y ∈ Z_2` give pairwise distinct forward words, all with endpoint
   `zeta_0(x)`. By Fubini, for `rho`-a.e. `(x, y)` and any conull invariant `X'`, `m_2`-a.e. `y'` has `(x, y') ∈ X'`,
   so the fibres stay uncountable inside `X'`. (FT) fails on every conull invariant set.
5. **Death.** By 2, Theorem 1 applies. `□`

Corollary 3 of [FT] called such codes (zero entropy, infinite fibres) the only zero-entropy escape. Item 2 shows why
they do not escape: respelling moves positions inside fibres and never moves the code relation.

## Step 7. Proof of Proposition 4 (zero entropy gives local dimension zero)

Let `P_0` be the finite partition of `X^#` by the letter `s_1(p) = P_p(1) ∈ S`, and `C_n(p)` the atom of
`P_0 ∨ (T^#)^{-1} P_0 ∨ ... ∨ (T^#)^{-(n-1)} P_0` containing `p`: the positions whose forward words agree with that of
`p` for `n` letters.

*Cylinders map into balls.* If `p' ∈ C_n(p)`, the rays `P_p|_{[0,∞)}` and `P_{p'}|_{[0,∞)}` from `1` share their first
`n` steps, so both pass through `v = P_p(n)`, with `|v| >= n/lambda - c`. By (Morse) both lie within `M` of geodesic
rays from `o`, which then pass within `M + 1` of `v`. By thin triangles
`(zeta^#(p)|zeta^#(p'))_o >= |v| - 2M - C_2(delta)`. For the visual metric `d_eps`,
`d_eps(zeta^#(p), zeta^#(p')) <= C_3 e^{-eps n/lambda}`. So `zeta^#(C_n(p)) ⊂ B(zeta^#(p), C_3 e^{-eps n/lambda})`.

*Cylinders are large.* `h(T^#, P_0) <= h(T^#, rho^#) = 0`. By the Shannon--McMillan--Breiman theorem (non-ergodic
form: the limit is the entropy of the ergodic component, which is `0` a.e.), `(1/n) log rho^#(C_n(p)) -> 0` for
`rho^#`-a.e. `p`.

*Every measure in the class.* Let `nu' << nu = sum_g c_g g_* nu_0`, `nu_0 = zeta^#_* rho^#`, with density `f`. Then
`nu' = sum_g c_g g_*(f_g nu_0)` with `f_g = f ∘ g`. Fix `g` and put `rho' = (f_g ∘ zeta^#) rho^#`. The partitions
`C_n` increase and generate the sigma-algebra of the forward word, of which `zeta^#` is a measurable function. By the
martingale convergence theorem, `rho'(C_n(p)) / rho^#(C_n(p)) -> f_g(zeta^#(p))` for `rho^#`-a.e. `p`, and the limit
is positive `rho'`-a.e. Hence for `rho'`-a.e. `p`,

`(f_g nu_0)(B(zeta^#(p), C_3 e^{-eps n/lambda})) >= rho'(C_n(p)) = e^{-o(n)}`.

So `f_g nu_0` has upper local dimension `0` at a.e. point. The map `g` is `e^{eps|g|}`-Lipschitz for `d_eps` up to a
constant, so `g_*(f_g nu_0)(B(g zeta, r)) >= (f_g nu_0)(B(zeta, C_4^{-1} e^{-eps|g|} r))`, and `g_*(f_g nu_0)` also
has upper local dimension `0` a.e. Since `nu' >= c_g g_*(f_g nu_0)` for each `g` and `nu'` is carried by the union of
their carriers, `nu'` has upper (hence lower) local dimension `0` at `nu'`-a.e. point. `□`

So the criterion "positive lower local dimension on a positive set" of Theorem C of
`fpbs-dini-boundary-class-diagonal-dissipative` never fires on a zero-entropy code class. Such a class may still be
dominated by a Dini measure (dimension zero does not exclude that), but then it dies there; either way size is not
what kills the zero-entropy branch, and Theorem 1 is.

**Remark 7.1 (positive entropy).** Theorem 1 does not look at entropy. A positive-entropy code with lower local
dimension zero, which escapes Theorem C, still dies if (LF) and (NF) hold. For finite invariant `rho^#`, the entropy
bound of [FT] Corollary 3(1) forces infinite fibres of positions, not accumulation of `R^eta`. The Bowen--Series code
shows that positive entropy often does produce accumulation (every past is compatible), but that is a property of
`R`, and it is `R` that must be controlled.

**Remark 7.2 (the current; not used above).** If `rho^#` is a finite `T^#`-invariant measure, the skew product
`(p, g) -> (T^# p, g P_p(1))` on `X^# x Gamma` preserves `rho^# x count` and commutes with the left `Gamma`-action. By
(UQ) it is totally dissipative with fundamental domain `D = {(p, g) : g is the first vertex of the line g P_p nearest
to o}`. The map `(p, g) -> g (zeta^{-#}(p), zeta^#(p))` is invariant along the skew product (by (0.1)) and
`Gamma`-equivariant, so it pushes `(rho^# x count)|_D` to a `Gamma`-invariant measure `mu_R` on `dGamma^2`, carried by
`R`. It is Radon: pairs whose geodesic passes within `r` of `o` come from `g` in a ball of radius `r + M + C_1`, so
their mass is at most `|Ball(o, r + M + C_1)| rho^#(X^#)`. Its forward marginal is absolutely continuous with respect to `nu`. The open
statement asks whether `mu_R` can have conditional measures on backward sections `R^eta` that accumulate away from
`eta` for `nu`-positively many `eta`, compatibly with a conservative diagonal. A Borel--Cantelli count against the
local finiteness of `mu_R` is the first test.
