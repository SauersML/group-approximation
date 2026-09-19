---
rg: 2
id: fpbs-finite-to-one-quasigeodesic-ray-codes-die-proof
kind: route
title: Proof that finite forward and countable backward endpoint fibres of a uniformly quasi-geodesic ray code freeze every infinite family of joint returns onto the backward half of one code line, so joint returns are finite off a relation with countable sections and every class on the rays has totally dissipative diagonal
target: fpbs-finite-to-one-quasigeodesic-ray-codes-die
requires:
  - fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups
  - fpbs-dini-boundary-class-diagonal-dissipative
---

# Proof

Notation is as in the claim. `o = 1` is the base point, `(a|b)_o` is the Gromov product, `|g| = d(o, g)`, and a
`(lambda, c)`-quasi-geodesic is a path `P : Z -> Gamma` with `|t - s|/lambda - c <= d(P(t), P(s)) <= lambda|t - s| + c`.
Refined paths move by one generator per unit of time, so the upper bound holds with `lambda >= 1`, `c = 0`.

## Imported inputs

- **(G1)** If `b_n -> theta ∈ dGamma` and `u ∈ Gamma` is fixed, then `b_n u -> theta` and `u b_n -> u theta`.
  (`d(b_n, b_n u) = |u|`; `Gamma` acts on `Gamma ∪ dGamma` by homeomorphisms.)
- **(Morse)** There is `M = M(delta, lambda, c)` such that a `(lambda, c)`-quasi-geodesic ray from `b` to `eta ∈ dGamma`
  lies within Hausdorff distance `M` of every geodesic ray `[b, eta)` (Bridson--Haefliger III.H.1.7 and III.H.3.3).
- **(GP)** There is `C = C(delta)` such that `d(o, [b, eta)) <= (b|eta)_o + C` for `b ∈ Gamma`, `eta ∈ dGamma`. If
  `b_n -> theta ∈ dGamma` and `theta != eta`, then `limsup_n (b_n|eta)_o <= (theta|eta)_o + 2 delta < ∞`
  (Bridson--Haefliger III.H.3.17; Ghys--de la Harpe, Ch. 7).
- **(UM), (Rec)** Universal measurability of analytic sets with Tonelli for completed products, and recurrence for
  nonsingular actions of countable groups, exactly as in `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups-proof`.
- **(PDR)** PDR needs a conservative piece of the diagonal (Theorem A of `fpbs-dini-boundary-class-diagonal-dissipative`).

## Step 0. Elementary facts about refined paths

**0.1 (shift).** `P_{T^# p}(s) = P_p(1)^{-1} P_p(1 + s)` for all `s ∈ Z`. By induction
`P_{(T^#)^t p}(s) = P_p(t)^{-1} P_p(t + s)`. This is the definition: moving one position forward re-bases the same
bi-infinite word.

**0.2 (endpoints).** By (UQ) and (Morse), `P_p(t)` converges to points `zeta^#(p) != zeta^{-#}(p)` of `dGamma` as
`t -> +∞` and `t -> -∞`. By 0.1,

`zeta^#((T^#)^t p) = P_p(t)^{-1} zeta^#(p)` and `zeta^{-#}((T^#)^t p) = P_p(t)^{-1} zeta^{-#}(p)`. (0.1)

`zeta^#` and `zeta^{-#}` are Borel, as pointwise limits of Borel maps into the compact metrizable `Gamma ∪ dGamma`.
`X^#` is a Borel subset of `X_0 x N`. At `p = (x, 0)`, `P_p(t)` for `t >= 0` runs through the spellings of
`G(x+1), G(x+2), ...`, so `zeta^#(x, 0) = zeta(x)`. Also `zeta^#(x, i) = u^{-1} zeta(x)`, where `u` is the prefix of
length `i` of `sigma(G(x+1))`.

## Step 1. The bad relation

For `omega ∈ dGamma` define the **backward set**

`B(omega) = {g zeta^{-#}(p) : p ∈ X^#, g ∈ Gamma, g zeta^#(p) = omega}`.

Geometrically, `B(omega)` is the set of backward endpoints of translated code lines whose forward endpoint is `omega`.

**Lemma 1.1.** Under (FT), `B(omega)` is countable for every `omega`.

*Proof.* If `g zeta^#(p) = omega`, then `zeta^#(p) ∈ Gamma omega`, a countable set. By (FT) (countable-to-one is
enough here), only countably many `p` qualify. For each `p` only countably many `g` exist, since `Gamma` is countable.
`□`

Define `N ⊂ dGamma x dGamma` as the set of pairs `(eta, eta')` with at least one of:
- `eta = eta'`;
- `B(eta) ∩ B(eta') != ∅`;
- `eta ∈ B(eta')`;
- `eta' ∈ B(eta)`.

**Lemma 1.2.** Under (FT) and (CT), `N` is analytic and every section `N_eta = {eta' : (eta, eta') ∈ N}` is countable.
Hence `(lambda_1 x lambda_2)(N) = 0` for all finite nonatomic Borel measures `lambda_1, lambda_2` on `dGamma`.

*Proof.* *Analytic.* The relation `B = {(omega, theta) : theta ∈ B(omega)}` is the countable union over `g` of the
images of the Borel set `X^#` under the Borel maps `p -> (g zeta^#(p), g zeta^{-#}(p))`, so it is analytic. Each of
the four conditions defining `N` is a projection of a finite intersection of analytic sets built from `B` and the
diagonal, so `N` is analytic, and (UM) applies.

*Countable sections.* Fix `eta`.
- If `theta ∈ B(eta')`, then `theta = g zeta^{-#}(p')` and `eta' = g zeta^#(p')` for some `g, p'`. So
  `zeta^{-#}(p') ∈ Gamma theta`. By (CT), only countably many `p'` qualify, and so `eta' ∈ Gamma zeta^#(p')` ranges
  over a countable set. Call it `K(theta)`.
- The second condition gives `eta' ∈ ⋃_{theta ∈ B(eta)} K(theta)`. This is countable by Lemma 1.1.
- The third condition gives `eta' ∈ K(eta)`, which is countable.
- The fourth gives `eta' ∈ B(eta)`, countable by Lemma 1.1. The first gives `eta' = eta`.

*Null.* By Tonelli for the completed product, `(lambda_1 x lambda_2)(N) = ∫ lambda_2(N_eta) d lambda_1(eta) = 0`,
since `lambda_2` is nonatomic and `N_eta` is countable. `□`

## Step 2. Freezing joint returns (the core)

**Proposition 2.1.** Assume (UQ) and (FT). Let `(eta, eta') ∈ dGamma^2 \ N`, and let `H ⊂ Gamma` be finite. Then only
finitely many `g ∈ Gamma` satisfy both `g eta ∈ H zeta(X_0)` and `g eta' ∈ H zeta(X_0)`.

(Only (FT) is used here; (CT) enters through Lemma 1.2 only.)

*Proof.* Suppose there are infinitely many distinct such `g`, say `g_1, g_2, ...`.

*Normalize.* Passing to a subsequence, fix `h, h' ∈ H` and points `y_n, y'_n ∈ X_0` with `g_n eta = h zeta(y_n)` and
`g_n eta' = h' zeta(y'_n)`. Put `b_n = g_n^{-1} h` and `b'_n = g_n^{-1} h'`. Then

`b_n zeta(y_n) = eta`, `b'_n zeta(y'_n) = eta'`, `b'_n = b_n u` with `u = h^{-1} h'` fixed.

The `b_n` are distinct, so they leave every finite set. By compactness of `Gamma ∪ dGamma`, pass to a subsequence with
`b_n -> theta ∈ dGamma`. By (G1), also `b'_n -> theta`.

*The code rays.* `Q_n(t) = b_n P_{(y_n, 0)}(t)`, for integers `t >= 0`, is a `(lambda, c)`-quasi-geodesic ray from `b_n`
to `b_n zeta(y_n) = eta`, by (UQ) and Step 0.2. Likewise `Q'_n(t) = b'_n P_{(y'_n, 0)}(t)` runs from `b'_n` to `eta'`.

**Claim A (one side freezes).** Suppose `theta != eta`. Then `theta ∈ B(eta)`.

*Proof of Claim A.* By (GP), `(b_n|eta)_o <= A` for all large `n`, where `A = (theta|eta)_o + 2 delta + 1`. So
`d(o, [b_n, eta)) <= A + C`. By (Morse), `Q_n` passes within `A + C + M` of `o`. Its vertices are at unit spacing, so
there is an integer `t_n >= 0` with

`w_n := Q_n(t_n) ∈ Ball(o, R)`, `R = A + C + M + 1`.

The ball is finite, so after passing to a subsequence `w_n = w` for all `n`. Let `p_n = (T^#)^{t_n}(y_n, 0)` be the
position of `Q_n` at time `t_n`. By (0.1),

`w zeta^#(p_n) = b_n P_{(y_n,0)}(t_n) zeta^#(p_n) = b_n zeta^#(y_n, 0) = eta`.

So `p_n ∈ (zeta^#)^{-1}(w^{-1} eta)`, a finite set by (FT). After passing to a subsequence, `p_n = p` for all `n`. By
Step 0.1 applied at time `t_n`,

`b_n = Q_n(0) = b_n P_{(y_n,0)}(t_n) · P_{p}(-t_n) = w P_p(-t_n)`.

The `b_n` are distinct, so the `t_n` are distinct. Since `t_n >= 0`, `t_n -> +∞`. By Step 0.2 and (G1),
`b_n = w P_p(-t_n) -> w zeta^{-#}(p)`. Hence `theta = w zeta^{-#}(p)`, with `w zeta^#(p) = eta`, which says
`theta ∈ B(eta)`. `□`

(In words: the base points `b_n` all run down the backward half of the single code line `w P_p`.)

**Claim A'.** If `theta != eta'`, then `theta ∈ B(eta')`. The proof is Claim A for `Q'_n`, `b'_n` and `y'_n`.

*Conclusion.* Since `eta != eta'`, at least one of the claims applies.
- If `theta ∉ {eta, eta'}`, both apply, and `theta ∈ B(eta) ∩ B(eta')`.
- If `theta = eta`, Claim A' gives `eta ∈ B(eta')`.
- If `theta = eta'`, Claim A gives `eta' ∈ B(eta)`.

Each case puts `(eta, eta')` in `N`, a contradiction. `□`

**Remark 2.2 (where (MR) used to be).** In `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups-proof`, (MR) turned
each return into a vertex `c_k(x)` of the one line through `eta`, and a boundary limit then gave a reversed match. Here
the vertices `b_n` may lie on many different code lines ending at `eta`. The finite ball and the finite fibre select a
single line, and the rest of the argument goes through as before. This is exactly the step that needs (FT). If the
fibre `(zeta^#)^{-1}(w^{-1} eta)` is infinite, the `b_n` can run along infinitely many distinct lines through `w`, and
their limit `theta` need only be an accumulation point of backward endpoints. That set is not countable in general.

## Step 3. Proof of Theorem 1

This is Step 5 of `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups-proof`, with Proposition 2.1 and Lemma 1.2 in
place of its Proposition 4.1 and Lemma 3.1. Modify `xi` on a null set to make it Borel.
- **A cover.** Choose finite-measure sets `E_n` increasing to `Z`, and finite sets `H_n` increasing to `Gamma`. The set
  `H_n zeta(X_0)` is analytic, hence universally measurable (UM). Since `xi_*(mu_Z|_{E_n})` is carried by
  `Gamma zeta(X_0) = ⋃_m H_m zeta(X_0)`, the sets `E'_n = E_n ∩ xi^{-1}(H_n zeta(X_0))` are measurable and increase to
  a conull set.
- **Pairs avoid `N`.** Put `lambda_n = xi_*(mu_Z|_{E'_n})`, finite and nonatomic. Then
  `(xi x xi)_*(mu_Z|_{E'_n} x mu_Z|_{E'_n}) = lambda_n x lambda_n`, which gives `N` measure zero by Lemma 1.2. So a.e.
  `(z, z') ∈ E'_n x E'_n` has `(xi z, xi z') ∉ N`.
- **Finite returns.** If `g(z, z') ∈ E'_n x E'_n`, then `g xi(z)` and `g xi(z')` lie in `H_n zeta(X_0)`. By
  Proposition 2.1, a.e. pair in `E'_n x E'_n` returns to `E'_n x E'_n` under only finitely many `g`.
- **Dissipativity.** Let `C` be the conservative part of `Z x Z`. By (Rec), a.e. point of `C ∩ (E'_n x E'_n)` returns
  to that set infinitely often. So `C ∩ (E'_n x E'_n)` is null for every `n`, and `C` is null.
- **Consequences.**
  - No ergodic such `Z` is PDR, by (PDR).
  - For `nu_rho`: it is carried by `Gamma zeta(X_0)` and is nonatomic when `zeta_* rho` is. Every imp action over
    `[nu_rho]` has `xi_*(mu_Z|_E) << nu_rho`, and the Maharam extension is one of them. So the hypotheses hold.
  - No hypothesis on dimension, Krieger type or the shadow sum of `nu_rho` was used.
- **Restriction.** If (UQ), (FT) and (CT) hold on a `T`-invariant Borel set `X_1` carrying `rho`, run the argument with
  `X_1` in place of `X_0`. The class `nu_rho` is carried by `Gamma zeta(X_1)`, and positions over `X_1` form a
  `T^#`-invariant set. `□`

## Step 4. Proof of Corollary 2 (match rigidity gives bounded fibres)

Let `Gamma` be torsion-free, so the set `Q` of boundary points with nontrivial stabilizer is countable
((G2) of the imported proof). Assume (UQ), (MR) and (MR±), with the bad relation `Rel` of (MR±) having countable
sections.

*Exceptional set.* By (MR), `zeta^{-1}(Gamma omega)` lies in one `T`-orbit for each `omega`. So the set of `x` with
`zeta(x) ∈ Q` is countable. It is `T`-invariant by (0.1), since `Q` is `Gamma`-invariant. Remove it, and remove also
the countable set of `x` with `zeta^-(x) ∈ Q` (countable by (MR±)). The rest, `X_1`, is `T`-invariant and co-countable.

*Forward fibres.* Let `p = (x, i)` and `p' = (x', j)` be positions over `X_1` with `zeta^#(p) = zeta^#(p')`. By Step
0.2, `zeta^#(p) ∈ Gamma zeta(x)` and `zeta^#(p') ∈ Gamma zeta(x')`, so (MR) gives `x' ∈ x + Z`. Hence `p'` lies on the
line of `p`: `p' = (T^#)^t p` for some `t ∈ Z`. By (0.1), `P_p(t)^{-1} zeta^#(p) = zeta^#(p)`. The stabilizer of
`zeta^#(p) ∉ Q` is trivial, so `P_p(t) = 1 = P_p(0)`. By (UQ), `|t|/lambda - c <= 0`, so `|t| <= lambda c`. The fibre
has at most `2 lambda c + 1` points.

*Backward fibres.* If `zeta^{-#}(p) = zeta^{-#}(p')`, then `zeta^-(x) ∈ Gamma zeta^-(x')` by Step 0.2, so
`(x, x') ∈ Rel`. For fixed `p`, only countably many `x'` and so countably many `p'` occur.

Thus (FT) and (CT) hold on the positions over `X_1`. `□`

For the transverse skeleton codes of `fpbs-transverse-skeleton-ray-codes-are-match-rigid`, (UQ) is its Theorem 2.1,
and (MR), (MR±) are its Theorem 2.3 for symmetric forward-injective codes. So Theorem 1 contains that conclusion.

## Step 5. Proof of Corollary 3 (entropy versus spelling multiplicity)

Let `rho^#` be finite, `T^#`-invariant and ergodic, and let the two-sided `S`-coding `p -> (s_k(p))_{k ∈ Z}` be
injective, where `s_k(p) = P_p(k-1)^{-1} P_p(k) ∈ S`. Write `P_k` for the partition by `s_k`, and
`pi^+(p) = (s_k(p))_{k >= 1}`, `pi^-(p) = (s_k(p))_{k <= 0}`. By Step 0.1, `s_k(T^# p) = s_{k+1}(p)`, and
`zeta^#(p)` is a function of `pi^+(p)` alone: it is the endpoint of the path from `1` spelled by `pi^+(p)`. Likewise
`zeta^{-#}(p)` is a function of `pi^-(p)`. Since the coding is injective and `S` is finite, `P_0` is a finite
generating partition. So `h := h(T^#, rho^#) = h(T^#, P_0) = H(P_0 | P_1 ∨ P_2 ∨ ...)` (Kolmogorov--Sinai and the
future formula for the entropy of an invertible map; Walters, *An introduction to ergodic theory*, Thm 4.14 and
§4.6), and `h <= log |S|`.

**(1) Positive entropy forces infinite fibres.** Let `F^+ = sigma(pi^+)` and disintegrate
`rho^# = ∫ rho_omega d nu(omega)` over `pi^+`, with `rho_omega` carried by the fibre `(pi^+)^{-1}(omega)` for
`nu`-a.e. `omega`. By the chain rule and invariance,

`H(P_{-k} ∨ ... ∨ P_0 | F^+) = sum_{j=0}^{k} H(P_{-j} | P_{-j+1} ∨ P_{-j+2} ∨ ...) = (k + 1) h`.

The left side is `∫ H_omega d nu`, where `H_omega` is the entropy of the law of the word `(s_{-k}, ..., s_0)` under
`rho_omega` (normalized). Also `H_omega <= (k + 1) log |S|`. Let `A_k` be the set of `omega` for which that law has
at least `e^{(k+1) h / 2}` atoms. Off `A_k`, `H_omega < (k + 1) h / 2`. So

`(k+1) h <= nu(A_k)(k+1) log|S| + (1 - nu(A_k))(k+1) h/2`, hence `nu(A_k) >= beta := (h/2)/(log|S| - h/2) > 0`

for every `k`. Distinct words give distinct points of the fibre. So `nu{omega : |(pi^+)^{-1}(omega)| >= e^{(k+1)h/2}}
>= beta` for all `k`. These sets decrease in `k`, and their intersection `{omega : fibre infinite}` has
`nu`-measure at least `beta`. The fibres of `zeta^#` contain those of `pi^+`. If `X'` is any invariant conull set,
`rho_omega(X') = 1` for a.e. `omega`, so the fibres stay infinite inside `X'`. Hence (FT) fails on every invariant
conull set.

**(2) Zero entropy gives injective codings.** If `h = 0`, then `H(P_0 | F^+) = 0`, so `s_0 = f_0(pi^+)` a.e. for a
Borel `f_0`. By invariance, `s_{-k}` is a.e. a Borel function of `(s_j)_{j > -k}`, and by induction of `pi^+`. Let
`X''` be the Borel set where all these identities hold. It is conull, and on it the two-sided word, hence the point,
is a function of `pi^+`. So `pi^+` is injective on the invariant conull set `⋂_j (T^#)^j X''`. The same argument with
`h(T^{#-1}) = 0` makes `pi^-` injective on an invariant conull set. On the intersection `X'''`:
- `zeta^#` is finite-to-one iff only finitely many forward words in `pi^+(X''')`, read from `1`, share an endpoint;
- `zeta^{-#}` is countable-to-one iff only countably many backward words in `pi^-(X''')` share an endpoint.

This is **finite spelling multiplicity**. `□`

The odometer, rotation and skeleton codes of the earlier nodes are zero-entropy (odometers and rotations have
discrete spectrum), so for them (FT) and (CT) are exactly statements about spelling multiplicity.

## Step 6. Corollary 4 and the recoding calibration

*Corollary 4.* A cocompact `Sp(n,1)` lattice is hyperbolic (it acts properly and cocompactly on quaternionic
hyperbolic space). Theorem 1 needs only hyperbolicity, so it applies to `Gamma` directly. Its conclusion does not
mention the matches at all.

*Recoding.* Let `(Omega, +1, G_0)` be the symmetric lattice odometer code of
`fpbs-quasiconvex-null-lattice-odometer-class-dies`, on a torsion-free finite-index subgroup `Gamma_0`, with (UQ),
(MR) and (MR±) on a conull invariant set `Omega_1`. On `X_0 = Omega_1 x {0, 1}`, let copy `0` carry `G_0`. On copy
`1`, group the same letter sequence differently: each insertion together with the whole preceding `F`-run becomes
one letter `w s_j`, spelled `sigma(w) sigma(s_j)`. Every other `F`-letter stays as it is. Let `T` be the successor on
each copy's regrouped sequence. This is aperiodic, and it is Borel because the run boundaries read off the odometer
digits.
- The bi-infinite `S`-words at corresponding positions of the two copies are equal. So (UQ) holds with the same
  constants, and `zeta^#` takes the same values at corresponding positions.
- A copy-`1` point `(x, 1)` at a run start has `zeta(x, 1) = zeta(x, 0)`, and `(x, 0)` is not in its `T`-orbit. So
  (MR) fails on every point of copy 1. With `rho = m_Omega x` (uniform on `{0, 1}`), that is measure `1/2`.
- A merged letter `w s_j` has a geodesic that fellow-travels the coset segment of `w`. The runs `w` have unbounded
  length, so (I1) of the skeleton node fails for every `D`.
- Each `zeta^#`-fibre is the union of a copy-0 fibre and the corresponding copy-1 fibre. So it has at most
  `2(2 lambda c + 1)` points off a countable set, by Step 4. `zeta^{-#}` fibres stay countable in the same way.

Theorem 1 applies, and the class, which is the class of the original code, dies. Neither
`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups` (no (MR)) nor `fpbs-transverse-skeleton-ray-codes-are-match-rigid`
(no (I1)) applies to this code. So off-orbit matches, even on half the space and with non-transverse insertions, are
not an invariant of the class.
