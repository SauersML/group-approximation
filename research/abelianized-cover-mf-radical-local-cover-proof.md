---
rg: 2
id: abelianized-cover-mf-radical-local-cover-proof
kind: route
title: Amplify by tensor powers, diagonalize over the chain, and read partial homomorphisms off the free group
target: abelianized-cover-mf-radical-is-union-of-local-cover-radicals
requires:
  - universal-mf-quotient
---

Notation and conventions.

- A *corona* is `Q = prod_n M_(k_n) / (+)_n M_(k_n)` for a sequence of
  positive integers `k_n`.
- A *model* of a countable group `Gamma` is a homomorphism
  `Gamma -> U(Q)`.
- `Rad_MF(Gamma)` is the intersection of the kernels of all models.
  `universal-mf-quotient` says `Gamma` is MF iff `Rad_MF(Gamma) = 1`.
- `S_L` is the set of reduced words of length at most `L` in `F`.

Two elementary facts are used throughout.

- **(L1) Lifts.**  Every unitary of `Q` lifts to a sequence of unitaries.
  If `a = (a_n)` lifts a unitary, then `||a_n^* a_n - 1|| -> 0` and
  `||a_n a_n^* - 1|| -> 0`.  So `a_n` is invertible for large `n`, and its
  polar part `w_n = a_n (a_n^* a_n)^(-1/2)` is a unitary with
  `||a_n - w_n|| -> 0`.  The quotient norm on `Q` is
  `||(b_n)|| = limsup_n ||b_n||`.  So for a unitary lift `(u_n)` of `x`,
  `||x - 1|| = limsup_n ||u_n - 1||`.
- **(L2) Subsequences.**  If `n_j` is strictly increasing, restriction to the
  coordinates `n_j` is a unital `*`-homomorphism
  `prod_n M_(k_n) -> prod_j M_(k_(n_j))` that preserves the ideals `(+)`.
  So it induces a unital `*`-homomorphism of coronas, and composing a model
  with it gives a model.

## Step 1. Amplification

**Lemma A.**  If `g notin Rad_MF(Gamma)`, there is a model `sigma` of
`Gamma` with `||sigma(g) - 1|| >= sqrt 3`.

*Proof.*

1. Take a model `rho` with `rho(g) != 1`, and choose unitary lifts `u_n(h)`
   of `rho(h)` for each `h in Gamma`, by (L1).  For all `h, h'`,
   `||u_n(h) u_n(h') - u_n(hh')|| -> 0`.
2. Let `t = limsup ||u_n(g) - 1|| > 0`.  Choose `n_j` with
   `||u_(n_j)(g) - 1|| -> t`.  Since `u_(n_j)(g)` is unitary, it has an
   eigenvalue `mu_j` with `|mu_j - 1| = ||u_(n_j)(g) - 1||`.  Pass to a
   further subsequence so that `mu_j -> lambda`.  Then `|lambda| = 1` and
   `|lambda - 1| = t > 0`.
3. Write `lambda = e^(i theta)` with `0 < |theta| <= pi`.
   - If `|theta| >= 2pi/3`, put `k = 1`.
   - Otherwise let `k` be minimal with `k|theta| >= 2pi/3`.  Then
     `k|theta| < 2pi/3 + |theta| < 4pi/3`.

   In both cases `Re lambda^k <= -1/2`, so
   `|lambda^k - 1|^2 = 2 - 2 Re lambda^k >= 3`.
4. Put `v_j(h) = u_(n_j)(h)^(tensor k)`, a unitary in `M_(k_(n_j)^k)`.  For
   unitaries, `a^(tensor k) b^(tensor k) = (ab)^(tensor k)` and
   `||a^(tensor k) - b^(tensor k)|| <= k ||a - b||` (telescope one factor at
   a time).  Hence
   `||v_j(h) v_j(h') - v_j(hh')|| <= k ||u_(n_j)(h) u_(n_j)(h') - u_(n_j)(hh')|| -> 0`.
5. So `(v_j)` defines a model `sigma` of `Gamma` in the corona with
   dimensions `k_(n_j)^k`.  The unitary `v_j(g)` has the eigenvalue
   `mu_j^k -> lambda^k`.  By (L1),
   `||sigma(g) - 1|| >= limsup |mu_j^k - 1| = |lambda^k - 1| >= sqrt 3`.
   QED

## Step 2. Proof of (U1)

Setup: `K_1 <= K_2 <= ...` normal in `F`, `K = U K_L`, `H = F/K`,
`H_L = F/K_L`.  Let `pi_(L,L') : H_L -> H_(L')` for `L <= L'` and
`pi_L : H_L -> H` be the canonical surjections.

**The union is increasing and normal.**
- If `sigma` is a model of `H_(L')`, then `sigma o pi_(L,L')` is a model of
  `H_L`, so it kills `Rad_MF(H_L)`.  Hence
  `pi_(L,L')(Rad_MF(H_L)) <= Rad_MF(H_(L'))`, and after applying `pi_(L')` the
  images increase with `L`.
- Each image is normal, because `pi_L` is onto.
- So the union `Phi` is a normal subgroup of `H`.

**`Phi <= Rad_MF(H)`.**  For a model `sigma` of `H`, `sigma o pi_L` is a model
of `H_L`.  It kills `Rad_MF(H_L)`, so `sigma` kills `pi_L(Rad_MF(H_L))`.

**`Rad_MF(H) <= Phi`.**  Let `h = wK notin Phi`, where `w in F`.  For every
`L`, `w K_L notin Rad_MF(H_L)`: otherwise `h = pi_L(w K_L)` would lie in `Phi`.

1. Since `K` is the increasing union of the `K_L`, and `K cap S_L` is finite,
   there is `M(L) >= L` with `K cap S_L <= K_(M(L))`.
2. By Lemma A, `H_(M(L))` has a model `sigma^L` with
   `||sigma^L(w K_(M(L))) - 1|| >= sqrt 3`.  Fix unitary lifts
   `(a_n^L(x))_n` of `sigma^L(x K_(M(L)))` for the generators `x in X`.
   Let `V_n^L : F -> U(d_n^L)` be the exact representation of the free group
   with `V_n^L(x) = a_n^L(x)`.
3. `(V_n^L(v))_n` lifts `sigma^L(v K_(M(L)))` for every `v in F`.  This holds
   because `sigma^L` is multiplicative and `v` is a finite product of the
   `x^(+-1)`, whose images are lifted by `a_n^L(x)^(+-1)`.
4. Hence:
   - `||V_n^L(v) - 1|| -> 0` as `n -> infinity`, for each of the finitely
     many `v in K cap S_L <= K_(M(L))`;
   - `limsup_n ||V_n^L(w) - 1|| >= sqrt 3`.

   Choose `n = n(L)` with `||V_n^L(v) - 1|| <= 1/L` for all
   `v in K cap S_L`, and `||V_n^L(w) - 1|| >= sqrt 3 - 1/L`.
   Put `W_L = V_(n(L))^L`.
5. `W = (W_L)_L : F -> prod_L U(d_(n(L))^L)` is a homomorphism.  Compose it
   with the quotient map to the corona with dimensions `d_(n(L))^L`.
   - For `v in K` and every `L >= |v|`, we have `v in K cap S_L`, so
     `||W_L(v) - 1|| <= 1/L`.  So `v` maps to `1`, and the composite factors
     through a model `tau` of `H`.
   - `||tau(h) - 1|| = limsup_L ||W_L(w) - 1|| >= sqrt 3`.

   So `h notin Rad_MF(H)`.  QED (U1)

`X` is taken finite throughout, so that each `S_L` is finite.  This is the
only case used.

## Step 3. Proof of (U2)

Now assume that each `K_L = << T_L >>` with `T_L` finite.

- `H` is *LEF* if for every `rho` there are a finite group `P` and an
  injective map `psi : B_rho(H) -> P` such that `psi(ab) = psi(a) psi(b)`
  whenever `a`, `b` and `ab` all lie in `B_rho(H)`.
- Here `B_rho(H)` is the image of `S_rho`.  Balls are cofinal among finite
  subsets, so this is the usual definition.
- As in Step 2, the images `pi_L(fr(H_L))` increase with `L`, because a
  finite quotient of `H_(L')` is a finite quotient of `H_L`.  So their union
  `Phi_fin` is a normal subgroup.

**`Phi_fin = 1` implies LEF.**

1. Fix `rho`.  Let `S = S_(2 rho) \ K`, a finite set.  Choose `L` with
   `K cap S_(3 rho) <= K_L`.
2. For each `u in S`, `u K_L notin fr(H_L)`, since otherwise `uK` would be a
   nontrivial element of `Phi_fin`.  So some finite quotient `phi_u` of
   `H_L` has `phi_u(u) != 1`.  Let `phi` be the diagonal map into
   `prod_(u in S) phi_u(H_L)`, and let `P` be its image, which is finite.
   Then `phi(u) != 1` for every `u in S`.
3. Define `psi(vK) = phi(v)` for `v in S_rho`.
   - **Well defined.**  If `vK = v'K`, then `v^-1 v' in K cap S_(2 rho) <= K_L`.
   - **Injective.**  If `vK != v'K`, then `v^-1 v' in S`.
   - **Multiplicative.**  If `a = uK`, `b = vK` and `ab = yK` all lie in the
     ball, then `u v y^-1 in K cap S_(3 rho) <= K_L`, so `phi(u)phi(v) = phi(y)`.

**LEF implies `Phi_fin = 1`.**

1. Suppose `h = wK in pi_L(fr(H_L))`.  Take
   `rho >= max(1, |w|, max_(t in T_L) |t|)` and an LEF map `psi` on
   `B_rho(H)` into a finite group `P`.
2. `psi(1) = psi(1)^2`, so `psi(1) = 1`.  Also
   `psi(xK) psi(x^-1 K) = psi(1) = 1` for every `x in X`.
3. Let `phi : F -> P` be the homomorphism with `phi(x) = psi(xK)`.
   Induction on word length, using multiplicativity on the ball, gives
   `phi(v) = psi(vK)` for every `v in S_rho`.
4. So `phi(t) = psi(1) = 1` for `t in T_L`.  Hence `phi` factors through a
   homomorphism `H_L -> P` with finite image, which kills `fr(H_L)`.
   Therefore `psi(h) = phi(w) = 1 = psi(1)`, and `h = 1` by injectivity.

QED (U2)

**Remark.**  For finitely generated `Gamma`, `Rad_MF(Gamma) <= fr(Gamma)`,
because finite groups are MF.  So `Phi <= Phi_fin`, which is consistent with
LEF implying MF.

## Step 4. The abelianized cover

Let `G = <X | r_1, ..., r_m>` with `X` finite, `R = <<r_j>>`,
`c = max |r_j|`, `E = F/[R,R]`, and
`N_L = << [u,v] : u, v in R cap S_L >>`.

**(a) The chain.**
- `R cap S_L` is finite, so `N_L` is finitely normally generated.
- `N_L <= N_(L+1) <= [R,R]`.
- `[R,R]` is generated by the commutators `[u,v]` with `u, v in R`, and
  `[u,v] in N_(max(|u|,|v|))`.  So `U_L N_L = [R,R]`.
- Steps 2 and 3 therefore apply with `K_L = N_L` and `H = E`.

**(b) Abelianization.**
- `N_L <= [R,R] <= [F,F]`, so `Gamma_L^ab = F^ab = Z^|X|`.
- `Z^|X|` is residually finite, hence MF.  A surjection maps `Rad_MF` into
  `Rad_MF` (Step 2) and `fr` into `fr` (Step 3).  So `Rad_MF(Gamma_L)` and
  `fr(Gamma_L)` both lie in `[Gamma_L, Gamma_L] = [F,F] N_L / N_L`.
- `Gamma_L` has an infinite abelian quotient, so it is not Kazhdan.

**(c) Item 1.**
- By `universal-mf-quotient`, `E` is non-MF iff `Rad_MF(E) != 1`.  By (U1)
  this holds iff `pi_L(Rad_MF(Gamma_L)) != 1` for some `L`.
- An element of that image is `w[R,R]` with `w N_L in Rad_MF(Gamma_L)` and
  `w notin [R,R]`.  By (b), `w` may be chosen in `[F,F]`.
- Monotonicity in `L` is the first paragraph of Step 2.

**(d) Item 2.**  This is (U2) with `K_L = N_L`.

**(e) Item 3.**  Assume `G` has no nontrivial finite quotient.  Let
`phi : F ->> P` factor through `Gamma_L`, with `P` finite.
- `phi(R)` is normal, and `P/phi(R)` is a finite quotient of `F/R = G`, so
  `P = phi(R)`.  Then `[P,P] = [phi(R), phi(R)] = phi([R,R])`.
- Likewise `P/<<phi(r_j)>>` is a finite quotient of `G`, so
  `P = <<phi(r_j)>>`.
- Let `D` be the diameter of the Cayley graph of `P` with respect to
  `phi(X)`, so every element of `P` is `phi(v)` for some `|v| <= D`.  Then
  `P` is generated by the elements `phi(v r_j v^-1)` with `|v| <= D`.
- If `2D + c <= L`, these words lie in `R cap S_L`, so their images commute
  pairwise in `Gamma_L`, and `P` is abelian.
- So a non-abelian `P` has `2D + c >= L + 1`.  Abelian `P` factor through
  `F^ab`, so they kill `[F,F]`.

**(f) Item 4.**  If every nontrivial element of `R` is longer than `L`, then
the generating set of `N_L` consists of trivial commutators.  So
`Gamma_L = F`, which is MF.  The equivalence `(DF) <=> L* < infinity` is
item 1.

QED
