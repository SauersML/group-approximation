# Deligne twisted algebras: stable finiteness is the rank condition (swarm, 2026-09-16)

Target hole: `deligne-twisted-group-algebra-is-not-stably-finite` (OPEN before and after this artifact).

New nodes supported here:
- `lef-graded-simple-base-sf-iff-rank-condition` (Sections 1–2), route
  `lef-graded-simple-base-sf-iff-rank-condition-proof`;
- `deligne-twisted-sf-iff-wf-rep-detects-center` (Section 3), route
  `deligne-twisted-sf-iff-wf-rep-detects-center-proof`.

## 0. Summary and conventions

**What is proved.**
1. **Absorption (Lemma 1.1, Proposition 1.2).** Let `A = ⊕_g A_g` be a `Gamma`-graded unital ring and
   `phi : A -> R` a unital homomorphism that is injective on every component `A_g`. Then
   `Phi(Σ x_g) = Σ phi(x_g) g` is a unital injective ring homomorphism `A -> R[Gamma]`.
2. **Theorem 2.1.** Let `Gamma` be LEF and `A` strongly `Gamma`-graded with simple identity component (for
   example any twisted group algebra `F^alpha[Gamma]` over a field). These are equivalent:
   - (i) `A` is stably finite;
   - (ii) `A` has a nonzero weakly finite homomorphic image;
   - (iii) `A` satisfies the rank condition;
   - (iv) `(K_0(A), [A])` has a state;
   - (v) no matrix ring `M_n(A)` is properly infinite.
   The general gap between the rank condition and stable finiteness (the Toeplitz algebra) closes here.
3. **Theorem 3.1 (Deligne dichotomy).** For `p != 3` the target at `p` is equivalent to
   `z in N_p`. Here `N_p` is the intersection of the kernels of all homomorphisms from `E_3` to unit groups
   of weakly finite rings of characteristic `p`, and `N_p` is either `1` or `<z>`. The target at `p` does
   not depend on `j` or on the finite field `F`. It holds iff some `M_n(A_1)` is properly infinite, and a
   witness can always be taken with a free rank-one summand in its defect.
4. **Section 4.** Consequences of a witness at `p`:
   - every Sylvester matrix rank function on `F[E_3]` is pulled back from `F[Sp_4(Z)]`;
   - every weakly finite representation of `E_3` in characteristic `p` factors through `Sp_4(Z)`.
5. **Section 5.** Records which images of `A_j` cannot exist and what remains open:
   - no PI images, and no algebraic ultraproducts or `Π/⊕` of matrix algebras;
   - Noetherian images reduce to homomorphisms `E_3 -> GL_d(D)` over division rings, which are open;
   - finite subgroups give no Herstein-type obstruction.

Nothing here decides the target. It is a reduction: the target is equivalent to a representation-theoretic
statement about `E_3`, and every witness is forced to be a compression.

**Conventions.**
- Rings are unital, homomorphisms and subrings unital.
- A ring `R` is **weakly finite** (= stably finite) if `XY = I_n` implies `YX = I_n` for all square `X, Y`
  over `R`. The zero ring counts as weakly finite; "nonzero" is always said explicitly.
- `R` has the **rank condition** if there are no `n >= 0`, `X in M_((n+1) x n)(R)` and
  `Y in M_(n x (n+1))(R)` with `XY = I_(n+1)`, that is, `R^(n+1)` is never a retract of `R^n`. For
  `m > n`, `XY = I_m` with `X` of size `m x n` restricts to the first `n+1` rows and columns, so `m = n+1`
  is the general case.
- `R` is **properly infinite** if there are `X_1, X_2, Y_1, Y_2 in R` with `X_i Y_k = delta_ik`.
- A group `Gamma` is **LEF** if every finite `E ⊂ Gamma` has an injective map into a finite group
  preserving every product `ab = c` with `a, b, c in E`. Residually finite groups are LEF: take a finite
  quotient injective on `E ∪ E·E`.
- `Gamma`-graded: `A = ⊕_(g in Gamma) A_g` with `A_g A_h ⊂ A_(gh)`, so `1 in A_1`. **Strongly graded** means
  `A_g A_h = A_(gh)` for all `g, h`.
- For a field `F` and a normalized 2-cocycle `alpha : Gamma x Gamma -> F^x`, the twisted group algebra
  `F^alpha[Gamma]` has `F`-basis `u_g`, `u_g u_h = alpha(g,h) u_(gh)`, `u_1 = 1`, with `F` central. It is
  strongly graded with `A_g = F u_g` and `A_1 = F` simple, since each `u_g` is a unit.
- **Deligne data.**
  - `1 -> C_3 = <z> -> E_3 -> Gamma = Sp_4(Z) -> 1` is the triple cover.
  - `a` is its section cocycle, with a section `s(g)s(h) = z^(a(g,h)) s(gh)`.
  - For a field `F` of characteristic `p != 3` containing a primitive cube root of unity `w`:
    `A_j(F) = F^(w^(ja))[Gamma] = F[E_3]/(z - w^j)`, with basis the images `u_g` of `s(g)`.
  - The central idempotents `e_k = (1/3)Σ_i w^(-ki) z^i` give `F[E_3] = F[Gamma] x A_1(F) x A_2(F)`.
  - `F_0 = F_p(w)`.

## 1. The absorption embedding

**Lemma 1.1 (absorption).** Let `A = ⊕_g A_g` be a `Gamma`-graded ring, `R` a ring, and `phi : A -> R` a
unital ring homomorphism. Let `R[Gamma]` be the ordinary group ring, whose group labels commute with `R`.
1. `Phi : A -> R[Gamma]`, `Phi(Σ_g x_g) = Σ_g phi(x_g) g` (with `x_g in A_g`) is a unital ring homomorphism.
2. `Phi` is injective iff `phi` is injective on every `A_g`.

*Proof.*
1. `Phi` is additive since the decomposition `x = Σ x_g` is additive. `1 in A_1`, so
   `Phi(1) = phi(1)·1 = 1`. For homogeneous `x in A_g`, `y in A_h` we have `xy in A_(gh)`, so
   `Phi(x)Phi(y) = phi(x) g phi(y) h = phi(x)phi(y) gh = phi(xy) gh = Phi(xy)`. Multiplicativity on sums
   follows by bilinearity.
2. The group labels are an `R`-basis of `R[Gamma]`, so `Phi(Σ x_g) = 0` iff `phi(x_g) = 0` for every `g`.
   If `phi` is injective on each `A_g`, this forces every `x_g = 0`. Conversely a nonzero `x in A_g` with
   `phi(x) = 0` lies in `ker Phi`. ∎

**Proposition 1.2 (strong grading over a simple base).** Let `A` be strongly `Gamma`-graded with `A_1`
simple, and `phi : A -> R` unital with `R != 0`. Then `phi` is injective on every `A_g`, so `A` embeds
unitally in `R[Gamma]`.

*Proof.*
- `ker phi ∩ A_1` is a two-sided ideal of `A_1` missing `1` (as `phi(1) = 1 != 0`), hence `0`.
- Let `x in A_g` with `phi(x) = 0`. Then `x A_(g^-1) ⊂ A_1 ∩ ker phi = 0`.
- Strong grading gives `1 in A_1 = A_(g^-1) A_g`, so `x = x·1 in (x A_(g^-1)) A_g = 0`.
- Lemma 1.1 finishes. ∎

**Examples.**
- Twisted group algebras `F^alpha[Gamma]` over a field: `A_g = F u_g`, and `phi(u_g)` is a unit of
  `R != 0`. Directly: `phi(c u_g) = phi(c)phi(u_g)` is a unit for `c in F^x`.
- Crossed products `S *_(sigma, alpha) Gamma` over a simple ring `S`.
- More generally, strongly graded rings with simple identity component. The Leavitt algebras `L(1,n)`,
  `n >= 2`, with `deg x_i = 1`, `deg y_i = -1` should be an instance: the identity component is the simple
  ultramatricial algebra `lim M_(n^k)(K)`, and strong grading is Hazrat's criterion for graphs without sinks
  (not re-fetched here). They fail both the rank condition and stable finiteness, consistent with
  Theorem 2.1.

**Non-example.** The Toeplitz algebra `T = K<x, y | yx = 1>` with the `Z`-grading `deg x = 1`, `deg y = -1`.
- `T_0` is spanned by the commuting idempotents `x^a y^a`, `a >= 0`. It is commutative with the non-trivial
  idempotent `xy`, so it is not a field and not simple.
- `T_1 T_(-1)` is spanned by `x^a y^a` with `a >= 1`, so it misses `1`, and `T` is not strongly graded.
- `T` has the rank condition (it maps onto the commutative ring `K[t, t^-1]`) but is not directly finite.
- So the simplicity hypothesis in Proposition 1.2 cannot be dropped.

**Remark 1.3 (the classical special case).**
- For `A = F[Gamma]` and `phi` the augmentation, `Phi` is the identity. Lemma 1.1 is the algebraic form of
  the comodule map `A -> A ⊗ F[Gamma]`, `u_g -> u_g ⊗ g`, followed by `phi ⊗ id`.
- In the C*-setting this is Fell absorption.
- No algebraic source stating Proposition 1.2 for stable finiteness was located (Section 6). It is recorded
  as probably folklore.

## 2. Stable finiteness equals the rank condition over LEF gradings

**Theorem 2.1.** Let `Gamma` be LEF and `A` a strongly `Gamma`-graded ring whose identity component `A_1`
is simple. The following are equivalent:
- (i) `A` is stably finite;
- (ii) `A` has a nonzero weakly finite homomorphic image;
- (iii) `A` satisfies the rank condition;
- (iv) `(K_0(A), [A])` admits a state, i.e. an additive `s : K_0(A) -> R` with `s([P]) >= 0` for f.g.
  projective `P` and `s([A]) = 1`;
- (v) no matrix ring `M_n(A)`, `n >= 1`, is properly infinite.

In particular this holds for every twisted group algebra `F^alpha[Gamma]` of an LEF group over a field,
with any cocycle `alpha`.

*Proof.* `A != 0`, since `A_1` is simple.

- **(i) ⇒ (ii).** Take the identity map.
- **(ii) ⇒ (i).**
  1. Let `phi : A -> R` with `R != 0` weakly finite.
  2. Proposition 1.2 gives a unital embedding `A -> R[Gamma]`.
  3. `R[Gamma]` is stably finite by `lef-group-rings-over-stably-finite-rings-are-stably-finite`, which
     allows noncommutative `R` and ordinary group labels commuting with `R`.
  4. A unital subring of a stably finite ring is stably finite: `M_n(A) ⊂ M_n(R[Gamma])`, and `XY = I`
     gives `YX = I` there, hence in `M_n(A)`.
- **(iii) ⇒ (ii).** This is `rank-condition-rings-have-weakly-finite-images` (Malcolmson's theorem, proved
  locally on main).
- **(i) ⇒ (iii).** Suppose `X in M_((n+1) x n)(A)`, `Y in M_(n x (n+1))(A)` and `XY = I_(n+1)`.
  1. Pad to square matrices `X~ = [X | 0]` and `Y~ = [[Y],[0]]` of size `n+1`.
  2. Then `X~ Y~ = XY = I_(n+1)`, while `Y~ X~ = diag(YX, 0) != I_(n+1)`, since `A != 0`.
  3. So `M_(n+1)(A)` is not directly finite.
- **(i) ⇒ (v).** Suppose `X_i Y_k = delta_ik I_n` in `M_n(A)`.
  1. Direct finiteness applied to `X_1 Y_1 = I` gives `Y_1 X_1 = I`.
  2. Then `X_2 = X_2 (Y_1 X_1) = (X_2 Y_1) X_1 = 0`.
  3. So `I = X_2 Y_2 = 0`, a contradiction.
- **(v) ⇒ (iii).** Contrapositive. Let `XY = I_(n+1)` as above, so `n >= 1`.
  1. Here `Y : A^(n+1) -> A^n` and `X : A^n -> A^(n+1)` exhibit `A^(n+1)` as a retract of `A^n`.
  2. Adding identities, `A^(n+k) = A^(n+1) ⊕ A^(k-1)` is a retract of `A^n ⊕ A^(k-1) = A^(n+k-1)` for
     every `k >= 1`.
  3. Composing these retractions for `k = 1, ..., n`, `A^(2n)` is a retract of `A^n`. So there are
     `X' in M_(2n x n)(A)` and `Y' in M_(n x 2n)(A)` with `X'Y' = I_(2n)`.
  4. Cut `X'` into two `n x n` row blocks `X_1, X_2` and `Y'` into two `n x n` column blocks `Y_1, Y_2`.
     Then `X'Y' = I_(2n)` reads `X_i Y_k = delta_ik I_n`, so `M_n(A)` is properly infinite.
- **(iii) ⇔ (iv).** Lemma 2.2. ∎

**Lemma 2.2 (Goodearl–Handelman form).** For any ring `A != 0`, `(K_0(A), [A])` has a state iff `A` has the
rank condition.

*Proof.* Write `G = K_0(A)`, `G^+ = {[P]}` and `u = [A]`. Recall that `[P] = [Q]` iff `P ⊕ A^k ≅ Q ⊕ A^k` for
some `k`, and that `u` is an order unit: `-Nu <= x <= Nu` for some `N`.

*State ⇒ rank condition.* If `A^(n+1)` is a retract of `A^n`, then `A^n ≅ A^(n+1) ⊕ P`. Applying a state
gives `n = n+1 + s([P]) >= n+1`, which is impossible.

*Rank condition ⇒ state.*
1. **`-u ∉ G^+`.** If `-[A] = [P]`, then `P ⊕ A ⊕ A^k ≅ A^k` for some `k`, so `A^(k+1)` is a retract of
   `A^k`. Hence `-ru ∉ G^+` for every `r >= 1`, since `-u = -ru + (r-1)u`.
2. **The sublinear functional.** Put `p(x) = inf{ m/k : k >= 1, m in Z, kx <= mu }`.
   - The set is nonempty, since `x <= Nu`.
   - If `kx <= mu`, adding `-kx <= kNu` gives `(m + kN)u >= 0`, so `m + kN >= 0` by step 1. Hence
     `p(x) >= -N`.
   - `p` is subadditive: `kx <= mu` and `k'y <= m'u` give `kk'(x+y) <= (k'm + km')u`.
   - `p(qx) = q p(x)` for integers `q >= 1`.
   - `p(0) = 0`, `p(u) = 1` and `p(-u) = -1`. Each lower bound is step 1 again: for example `ku <= mu` with
     `m < k` would put `-(k-m)u` in `G^+`.
   - If `x in G^+`, then `1·(-x) <= 0·u`, so `p(-x) <= 0`.
3. **Extension.** By homogeneity `p` descends to a sublinear functional on the `Q`-vector space
   `G ⊗ Q`: torsion `t` has `p(t) = p(qt)/q = 0`, and `p(x + t) = p(x)`.
   - Define `f(qu) = q` on `Q u`. Then `f <= p` there, using `p(u) = 1` and `p(-u) = -1`.
   - The one-dimensional Hahn–Banach step uses only positive rational scaling, so it runs verbatim over
     `Q`. Zorn's lemma extends `f` to an additive `f <= p` on `G ⊗ Q`.
4. **The state.** Put `s = f|_G`. Then `s(u) = 1`, and for `x in G^+`, `-s(x) = f(-x) <= p(-x) <= 0`. ∎

The same criterion is proved by Hahn–Banach, for the ternary anti-central summand, in
`research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md`
(`anti-central-state-obstruction-equals-stable-finiteness`). The argument above is general and
self-contained.

**Remark 2.3 (what the hypotheses do).**
- **The general gap.** For arbitrary rings (iii) is strictly weaker than (i); see the Toeplitz algebra in
  Section 1. Simple rings are the trivial grading `Gamma = 1`. For them Theorem 2.1 recovers the classical
  fact that a simple ring with the rank condition is weakly finite: a nonzero defect projective is a
  generator.
- **Only one use of LEF.** The group enters only through `R[Gamma]` being stably finite for every weakly
  finite `R`. For sofic `Gamma` the literature gives `D[Gamma]` stably finite for division rings `D`
  (Elek–Szabó 2004; not re-fetched). The proof then gives only: a nonzero image in some `M_d(D)` implies
  stable finiteness.
- **Sylvester rank functions.** A Sylvester matrix rank function `rk` with `rk(1) = 1` gives (iii), since
  `n+1 = rk(XY) <= rk(X I_n) <= n`. The converse for arbitrary rings is the OPEN
  `rank-condition-rings-carry-sylvester-rank-functions`. Theorem 2.1 does not touch it.

**Remark 2.4 (another instance on main; hypotheses not re-verified).**
- `research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md`, Section 3, writes the
  anti-central factor as a skew group ring `A_S = C_S * G`. Here `C_S` is the twisted group algebra over
  `F_3` of `V = F_2^(X)` with commutator form `b_S`, and `G` is residually finite by that artifact.
- A skew group ring is strongly graded (`A_g = C_S g`, with `g` a unit).
- If `b_S` has trivial radical, then `C_S` is simple. Take a nonzero element of an ideal with minimal
  support containing `0`. If `v != 0` is in the support, pick `w` with `b_S(v, w) = 1`; then
  `u_w x u_w^(-1) - x` is nonzero with smaller support. Minimal support is therefore `{0}`, and the ideal
  contains a unit.
- The complete graph on the infinite set `X` has trivial radical: for a finite nonempty `T ⊂ X`, the vector
  `Σ_(x in T) x` pairs to `|T| - 1` with points of `T` and to `|T|` with points outside `T`, and these are
  not both even.
- So for such `S`, Theorem 2.1 applies: `A_S` is stably finite iff it has the rank condition iff it has a
  nonzero weakly finite image. This concerns `kun-thom-clifford-skew-rings-are-stably-finite`, and it is not
  recorded as a node, since the setup of that artifact was not re-checked here.

## 3. The Deligne dichotomy

Fix a prime `p != 3` and put `F_0 = F_p(w)`, which is `F_p` for `p ≡ 1 mod 3` and `F_(p^2)` for
`p ≡ 2 mod 3`. Let `N_p` be the intersection of `ker rho` over all nonzero weakly finite rings `R` with
`p·1_R = 0` and all group homomorphisms `rho : E_3 -> R^x`. Since `M_n(R)` is weakly finite with `R`, this
includes every `rho : E_3 -> GL_n(R)`.

**Theorem 3.1 (Deligne dichotomy).** The following are equivalent:
- (a) the target at `p`: for some finite field `F ⊇ F_0` and some `j`, `A_j(F)` is not stably finite;
- (b) `A_j(F)` is not stably finite for every finite `F ⊇ F_0` and both `j`;
- (c) `A_1(F_0)` fails the rank condition, i.e. `XY = I_(n+1)` for some `X in M_((n+1) x n)`,
  `Y in M_(n x (n+1))`. Equivalently, `A_1(F_0)` has no nonzero weakly finite image, and
  `(K_0(A_1(F_0)), [1])` has no state;
- (d) some `M_n(A_1(F_0))` is properly infinite;
- (e) `z in N_p`: every homomorphism from `E_3` to the unit group of a weakly finite ring of characteristic
  `p` kills `z`, so factors through `Sp_4(Z)`.

Moreover `N_p` is `1` or `<z>`.

*Proof.*

**Step 1 (LEF).** `Sp_4(Z) <= GL_4(Q)` is finitely generated, so it is residually finite by
`finitely-generated-linear-groups-are-residually-finite`, hence LEF (Section 0). Each `A_j(F)` is a twisted
group algebra, so Theorem 2.1 applies to it over any field.

**Step 2 (independence of `j`).**
- The antipode `S(Σ c_g g) = Σ c_g g^(-1)` is an `F`-linear anti-automorphism of `F[E_3]`.
- `S(z - w^j) = z^(-1) - w^j = -w^j z^(-1) (z - w^(-j))`, a unit multiple of `z - w^(-j)` with `z` central.
  So `S` maps the ideal `(z - w^j)` onto `(z - w^(-j))`.
- Hence `A_j(F)^op ≅ A_(3-j)(F)`.
- Stable finiteness passes to opposite rings, since transpose gives `M_n(R^op) ≅ M_n(R)^op`.

**Step 3 (independence of the finite field).** Let `F ⊇ F_0` be finite with `F_0`-basis `b_1, ..., b_d`.
- The inclusion `A_j(F_0) ⊂ A_j(F)` is unital, since the `u_g` are a basis over both fields.
- `A_j(F) = F ⊗_(F_0) A_j(F_0)` is a free right `A_j(F_0)`-module with basis `b_1, ..., b_d`, since `F` is
  central.
- Left multiplication is therefore a unital injective homomorphism `A_j(F) -> M_d(A_j(F_0))`.
- So `A_j(F)` is stably finite iff `A_j(F_0)` is.

**Step 4 ((a) ⟺ (b) ⟺ (c) ⟺ (d)).**
- By Steps 2 and 3, stable finiteness of `A_j(F)` does not depend on `j` or `F`. This gives (a) ⟺ (b),
  and both are equivalent to `A_1(F_0)` not being stably finite.
- Theorem 2.1, (i) ⟺ (ii) ⟺ (iii) ⟺ (iv) ⟺ (v), turns that into (c) and (d).

**Step 5 ((a) ⟺ (e)).**
- **(e) ⇒ (a).** Suppose (a) fails, so `A_1(F_0)` is stably finite. The composite
  `rho : E_3 -> F_0[E_3] -> A_1(F_0)` sends `z` to `w != 1`. `A_1(F_0)` is nonzero, weakly finite and of
  characteristic `p`, so `z ∉ N_p`.
- **(a) ⇒ (e).** Suppose `rho : E_3 -> R^x` with `R` nonzero weakly finite, `p·1 = 0` and `rho(z) != 1`.
  1. **Adjoin `w`.** `R' = R ⊗_(F_p) F_0` is free of rank `[F_0 : F_p] <= 2` over `R`, so it embeds
     unitally in `M_2(R)` or equals `R`. It is weakly finite, `F_0` is central in it, and `R -> R'` is
     injective, so `rho(z) != 1` in `R'`.
  2. **The image ring.** Let `S` be the image of `F_0[E_3] -> R'`, a unital subring and hence weakly finite.
     `rho(z)` is central in `S` with `rho(z)^3 = 1`, and `3` is invertible.
  3. **The idempotents.** `e_k = (1/3)Σ_i w^(-ki) rho(z)^i` are central orthogonal idempotents of `S` with
     `Σ e_k = 1` and `rho(z) e_k = w^k e_k`.
  4. **Some `e_j != 0`.** `rho(z) - 1 = (w - 1)e_1 + (w^2 - 1)e_2 != 0`, so `e_j != 0` for some
     `j in {1, 2}`.
  5. **`S e_j` is nonzero and weakly finite.** If `XY = e_j I` in `M_n(S e_j)`, then
     `(X + (1-e_j)I)(Y + (1-e_j)I) = I` in `M_n(S)`. So `YX + (1-e_j)I = I` and `YX = e_j I`.
  6. **Conclude.** `x -> (image of x)·e_j` is a unital homomorphism `F_0[E_3] -> S e_j` killing
     `z - w^j`, so it factors through `A_j(F_0)`. Theorem 2.1 (ii) ⇒ (i) makes `A_j(F_0)` stably finite,
     and by Step 4 (a) fails.

**Step 6 (`N_p` is `1` or `<z>`).**
- Let `g ∉ <z>`. By `deligne-triple-cover-finite-residual-is-center` some finite quotient
  `pi : E_3 -> Q` has `pi(g) != 1`.
- The regular permutation representation `Q -> GL_(|Q|)(F_p)` is faithful, and `M_(|Q|)(F_p)` is nonzero,
  weakly finite and of characteristic `p`. So `g ∉ N_p`.
- Thus `N_p` is a normal subgroup of `<z> ≅ C_3`, hence `1` or `<z>`. ∎

**Corollary 3.2 (the target restated).** `deligne-twisted-group-algebra-is-not-stably-finite` holds iff for
some prime `p != 3` every weakly finite characteristic-`p` representation of `E_3` factors through
`Sp_4(Z)`. Equivalently, `A_1(F_p(w))` fails the rank condition for some `p != 3`.

**Remark 3.3 (relation to the 2026-09-12 artifact).**
- Corollary 2.5 of `research/artifacts/deligne-twisted-group-algebras-2026-09-12.md` derives stable
  finiteness from rank-approximate projective representations. That is one special weakly finite image: a
  rank ultraproduct, made weakly finite by `sylvester-rank-function-quotients-are-weakly-finite`.
- Theorem 3.1 removes metric, approximation and rank function altogether. One exact homomorphism from
  `E_3` into the units of any weakly finite ring of characteristic `p` not killing `z` refutes the target
  at `p`.
- A counterexample must kill `z` in all of them at once.

**Proposition 3.4 (inflation invariance).** Let `alpha` be any `F^x`-valued cocycle on a group `Gamma`, and
`beta = pi^* beta_0` inflated from a finite quotient `pi : Gamma -> Q` with `N = |Q|`.
1. `F^(alpha beta)[Gamma]` embeds unitally in `M_N(F^alpha[Gamma])`.
2. Conversely, since `beta^(-1)` is also inflated, `F^alpha[Gamma]` is stably finite iff
   `F^(alpha beta)[Gamma]` is.
3. So the target at `p` depends only on the class of the Deligne multiplier modulo coboundaries and finite
   inflations.

*Proof.*
- The map `u_g -> u_g ⊗ v_(pi(g))` into `F^alpha[Gamma] ⊗_F F^(beta_0)[Q]` is multiplicative, since the
  cocycles multiply.
- It is injective: the target is `⊕_q F^alpha[Gamma] ⊗ v_q`, since the `v_q` are an `F`-basis. A relation
  `Σ c_g u_g ⊗ v_(pi(g)) = 0` therefore splits over the fibres of `pi`, and each `c_g = 0`.
- `F^(beta_0)[Q] ⊂ M_N(F)` by the left regular representation. ∎

No LEF hypothesis is used in Proposition 3.4.

## 4. What a witness at p forces

Assume the target holds at `p != 3`, and let `F ⊇ F_0` be any field of characteristic `p` containing `w`
(finite in 4.1).

**4.1 Normal form of a witness.** Any witness `BA = 1 != AB` over any `A_j(F)` upgrades to the following.
- **Rectangular split.** `X in M_((n+1) x n)`, `Y in M_(n x (n+1))` over `A_1(F_0)` with `XY = I_(n+1)`.
  The square pair `[X | 0]`, `[[Y],[0]]` has defect `diag(I_n - YX, 1)`, which contains a free rank-one
  summand.
- **Proper infiniteness.** `X_i Y_k = delta_ik I_n` in some `M_n(A_1(F_0))`. So `M_n(A_1(F_0))` contains a
  unital image of the algebra presented by `x_i y_k = delta_ik`, `i, k in {1, 2}`.

**Trace check.**
- `tau(Σ c_g u_g) = c_1` is an `F`-valued trace: for normalized cocycles `alpha(g, g^(-1)) = alpha(g^(-1), g)`,
  by the cocycle identity at `(g, g^(-1), g)`.
- For the rectangular split, `tau(I_n - YX) = n - tau(XY) = n - (n+1) = -1` in `F`.
- Every square witness has defect trace `0`, so the mod-`p` trace constrains neither form. The upgrade is
  genuinely nonlinear: it comes from Malcolmson's maximal quotient and the absorption embedding, not from
  a formula.

**What this does to negative-side designs.**
- A counterexample cannot be "tracially small". It must build a compression `A^n ≅ A^(2n) ⊕ Q` inside a
  matrix ring over the Deligne twisted algebra.
- This matches the observation in the target's Attempts that every strict-pair design on main comes from a
  compressing host `R = R^2`. Theorem 2.1 shows that, for twisted group algebras of LEF groups, a
  compression is also *necessary*.

**4.2 Rank functions.** Every Sylvester matrix rank function `rk` on `F[E_3]` is pulled back from
`F[Sp_4(Z)]`: `rk(M) = rk(M e_0)` for every matrix `M`, and `rk(z - 1) = 0`.

*Proof.*
1. **Corners carry rank functions.** Let `e_k` be the central idempotents of Section 0. If `rk(e_j) > 0`,
   then `M -> rk(M)/rk(e_j)` on matrices over `e_j F[E_3] = A_j(F)` is a Sylvester matrix rank function.
   Every axiom is inherited, because products, sums and block matrices over the corner are computed in
   `F[E_3]`.
2. **The twisted corners have rank zero.**
   - A rank function on `A_j(F)` gives the rank condition (Remark 2.3).
   - By Theorem 3.1(c), `A_1(F_0)` fails the rank condition. The failure persists in `A_1(F)` along the
     unital inclusion `A_1(F_0) ⊂ A_1(F)`, and in `A_2(F)` through the antipode of Step 2.
   - So `rk(e_1) = rk(e_2) = 0`.
3. **The complement has rank zero.** `rk(1 - e_0) <= rk(e_1) + rk(e_2) = 0`.
4. **Conclude.** For any `n x n` matrix `M`, `rk(M) <= rk(M e_0) + rk(M(1 - e_0)) <= rk(M e_0) + 0`, and
   `rk(M e_0) <= rk(M)`. Also `z - 1 = (z - 1)(1 - e_0)`. ∎

Contrapositive: a Sylvester matrix rank function on `F[E_3]` with `rk(z - 1) > 0` refutes the target at
`p`. This recovers the 2026-09-12 artifact's Corollary 2.5 without any approximation. By Theorem 3.1(e)
the same holds for every homomorphism `F[E_3] -> R` into a nonzero weakly finite ring, since such a map
must kill `z - 1`.

**4.3 Group-level consequences.**
- `E_3` is not `F_p`-linear sofic, as already on main via `non-linear-sofic-via-deligne-twisted-algebra-failure`.
- More strongly, no homomorphism of `E_3` into the units of a weakly finite ring of characteristic `p`
  separates `z`. Examples:
  - `GL_n` of Ore domains or of division rings;
  - rank ultraproducts `Π_U M_(n_i)(F_p)/ker rk_U`;
  - unit groups of stably finite group algebras `F_p[Lambda]`, for example any `F_p`-linear sofic `Lambda`.
- In particular `E_3` admits no homomorphism to an `F_p`-linear sofic group `Lambda` that is injective on
  `<z>`. The composite with `Lambda -> F_p[Lambda]^x` would separate `z`, and `F_p[Lambda]` is stably
  finite by `linear-sofic-group-algebra-is-stably-finite`.
- Sofic groups are stably finite over every field (Elek–Szabó 2004; not re-fetched here), so the same
  applies to sofic `Lambda`.
- This is consistent with the payoff "not sofic" of the target and slightly sharper: it forbids sofic
  *quotients* detecting `z`, not only sofic approximations of `E_3`.

## 5. Where positive-side candidates die

By Theorem 3.1 the positive side (refuting the target at `p`) needs exactly one weakly finite image of
`A_j`. This section records which families of images cannot exist, unconditionally, and which remain.
Throughout, `K` is any field of characteristic `p != 3` containing `w`.

**Proposition 5.1 (no PI images).** `A_j(K)` has no nonzero homomorphic image satisfying a polynomial
identity. This includes commutative rings, finite-dimensional algebras and `M_d` over fields.

*Proof.*
1. Let `psi : A_j(K) -> R != 0` with `R` PI, and `P` a maximal ideal of `R`, which is prime.
2. By Posner's theorem (with Formanek–Rowen; classical, not re-fetched), the prime PI ring `R/P` has a
   classical ring of quotients `Q` that is central simple and finite-dimensional over its centre `Z`.
3. For a splitting field `L ⊇ Z`, `Q ⊗_Z L ≅ M_d(L)`. The composite
   `rho : E_3 -> A_j(K)^x -> GL_d(L)` has `rho(z) = w^j·1 != 1`, since `K -> L` is a unital map of fields.
4. `rho(E_3)` is a finitely generated linear group, hence residually finite
   (`finitely-generated-linear-groups-are-residually-finite`). So `rho(z) != 1` survives in a finite
   quotient of `E_3`.
5. That contradicts `deligne-triple-cover-finite-residual-is-center`. ∎

This strengthens Lemma 1.1 of the 2026-09-12 artifact, which excludes finite-dimensional modules.

**Proposition 5.2 (no exact matricial limits).**
- **Claim.** `A_j(K)` has no nonzero homomorphism into any product `Π_i M_(n_i)(K_i)`, any algebraic
  ultraproduct `Π_U M_(n_i)(K_i)`, or `Π_i M_(n_i)(K_i) / ⊕_i M_(n_i)(K_i)`. Here the `K_i` are fields of
  characteristic `p`, and there is no rank quotient.
- **Input.** `Sp_4(Z)` is finitely presented (Behr; standard, not re-fetched), so `E_3`, a central
  extension by `C_3`, is finitely presented.
- **Proof.**
  1. A homomorphism `E_3 -> Π_U GL_(n_i)(K_i)` with `z -> w^j` can be represented on generators by
     coordinates that are invertible for `U`-most `i`.
  2. Finitely many relators and the relation `rho(z)^2 + rho(z) + 1 = 0` (the image of `w^(2j) + w^j + 1 = 0`)
     then hold in `U`-most coordinates (cofinitely many for `Π/⊕`). A nonzero ultraproduct has `n_i >= 1`
     for `U`-most `i`. For a plain product, a nonzero homomorphism has a nonzero coordinate, which is a PI
     image, excluded by Proposition 5.1.
  3. This gives representations `rho_i : E_3 -> GL_(n_i)(K_i)` with `rho_i(z)^2 + rho_i(z) + 1 = 0`, so
     `rho_i(z) != 1` because `3 != 0` in `K_i`. Steps 4–5 of the proof of Proposition 5.1 (Malcev and the
     finite residual) exclude them.
- **What survives.** Only the *rank-metric* quotient of an ultraproduct survives. That is the linear
  soficity route of the 2026-09-12 artifact, Theorem 2.1.

**5.3 Artinian and Noetherian images: reduction, open.**
- **Noetherian images reduce to division rings.** A nonzero right Noetherian image `R` of `A_j(K)` has a
  prime quotient with a classical right quotient ring `M_d(D)`, `D` a division ring (Goldie; classical, not
  re-fetched). `M_d(D)` is weakly finite, and the image of `K` is central in it. So a Noetherian image
  yields a homomorphism `rho : E_3 -> GL_d(D)` over a division ring of characteristic `p` with
  `rho(z) = w^j`.
- **Conversely.** Any `rho : E_3 -> GL_d(D)` with `D` a division ring of characteristic `p` and
  `rho(z) != 1` refutes the target at `p` by Theorem 3.1(e), whether or not its image ring is Noetherian.
- **Known cases.**
  - Commutative `D` is dead by Malcev, as in Proposition 5.1.
  - If `D` is finite-dimensional over its centre `Z`, then `D ⊗_Z L ≅ M_m(L)` for a splitting field `L`.
    So `rho` becomes a representation over a field with `rho(z) != 1`, and that case is dead too.
- **Open case.** `D` infinite-dimensional over its centre. Finitely generated groups linear over such
  division rings need not be residually finite. For example, torsion-free one-relator groups such as
  `BS(2,3)` have group algebras embedding in division rings (Lewin–Lewin 1978; not re-fetched). So Malcev
  does not apply, and no construction is known here.

**Proposition 5.4 (finite subgroups give no obstruction).** Every finite subgroup `H~ <= E_3` containing
`z` has a homomorphism `lambda : H~ -> L^x` with `lambda(z) = w`, for some finite extension `L` of `K`. So obstructions supported on finite subgroups
cannot force `rho(z) = 1`. Examples:
- Herstein's theorem that finite subgroups of `D^x` are cyclic in characteristic `p`;
- character or commutator arguments on torsion.

*Proof.*
1. **Integrality.** `E_3` is the preimage of `Sp_4(Z)` in the connected triple cover of `Sp_4(R)`
   (`research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md`). So `E_3 = Sp~/3Z`, where
   `1 -> Z -> Sp~ -> Sp_4(Z) -> 1` is the preimage in the universal cover.
2. **The finite preimage.** Enlarge `H~` to the full preimage of the finite group `H = image(H~) <= Sp_4(Z)`.
   Since `H^i(H; Q) = 0` for `i >= 1`, the Bockstein gives `H^2(H; Z) ≅ Hom(H, Q/Z)`.
3. **The pullback model.** The restricted class is `delta(chi)` for a character `chi`. So the preimage of
   `H` in `Sp~` is the pullback `P = {(h, q) in H x Q : chi(h) = q + Z}`, with `Z = {(1, m)}`, and `H~ = P/3Z`.
4. **The character.** `(h, q) -> q/3 + Z` is a well-defined homomorphism `H~ -> Q/Z` sending
   `z = (1, 1) -> 1/3`.
5. **Into `K^x`.** Project its finite cyclic image to the 3-primary part, which still contains the image
   of `1/3`, and embed that cyclic 3-group into `\bar{F_p}^x`, which is possible as `p != 3`. The values lie
   in a finite extension of `K`, and one chooses the embedding with `1/3 -> w`.

Replacing `K` by that finite extension changes nothing. The restricted class is in the Ext part, so `z` is
never a product of commutators in a finite subgroup. ∎

**5.5 Central deformations: nothing gained.**
- Put `E_m = Sp~/mZ` and `A^(lambda) = F[Sp~]/(c - lambda)` for the central generator `c` and `lambda` of
  order `m`.
- Deligne's theorem puts `2Z` in the finite residual of `Sp~`. So `E_m` can be residually finite only for
  `m | 2`: otherwise the image of `2Z` in `Z/mZ` is a nontrivial part of the finite residual of `E_m`.
  For `m = 3` the twisted factors are exactly the `A_j`, so the deformation just returns to the target.
- No specialization map transports stable finiteness from `lambda = ±1` to `lambda = w`. Weak finiteness
  is not an open condition in a parameter, and `F[Sp~]` itself is not covered: `Sp~` is finitely presented
  and not residually finite, hence not LEF.

**5.6 What remains on the positive side.** By Theorem 3.1, the complete list of positive mechanisms is:
- a weakly finite image of `A_j` (equivalently a weakly finite representation of `E_3` separating `z`) that
  is not PI and not an exact matricial limit;
- concretely: a rank-metric model (linear soficity, as on main), a division-ring representation (5.3), or
  a stably finite ring built by other means, e.g. crossed products or Ore localizations.

None is available.

## 6. Literature and novelty (checked 2026-09-16)

**Fetched 2026-09-16 (abstract pages).**
- **arXiv:2410.02913.** M. Chapman, Y. Dikstein, A. Lubotzky, *Conditional non-soficity of p-adic Deligne
  extensions: on a theorem of Gohla and Thom* (v1 Oct 3 2024, v2 Dec 16 2024).
  - It gives an alternative proof that stability of arithmetic lattices of `Sp(2g, Q_p)` implies
    non-soficity of their Deligne central extensions (Gohla–Thom).
  - It does not address linear soficity, stable finiteness, twisted group algebras, or `Sp_4(Z)` and its
    triple cover.
- **arXiv:2505.21030.** K. Lorensen, J. Öinert, *The rank condition and strong rank conditions for Ore
  extensions* (v1 May 27 2025, v3 Mar 24 2026).
  - Ore extensions and skew power series only. Nothing on twisted group rings, crossed products, or LEF or
    sofic groups.
  - It credits Malcolmson with "rank condition iff a nonzero stably finite quotient". That quote is already
    recorded on main in `rank-condition-rings-have-weakly-finite-images`.
- **arXiv:2608.06222.** G. Kun, A. Thom, *Nonsofic wreath products of residually finite groups* (Aug 6 2026,
  v3 Aug 20 2026). It concerns soficity of generalized wreath products and doubles under property (T)
  hypotheses. Nothing on Deligne extensions, linear soficity, stable finiteness or twisted algebras.
- **X. K. Phung, CJM 76(4) (2024), 1089–1108.** *Stable finiteness of twisted group rings and noisy linear
  cellular automata.* Its "twisted group ring" `D^1(k[G]) = k[G] x (k[G])[G]` carries a special
  multiplication and is not a cocycle-twisted group algebra. Its theorems (residually finite and initially
  subamenable groups are L^1-surjunctive) do not bear on `F^alpha[Gamma]` with a non-inflated multiplier.
- **Blog, 2026-09-11.** A. Thom, guest post on T. Tao's blog, "On the existence of non-sofic groups".
  - It reports the August 2026 construction of a non-sofic group, which relies on Kun–Thom centralizer
    rigidity, and points to arXiv:2608.06222.
  - It does not mention Deligne extensions, non-linear-soficity or Kaplansky finiteness.

**Seen in search listings only (not fetched).** arXiv:2608.02025, F. Fournier-Facio, *A torsion-free
non-sofic group* (dated Aug 17 2026 in the listing). The contents were not checked.

**Cited, not re-fetched here.**
- P. Malcolmson, *On making rings weakly finite*, Proc. Amer. Math. Soc. 80 (1980), 215–218. It is quoted via
  arXiv:2505.21030 and arXiv:2201.01432 (Hung–Li) on main, and the local proof on main is used instead.
- Classical results used only in Section 5 and Remark 2.3:
  - Posner's theorem with Formanek–Rowen;
  - Goldie's theorem;
  - Behr's finite presentation of `Sp_4(Z)`;
  - Elek–Szabó (2004), sofic groups are stably finite;
  - Hazrat's strong-grading criterion for Leavitt path algebras;
  - Lewin–Lewin (1978), group algebras of torsion-free one-relator groups embed in division rings;
  - Deligne (1978), the finite residual of the universal symplectic extension.

**Novelty assessment.**
- Searches on 2026-09-16 found no source stating Proposition 1.2 or Theorem 2.1:
  - "stably finite" together with "twisted group ring" and "residually finite";
  - "rank condition" together with "crossed product" and "LEF";
  - Kaplansky direct finiteness for cocycle-twisted group algebras.
- The absorption map is a standard coaction trick, so the result is probably folklore but was not located.
- No 2024–2026 source decides the target, and none treats weakly finite representations of `E_3`.
