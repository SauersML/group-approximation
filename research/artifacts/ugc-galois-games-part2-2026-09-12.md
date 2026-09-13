# Galois unique games, part 2: free-subgroup rounding over every finite group

Date: 2026-09-12. Lane `ex-ugc`. Continues
`research/artifacts/ugc-galois-games-2026-09-12.md` (notation `Gal(G,K,mu)`,
`Phi_mu`, (3.1)). Status: complete proofs of Theorems 7--8 and Corollary 9.
Section 4 is an open question with tests. **No bearing on the truth of UGC is
claimed.**

## 1. Theorem 8: free-subgroup rounding and the duality

**Theorem 8.** Let `G` be finite, `K <= G`, and `mu` a symmetric probability
measure. For every subgroup `H <= G`, the following are equivalent:

* (a) `H` acts freely on `G/K`;
* (b) `K` acts freely on `G/H`;
* (c) `H cap x K x^-1 = {e}` for every `x in G`.

For every such `H`,

```text
val Gal(G,K,mu)  >=  1 - mu(G \ H).                                          (8.1)
```

*Proof.* The stabilizer of `xK` in `H` is `H cap x K x^-1`, and the stabilizer
of `yH` in `K` is `K cap y H y^-1 = y (y^-1 K y cap H) y^-1`. So (a) and (b)
both say (c).

For (8.1), put `Y(g) = g^-1 H in G/H`, and let `D subset G/H` be a set of
representatives of the `K`-orbits on `G/H` under left multiplication. Put
`T = { g : Y(g) in D }`. For a coset `gK`, `Y(g a) = a^-1 Y(g)`. As `a` runs over
`K`, this runs once over the `K`-orbit of `Y(g)`, by freeness (b). That orbit
meets `D` exactly once, so `T` is a left transversal. If `s in H`, then
`Y(s t) = t^-1 s^-1 H = Y(t)`, so `s t in T` whenever `t in T`. Hence
`Phi_mu(T) <= Pr_(s~mu)[s notin H]`, and Theorem 1 gives (8.1). `square`

Theorem 2, "perfect iff `<supp mu>` acts freely on `G/K`", is the case
`mu(G \ H) = 0`. Theorem 4's subgroup complement is the case `H = ker Y`.
Section 2 shows that every rounding in these notes is of this form.

## 2. Theorem 7: irreducible-kernel rounding over every finite group

**Theorem 7.** Let `G` be finite of exponent `m`, `K <= G` of order `k`, and `mu`
symmetric and conjugation-invariant. Suppose `phi` is admissible in (3.1) with
`sum_g mu(g) phi(g) >= 1 - epsilon`, for instance from `SDP >= 1 - epsilon`.
Then there are irreducible representations `rho_1, ..., rho_t` of `G` with the
following properties:

* `t <= log_2 k`;
* `lambda_(rho_i) = chi_(rho_i)(mu)/d_(rho_i) >= 1 - 3 epsilon`;
* `K cap ker rho_1 cap ... cap ker rho_t = {e}`.

For `H = ker(rho_1 + ... + rho_t)`,

```text
val Gal(G,K,mu) >= 1 - mu(G \ H) >= 1 - (3 epsilon/(1 - cos(2 pi/m))) (d_(rho_1) + ... + d_(rho_t))
                >= 1 - (3 m^2/8) epsilon (d_(rho_1) + ... + d_(rho_t)).                     (7.1)
```

*Proof.* (i) **Isotypic splitting.** By GNS, `phi(g) = <pi(g) xi, xi>` with
`pi` unitary and `|xi| = 1`. Split `xi = sum_rho xi_rho` into isotypic components
and put `w_rho = |xi_rho|^2`, so `sum w_rho = 1` and
`phi(g) = sum_rho <pi(g) xi_rho, xi_rho>`. Since `mu` is a class function,
`pi(mu)` acts on the `rho`-isotypic component as the scalar `lambda_rho`, which
is real and at most `1` (Schur). So
`sum_rho w_rho (1 - lambda_rho) = 1 - sum mu phi <= epsilon`.

(ii) **The good kernels meet `K` trivially.** Put `B = { rho : lambda_rho < 1 - 3 epsilon }`,
so `w(B) <= 1/3`. Let `calG = { rho notin B : w_rho > 0 }` and
`N = K cap intersection_(rho in calG) ker rho`. For `a in N`, each `rho in calG`
contributes exactly `w_rho` to `phi(a)`, and each `rho in B` contributes a
number of modulus at most `w_rho`. So `Re phi(a) >= w(calG) - w(B) >= 1/3 > 0`.
Admissibility forces `phi = 0` on `K \ {e}`, so `N = {e}`. (If `epsilon = 0`,
then `w(B) = 0` and the same argument applies.)

(iii) **Few representations suffice.** Starting from `N_0 = K`, pick
`rho_i in calG` with `N_i = N_(i-1) cap ker rho_i` properly smaller than
`N_(i-1)`. Such a `rho_i` exists while `N_(i-1) != {e}`, by (ii). Each step at
least halves the order, so `t <= log_2 k`.

(iv) **The subgroup.** `H = ker(rho_1 + ... + rho_t)` is normal with
`H cap K = {e}`. A normal subgroup meets every conjugate of `K` the way it
meets `K`, so Theorem 8 applies, and
`mu(G \ H) <= sum_i Pr_mu[rho_i(s) != I]`.

(v) **Markov in Hilbert--Schmidt norm.** If `rho(g) != I`, then `rho(g)` has an
eigenvalue that is a nontrivial `m`-th root of unity. So
`|rho(g) - I|_HS^2 >= 2(1 - cos(2 pi/m))`. On the other hand,
`E_mu |rho(s) - I|_HS^2 = 2 d_rho - 2 Re chi_rho(mu) = 2 d_rho (1 - lambda_rho) <= 6 epsilon d_rho`.
Markov gives `Pr[rho(s) != I] <= 3 epsilon d_rho/(1 - cos(2 pi/m))`. Finally,
`1 - cos x >= 2 x^2/pi^2` on `[0, pi]`. `square`

**Corollary 9 (every finite abelian group).** If `G` is abelian of exponent `m`,
all `d_rho = 1`, and

```text
SDP Gal(G,K,mu) >= 1 - epsilon   ==>   val >= 1 - 3 epsilon log_2 k/(1 - cos(2 pi/m)).
```

For `m = 2` this is `1 - (3/2) epsilon log_2 k`, recovering Theorem 4 with a
proof that needs neither Bochner nor Fourier inversion. Proposition 5
(`Z_(2n)`, the odd cycle) shows that some growth in `m` is necessary. There
`1 - val >= (2/pi) sqrt(epsilon)` while `m = 2n`, and Corollary 9's bound reads
`O(n^2 epsilon) = O(1)`: consistent, but not tight.

## 3. What these results say

* Every labeling found here is a **free-subgroup transversal**: pick `H`
  acting freely on `G/K`, then choose one `K`-orbit representative in `G/H`.
  Its cost is the `mu`-mass outside `H`, independent of `D`.
* An SDP certificate supplies such an `H` cheaply exactly when the
  representations carrying the certificate are **low-dimensional**, or more
  precisely when the elements that almost fix the certificate vector lie in
  a subgroup. This holds for abelian groups (Corollary 9). It fails for the
  standard representation of `S_N` (`d = N - 1`), where transposition noise has
  `lambda = 1 - O(epsilon)` but `rho(s) != I` for almost every `s`. There a
  different free subgroup, a point stabilizer, works; see Section 4.

## 4. Open: is free-subgroup rounding universal at bounded exponent?

**Question.** Is there `C(m)` such that for every finite group `G` of exponent
`m`, every `K`, and every symmetric conjugation-invariant `mu`, `SDP >= 1 - epsilon`
implies some `H` acting freely on `G/K` has `mu(G \ H) <= C(m) epsilon log k`?

Tests.

1. **Abelian:** yes (Corollary 9).
2. **Extraspecial 2-groups** `2^(1+2n)` with `K = Z(G)` (`k = 2`): (3.1) forces
   weight `1/2` on the `2^n`-dimensional irreducible, whose `lambda` is
   `mu(e) - mu(z)`. So `SDP >= 1 - epsilon` forces `mu(e) >= 1 - 2 epsilon`,
   and `H = {e}` works. No gap.
3. **`S_N` (unbounded exponent)**, transposition noise, `K` semiregular on
   `[N]`: the certificate from the standard representation has
   `lambda = 1 - O(epsilon)`. Theorem 7 is vacuous (`d = N - 1`), but
   `H = Stab(1)` acts freely on `G/K` iff `K` is semiregular, and
   `mu(G \ H) = Pr[s(1) != 1] = O(epsilon)`. The right `H` is not a kernel.
4. **Where the argument dies.** One would need a stability statement: a
   vector almost fixed by `mu`-most elements, with orthonormal `K`-translates,
   yields a subgroup carrying `mu`-most mass that meets no conjugate of `K`.
   No such statement is supplied for large irreducibles of bounded-exponent
   groups. A counterexample would be a bounded-exponent group whose SDP-optimal
   certificates live in large representations while no free subgroup carries
   most of `mu`.
