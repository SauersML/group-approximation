# The congruence norm splits into a vector sector and a Gelfand--Graev sector (2026-09-16)

Supports `cubic-division-congruence-norm-splits-into-two-sectors`.  Written by the swarm agent
`swarm-cubic-division-congruence-repr`, unreviewed.  Experiments:
`experiments/cubic-division-gelfand-graev-2026-09-16/`.

## 0. Notation

- `p` is a prime, `F = F_p`, `G = SL_3(F)`, `G~ = GL_3(F)`, `U` the upper unitriangular group,
  `T` the diagonal torus of `G`, `B = TU`.
- `psi` is a fixed nontrivial additive character of `F`.  For `s, r in F^x` put
  `psi_(s,r)(u) = psi(s u_12 + r u_23)`, a character of `U`.  Put `kappa = kappa_p = gcd(3, p - 1)`,
  fix representatives `a` of `F^x / F^x3` and write `psi_a = psi_(1,a)`.
- **Vector sector.**  `sigma_p = l^2(F^3 minus 0)` with the linear action, and `sigma_p^0 = sigma_p minus constants`.
  `G` acts transitively on `F^3 minus 0` with stabiliser `Q = Stab_G(e_1)`, so `sigma_p = Ind_Q^G 1`.
- **Gelfand--Graev sector.**  `GG_(a,p) = Ind_U^G psi_a` and `GG_p = sum_a GG_(a,p)`, of dimension
  `d_p = kappa (p^2 - 1)(p^3 - 1) <= 3 p^5`.
- `pi_p = l^2_0(G)`.  For `D`, `Gamma_D` and `P_D` as in
  `cubic-division-congruence-representations-converge-strongly`, every representation of `G` is pulled back
  to `Gamma_D` along the reduction map, which is onto for `p` not in `P_D`.

**Imports** (not re-read in this session).
- (GG1) Gelfand--Graev: `Ind_U^(G~) psi_(1,1)` is multiplicity free (its Hecke algebra is commutative).
  Standard, going back to Gelfand--Graev (1962) and Steinberg; no theorem number is claimed.
- Elementary facts used without comment: Mackey's formula for `Hom(Ind, Ind)` and for restriction of an
  induced representation; the norm of `rho(z)` for a finite group is the maximum over the irreducible
  constituents of `rho`.

## 1. The vector sector has no generic constituent

**Lemma 1.**  For every `a`, `Hom_G(GG_(a,p), sigma_p) = 0`.  The same holds for `G~`:
`Hom_(G~)(Ind_U^(G~) psi_(s,r), l^2(F^3 minus 0)) = 0`.

*Proof.*  By Mackey, `Hom_G(Ind_U psi_a, Ind_Q 1)` is the space of `f : G -> C` with
`f(u g q) = psi_a(u) f(g)`.  Such an `f` can be nonzero on `U g Q` only if `psi_a` is trivial on
`U cap g Q g^-1 = U cap Stab(v)`, where `v = g e_1`.  Now `u v = (v_1 + u_12 v_2 + u_13 v_3, v_2 + u_23 v_3, v_3)`.
- If `v_3 != 0`, `U cap Stab(v)` contains every `u` with `u_23 = 0`, `u_12 = c` and `u_13 = -c v_2 / v_3`.
  On these, `psi_a(u) = psi(c)`, which is nontrivial.
- If `v_3 = 0` and `v_2 != 0`, it contains every `u` with `u_12 = 0` and `u_23 = c`.  On these
  `psi_a(u) = psi(a c)`, which is nontrivial.
- If `v_2 = v_3 = 0`, it is all of `U`.

So every double coset is killed, and `f = 0`.  The computation for `G~` is identical.  QED

Both representations are semisimple, so they have no common irreducible constituent.

## 2. Every nontrivial irreducible representation of `G` lies in one of the two sectors

### 2A. Vector-type representations of `GL_3`

Let `P~ = Stab_(G~)(F e_1)`, with elements `[[alpha, *], [0, h]]`, `alpha in F^x`, `h in GL_2(F)`.  Then
`Q~ = Stab_(G~)(e_1)` is the kernel of `P~ -> F^x`, `x -> alpha`.  So

```text
l^2(F^3 minus 0) = Ind_(Q~)^(G~) 1 = sum over characters chi of F^x of  W_(chi,1),
W_(chi,mu) := Ind_(P~)^(G~) (chi (x) mu o det_2),     (chi (x) mu o det_2)(x) = chi(alpha) mu(det h).
```

Since `(mu o det)(x) = mu(alpha) mu(det h)` on `P~`, we get `W_(chi,mu) = (mu o det) (x) W_(chi mu^-1, 1)`.  So the
constituents of all det-twists of `l^2(F^3 minus 0)` are exactly the constituents of all `W_(chi,mu)`.

**Mackey.**  `P~` has two orbits on lines, so `P~ \ G~ / P~` has representatives `1` and `s`, the
permutation matrix exchanging `e_1` and `e_2`.  Every double coset contributes at most one dimension to
`Hom(W_(chi1,mu1), W_(chi2,mu2))`.
- The coset of `1` contributes iff `(chi1, mu1) = (chi2, mu2)`.
- The coset of `s` contributes iff the two characters agree on `P~ cap s P~ s^-1`, after conjugating
  one of them by `s`.  This group contains the diagonal torus.  At `x = diag(alpha, beta, gamma)` the
  condition reads `chi1(alpha) mu1(beta gamma) = chi2(beta) mu2(alpha gamma)`.  Taking one variable at a
  time gives `chi1 = mu2`, `chi2 = mu1` and `mu1 = mu2`, so all four characters are equal.
  Conversely, if all four equal `chi`, both characters are `chi o det`, and the condition holds.

Consequences:
1. If `chi != mu`, then `End(W_(chi,mu)) = C`, so `W_(chi,mu)` is irreducible of dimension `p^2 + p + 1`.
   Also `W_(chi1,mu1) = W_(chi2,mu2)` iff the pairs are equal.  This gives `(p-1)(p-2)` distinct irreducibles.
2. `W_(mu,mu) = (mu o det) (x) l^2(P^2(F))` has a 2-dimensional endomorphism algebra.  So it is the sum
   of two non-isomorphic irreducibles, `mu o det` and `(mu o det) (x) rho_1` with `rho_1 = l^2_0(P^2(F))`.
   For `mu != nu`, `Hom(W_(mu,mu), W_(nu,nu)) = 0`, so these `2(p-1)` irreducibles are distinct.  Their
   dimensions are `1` and `p^2 + p`, so they also differ from those in 1.

So the det-twists of `l^2(F^3 minus 0)` contain exactly `p(p-1)` distinct irreducibles of `G~`.  By Lemma 1,
none of them is a constituent of `Ind_U^(G~) psi_(1,1)`.  Here we also use that `(mu o det) (x) Ind_U psi = Ind_U psi`,
because `mu o det` is trivial on `U`.

### 2B. The number of generic representations of `GL_3`

Put `GG~ = Ind_U^(G~) psi_(1,1)`.  By Mackey, `dim End(GG~)` is the number of double cosets `U g U` such that
`psi(x) = psi(g^-1 x g)` for all `x in U cap g U g^-1`.

By Bruhat, the double cosets have unique representatives `g = w t`, where `w` is a permutation matrix
(`w e_j = e_(pi(j))`) and `t` lies in the diagonal torus of `G~`.
- `U cap g U g^-1` is the product of the root groups `U_(ij)` (`i < j`) with `pi^-1(i) < pi^-1(j)`.
- On it, `g^-1 (1 + c E_ij) g = 1 + c (t_l / t_k) E_(kl)`, where `(k, l) = (pi^-1(i), pi^-1(j))`.
- `psi_(1,1)` is nontrivial on `U_12` and `U_23` and trivial on `U_13`.

So the condition fails if some root group in the intersection has exactly one of `(i,j)` and `(k,l)` simple.
When both are simple, it reads `t_k = t_l`.  Running through `S_3`:

| `pi` | root groups in `U cap wUw^-1` and their images | condition on `t` | cosets |
|---|---|---|---|
| `1` | `12 -> 12`, `23 -> 23`, `13 -> 13` | `t` central | `p - 1` |
| `(12)` | `23 -> 13`, `13 -> 23` | fails | 0 |
| `(23)` | `12 -> 13`, `13 -> 12` | fails | 0 |
| `(123)` | `23 -> 12` | `t_1 = t_2` | `(p-1)^2` |
| `(132)` | `12 -> 23` | `t_2 = t_3` | `(p-1)^2` |
| `(13)` | none | none | `(p-1)^3` |

Hence `dim End(GG~) = (p-1) + 2(p-1)^2 + (p-1)^3 = p^3 - p^2`.  By (GG1), `GG~` is multiplicity free, so it
has exactly `p^3 - p^2` distinct irreducible constituents: the generic representations.

### 2C. Exhaustion for `GL_3`

`G~` has `p^3 - p` conjugacy classes.  This is elementary, via rational canonical forms.  The possible
characteristic-polynomial types, with the number of classes of each, are:
- three distinct roots in `F`: `C(p-1, 3)` classes;
- a double root and a simple root: `2 (p-1)(p-2)` classes;
- a triple root: `3 (p-1)` classes;
- a root times an irreducible quadratic: `(p-1)(p^2-p)/2` classes;
- an irreducible cubic: `(p^3-p)/3` classes.

These sum to `p^3 - p`.  So there are `p^3 - p` irreducibles.  By 2A and 2B there are `p^3 - p^2` generic ones
and `p^2 - p` vector-type ones, and the two sets are disjoint.

**Proposition 2.**  Every irreducible representation of `GL_3(F_p)` is a constituent of `Ind_U psi_(1,1)` or
of `(mu o det) (x) l^2(F^3 minus 0)` for some `mu`, and not both.

*Cross-check.*  Steinberg's degree list for `GL_3(F_q)` (import, not re-read) is consistent with these
counts.  `experiments/cubic-division-gelfand-graev-2026-09-16/gl3_degree_check.py` checks, for 21 values of `q`:
- the class number;
- the sum of squared degrees;
- `p^3 - p^2` generic families, whose degrees sum to `|G~ / U|`;
- `p^2 - p` non-generic families.

### 2D. Restriction to `SL_3`

Let `rho'` be an irreducible representation of `G`.  By Frobenius reciprocity, `rho'` is a constituent of
`Res_G rho` for some irreducible `rho` of `G~`.
- **Vector type.**  Suppose `rho` lies in `(mu o det) (x) l^2(F^3 minus 0)`.  The twist is trivial on `G`, and
  `G` is transitive on `F^3 minus 0` with stabiliser `Q`.  So `Res_G` of this representation is `sigma_p`, and
  `rho'` lies in `sigma_p`.
- **Generic.**  Suppose `rho` lies in `GG~`.  `G` is normal and `U <= G`, so `G \ G~ / U = G~ / G = F^x`, with
  representatives `d_t = diag(t, 1, 1)`.  Mackey gives
  `Res_G GG~ = sum over t in F^x of Ind_U^G psi_(t^-1, 1)`.
  - For `x = diag(alpha, beta, gamma) in T`, conjugation by `x` normalises `U` and gives
    `Ind_U^G psi_(s,r) = Ind_U^G psi_(s beta/alpha, r gamma/beta)`.
  - The map `x -> (beta/alpha, gamma/beta)` has image `{(lambda, mu) : lambda/mu in F^x3}`.  Indeed
    `lambda/mu = beta^2/(alpha gamma) = beta^3`, and conversely `alpha = beta/lambda`, `gamma = mu beta` works.
  - Hence `Ind_U^G psi_(s,r)` depends only on the class of `r/s` in `F^x / F^x3`, and equals `GG_(a,p)` for `a == r/s`.

  So `Res_G GG~` is a sum of copies of the `GG_(a,p)`, and `rho'` lies in `GG_p`.

The trivial representation has multiplicity one in `sigma_p`, and by Lemma 1 it does not occur in `GG_p`.

**Proposition 3.**  Every irreducible representation of `SL_3(F_p)` is a constituent of exactly one of
`sigma_p` and `GG_p`.  Every nontrivial one is a constituent of exactly one of `sigma_p^0` and `GG_p`.

## 3. The norm identity and the equivalence

**Theorem 4.**  For `p` not in `P_D` and `z in C[Gamma_D]`,

```text
||pi_p(z)|| = max( ||sigma_p^0(z)||, ||GG_p(z)|| ),        ||GG_p(z)|| = max over a of ||GG_(a,p)(z)||.
```

*Proof.*  Reduction is onto, so the image of `z` in `C[G]` has the same norms.  `l^2(G)` contains every
irreducible representation of `G`, and `pi_p` contains exactly the nontrivial ones.  The norm of a
representation of a finite group at a group-ring element is the maximum over its irreducible
constituents.  Apply Proposition 3.  QED

**Corollary 5.**  Let `p -> infinity` over primes not in `P_D`.
1. For `w in Gamma_D minus {1}`, `chi_(sigma_p^0)(w) = -1` for all large `p`, and `chi_(GG_p)(w) = 0` for all large `p`.
2. Hence both sectors converge in distribution to `lambda_(Gamma_D)`, and
   `liminf ||sigma_p^0(z)|| >= ||lambda(z)||` and `liminf ||GG_p(z)|| >= ||lambda(z)||` for every `z`.
3. Therefore `pi_p -> lambda` strongly iff both `sigma_p^0 -> lambda` and `GG_p -> lambda` strongly.

*Proof.*
1. `chi_(sigma_p^0)(w) = #Fix_(F^3 minus 0)(w mod p) - 1 = p^(d_1) - 2`, with `d_1 = dim ker(w - 1 mod p)`.
   Here `d_1 >= 1` iff `p` divides `Delta(w) = det(1 - w)`, which is a nonzero integer
   (`cubic-division-ihara-traces-count-roots-mod-p`, parts 1 and 3).

   The character of an induced representation from `U` vanishes off the conjugates of `U`, that is, off
   the unipotent elements.  `w mod p` has characteristic polynomial `f_w mod p`, by the "Reduction"
   paragraph of the proof of that node.  So `w mod p` is unipotent iff `p` divides both `Trd(w) - 3` and
   `Trd(w^-1) - 3`.  Since `f_w` is irreducible over `Q` (part 1 there), `f_w != (x - 1)^3`, and one of
   these integers is nonzero.
2. The normalised traces converge to the canonical trace `tau` on every group element.  For `x = z*z`,
   `||rho(x)||^m >= tr_rho(x^m) -> tau(x^m)`.  Since `tau` is faithful on `C*_lambda(Gamma_D)`,
   `sup_m tau(x^m)^(1/m) = ||lambda(x)||`.
3. The reverse implication is Theorem 4.  The forward one follows from
   `||sigma_p^0(z)||, ||GG_p(z)|| <= ||pi_p(z)||` together with 2.  QED

So the target splits into two independent no-outlier problems.
- The **vector sector** is a permutation representation: the Schreier graphs of `Gamma_D` on nonzero
  vectors mod `p`.
- The **Gelfand--Graev sector** carries every generic representation.  This includes the constituents of
  the Steinberg representation, the cuspidal representations and the irreducible principal series.  It
  is a monomial representation on `G/U`, which is modelled in Section 6.

## 4. The Gelfand--Graev character

Call `g in G` a **transvection** if `rank(g - 1) = 1`.  Then `g - 1 = v phi^T` with `1 = det g = 1 + phi(v)`,
so `(g - 1)^2 = 0` and `g` is unipotent.  Call `g` **regular unipotent** if it is unipotent with `rank(g - 1) = 2`.

**Proposition 6.**  For `g in G = SL_3(F_p)`,

```text
chi_(GG_p)(g) = kappa [ (p^2 - 1)(p^3 - 1) 1{g = 1}  -  (p^2 - 1) 1{g is a transvection}  +  1{g is regular unipotent} ].
```

The first two terms hold for each `GG_(a,p)` separately, with `kappa` removed.  The third holds only after
summing over `a`.

*Proof.*  `chi_(GG_(a,p))(g) = |U|^-1 sum over x in G with x^-1 g x in U of psi_a(x^-1 g x)`.  This vanishes
unless `g` is unipotent.

- **`g = 1`.**  The value is `|G|/|U| = (p^2 - 1)(p^3 - 1)`.
- **Transvections.**  All transvections are conjugate in `G`.  Write `g = 1 + v phi^T` in a basis
  `e_1 = v`, `e_2 in ker phi`, `e_3` with `phi(e_3) = 1`.  Rescaling `e_2` makes the change of basis
  determinant 1 and does not change the matrix `1 + E_13`.

  The centraliser of `1 + E_13` consists of the matrices `[[l, a, b], [0, c, d], [0, 0, l]]` with
  `l^2 c = 1`, so it has order `p^3 (p - 1)`.  Hence
  `chi_a(g) = |C_G(g)| |U|^-1 sum over u in U cap C of psi_a(u)`, where `C` is the class of transvections.

  Now `U cap C = {1 + N : N` strictly upper triangular, `N != 0`, `N_12 N_23 = 0}`, and
  `psi_a(1 + N) = psi(N_12 + a N_23)`.  The sum splits into three parts:
  - `N_12 = N_23 = 0`, `N_13 != 0`: this gives `p - 1`;
  - `N_12 != 0`, `N_23 = 0`: this gives `p (-1)`;
  - `N_12 = 0`, `N_23 != 0`: this gives `p (-1)`.

  The total is `-(p + 1)`, so `chi_a(g) = (p - 1)(-(p + 1)) = -(p^2 - 1)`.
- **Regular unipotents.**  `N = g - 1` is a single nilpotent Jordan block, so the only `g`-stable flag is
  `ker N < ker N^2`.  Indeed, a stable line lies in `ker N`, and a stable plane `W` has `N^2 W = 0`.

  Now `x^-1 g x in U` iff `g` stabilises the flag `x F_0`, where `F_0` is the standard flag.  So the set
  of such `x` is one coset `x_0 B`.  Writing `x = x_0 t u'` and using that `psi_a` is a character of `U`,
  `chi_a(g) = sum over t in T of psi_a(t^-1 u_0 t)`, with `u_0 = x_0^-1 g x_0 in U`, `(u_0)_12 = s != 0` and
  `(u_0)_23 = r != 0`.

  For `t = diag(alpha, beta, gamma)`, `t^-1 u_0 t` has entries `lambda s` at `(1,2)` and `mu r` at `(2,3)`,
  with `(lambda, mu) = (beta/alpha, gamma/beta)`.  The map `t -> (lambda, mu)` is `kappa`-to-1 onto
  `{lambda/mu in F^x3}` (Section 2D).  So
  `chi_a(g) = kappa sum over lambda/mu in F^x3 of psi(lambda s + a mu r)`.

  As `a` runs over the representatives, `(lambda, a mu)` runs over `(F^x)^2` exactly once, since
  `lambda/(a mu) in a^-1 F^x3`.  So `sum_a chi_a(g) = kappa (sum over lambda != 0 of psi(lambda s))
  (sum over mu != 0 of psi(mu r)) = kappa`.  QED

**Checks.**
- *Orthogonality to constants.*  `SL_3(F_p)` has `p^6` unipotent elements (Steinberg; import).  There are
  `(p^3 - 1)(p + 1)` transvections, which is the class size `|G| / (p^3 (p - 1))`.  So there are
  `p^6 - 1 - (p^3 - 1)(p + 1)` regular unipotents, and

  ```text
  sum_g chi_(GG_p)(g) = kappa (p^3 - 1) [ (p^2 - 1) - (p^2 - 1)(p + 1) + (p^3 + 1) - (p + 1) ] = 0,
  ```

  as it must be, because `GG_p` has no trivial constituent.
- *Numerical check.*  See Section 6(i).

## 5. Ihara traces for a free pair

Let `A, B in Gamma_D` generate a free group `H`, and put `Z = A + A^-1 + B + B^-1`.  Let `p` lie outside
`P_D` and `P_H`, so that `H -> G` is onto.  Let `CR_n` be the set of cyclically reduced words of length `n`.
Put `T_GG(n) = sum over w in CR_n of chi_(GG_p)(w mod p)`, and define

```text
I_p(n)  = #{ w in CR_n : w == 1 mod p },
Tr_p(n) = #{ w in CR_n : rank(w - 1 mod p) = 1 },
R_p(n)  = #{ w in CR_n : Trd(w) == Trd(w^-1) == 3 mod p  and  rank(w - 1 mod p) = 2 }.
```

**Proposition 7.**
1. `T_GG(n) = kappa [ (p^2 - 1)(p^3 - 1) I_p(n) - (p^2 - 1) Tr_p(n) + R_p(n) ]`.
   - `w mod p` is unipotent iff `Trd(w) == Trd(w^-1) == 3 mod p`, because its characteristic polynomial is
     `f_w mod p` and `(x - 1)^3 = x^3 - 3x^2 + 3x - 1`.
   - `Tr_p(n) = U_p(n) - I_p(n)`, in the notation of `cubic-division-ihara-traces-count-roots-mod-p`.
2. **Ihara--Bass forms.**  Apply `free-group-ihara-bass-outlier-trace-criterion` with two generators, so
   `q = 3` and `E_GG(n) = T_GG(n) - d_p (1 + (-1)^n)`.
   - (a) If `limsup_p ||GG_p(Z)|| <= 2 sqrt 3`, then for every `delta > 0`, all large `p` and all `n`,
     `|T_GG(n) - d_p (1 + (-1)^n)| <= 2 d_p (sqrt 3 + delta)^n`.
   - (b) Conversely, suppose there are `C`, `delta_p -> 0` and even `n_p` with `n_p / log p -> infinity` such
     that `T_GG(n_p) - 2 d_p <= p^C (sqrt 3 + delta_p)^(n_p)`.  Then `limsup_p ||GG_p(Z)|| <= 2 sqrt 3`.

   These are 4(a) and 4(b) of the criterion.  In (b) we use `p <= d_p <= 3 p^5`, so `log d_p ~ 5 log p`
   and `p^C <= d_p^C`.
3. **Cancellation of main terms.**  Suppose the words of `CR_n` were exactly equidistributed in `G`.
   - `(p^2 - 1)(p^3 - 1) I_p(n)` would be `|CR_n| / p^3`.
   - `(p^2 - 1) Tr_p(n)` would be `|CR_n| (p + 1) / p^3`.
   - `R_p(n)` would be `|CR_n| / p^2`.

   These cancel exactly, by the orthogonality check of Section 4.  So (b) says: at lengths `n >> log p`,
   the signed count of cyclically reduced words that are unipotent mod `p`, weighted by the rank of
   `w - 1`, has fluctuations of size at most `p^C 3^(n/2)`, against main terms of size `3^n / p^2`.

*Proof.*  Part 1 is Proposition 6 evaluated at `w mod p`.  A rank-1 element `w - 1` of `SL_3` is
automatically a transvection (Section 4).  Part 2 is a direct substitution, with `k - 1 = 1` and
`dimension d_p`.  Part 3 uses `|G| = p^3 (p^2 - 1)(p^3 - 1)`, `(p^3 - 1)(p + 1)` transvections and
`p (p^2 - 1)(p^3 - 1)` regular unipotents.  QED

**Comparison with the vector sector.**  There the traces are
`(p - 1) N_p(n) + (p^2 - p) U_p(n) + (p^3 - p^2) I_p(n) - |CR_n|`
(part 3 of `cubic-division-ihara-traces-count-roots-mod-p`).  So the two sectors see different arithmetic.
- The vector sector sees a single divisibility, `p | Trd(w^-1) - Trd(w)`.
- The Gelfand--Graev sector sees the simultaneous divisibility `p | Trd(w) - 3` and `p | Trd(w^-1) - 3`,
  and is blind to non-unipotent reductions.

At a fixed length `n`, `T_GG(n) = 0` for all large `p`.  So, unlike the `P^2` sector, the GG sector has no
vertical Chebotarev statistics at all: its whole content sits at `n >> log p`.

## 6. Numerical checks

Code: `experiments/cubic-division-gelfand-graev-2026-09-16/gg.c`, compiled with `gcc -O2 gg.c -lm`.  Its
arithmetic of `Lambda` is `algebra.inc`, copied from `experiments/cubic-division-sc/sc_p2.c`.

**Model.**
- `G/U` is identified with the pairs `(v, w)`, where `v in F^3 minus 0`, `w != 0` and `w_i = 0` at the pivot
  `i` of `v`.  There are `(p^3 - 1)(p^2 - 1)` of them.
- The section is `s(v, w) = (v | w | e_k / det(v, w, e_k))`, with `k` the remaining index.
- The cocycle is `u(g, x) = s(gx)^-1 g s(x)`, which lies in `U`.
- `GG_(a,p)(g) delta_x = psi_a(u(g, x)) delta_(gx)`.

`gg test` checks the identity action and the cocycle identity, and evaluates characters.

**(i) Character formula** (`test-output.txt`, `p = 5, 7, 11, 13`, one random conjugate per element).
- Identity action: no failures.  Cocycle identity `u(gh, x) = u(g, hx) u(h, x)`: 0 failures in 400000.
- Per `a`:
  - the identity gives `(p^2 - 1)(p^3 - 1)`;
  - a transvection gives `-(p^2 - 1)`;
  - `diag(1, 2, 1/2)`, a `(-1)`-Jordan block plus `1`, and a random element all give `0`.
- Regular unipotents: for `kappa = 1` the value is `1`.  For `kappa = 3`, each of the three classes
  `1 + E_12 + c E_23` gives per-`a` values `(2p + 1, -(p - 1), -(p - 1))` in some order, with sum `3`.
  For example `(15, -6, -6)` at `p = 7` and `(27, -12, -12)` at `p = 13`.

**(ii) Extreme eigenvalues at `p = 13`** (`job-p13.sh`, `res-p13.txt`).
- The element is `Z = A + A^-1 + B + B^-1`, with `A = a^19` and `B = b^19`, where `a = L_theta` and
  `b = L_u a L_u^-1` as in the target node.
- Controls: `ctl 1` takes `B` to be a random conjugate of `A`; `ctl 2` takes a Haar-random pair.
- Method: complex Lanczos, `k = 1000` steps, extreme Ritz values found by Sturm bisection.  Ritz values are
  lower bounds for the true extreme eigenvalues.
- Regular norm: `2 sqrt 3 = 3.4641016`.

| sector | dim | arithmetic pair | ctl 1 (seeds 1, 2) | ctl 2 (seeds 1, 2) |
|---|---|---|---|---|
| vector `sigma_13^0` | 2196 | 3.5416 (+0.077) | 3.5076, 3.5562 | 3.4425, 3.5168 |
| `GG_(a,13)`, `a = 1, 2, 4` | 368928 each | 3.4772 (+0.013) | 3.4740, 3.4791 | 3.4719, 3.4697 |

- Theorem 4 gives `||pi_13(Z)|| >= 3.5416` for the arithmetic pair.  Both sectors sit inside the control
  ranges.
- At `p = 13` the vector sector is tiny, and `A mod 13` has order dividing 12, so finite-size effects
  dominate.  This is evidence of nothing asymptotic.
- The three `GG_(a,13)` gave identical extreme Ritz values to 7 digits (one control differs in the 6th
  digit).  This is expected, not a bug.
  - By Frobenius, `Hom_G(Res rho, GG_(a,p)) = Hom_(G~)(rho, Ind_U^(G~) psi_a) = C` for every generic `rho` of `G~`
    and every `a`.  So every generic `rho` that stays irreducible on `SL_3` lies in all `kappa` sectors.
  - The sectors differ only on the constituents of the `rho` with `rho = rho (x) (mu o det)`, `mu` cubic.
  - Short runs (`k = 6, 40`, not saved) did differ across `a`, and 92.9% of cosets have `u_23 != 0`, so the
    operators do depend on `a`.
- `p = 29` has `kappa = 1` and `|G/U| ~ 2.0e7`.  It was estimated not to fit the 10-minute single-thread cap
  on the shared machine, and was not run.
