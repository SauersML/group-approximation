# KMS machine groups with finite classes are residually bounded-prime solvable

Lane `swarm-zaremsky-3-09-braid-groups-sel`, 2026-09-16.  Hole worked:
`some-fp-rf-group-acts-on-no-regular-rooted-tree`.  Claim proven here:
`finite-class-kms-groups-act-on-regular-rooted-trees`.

**Sources.**
- KMS = O. Kharlampovich, A. Myasnikov, M. Sapir, *Algorithmically complex
  residually finite groups*, arXiv:1204.6506v5.  Its LaTeX source was fetched
  and read on 2026-09-16:
  - §3.1: the semigroup `S(M)`, Lemmas 3.4--3.6;
  - §4.1: the group `G(M)`, Lemma 4.1 (`lBRG`), Theorem 4.3, Lemmas 4.4--4.5;
  - §4.2: the semigroup `Š`, the sets `W`, `W_0`, the automorphism formulas,
    and Lemmas 4.9--4.16;
  - the proof of Theorem 4.17.
- Numbering.  The source has one theorem counter per section, shared by lemmas,
  theorems and remarks.  The v5 numbers used here were obtained by counting
  environments in the source, and they agree with the numbers the repo already
  cites (Lemma 4.5, Remark 4.7, Lemmas 4.10, 4.11, 4.14, Theorem 4.17).  The
  published version numbers some results differently; its numbers are not used.
  LaTeX labels are given where a number could be confused: Lemma 3.3 is
  `l:l9`, Lemma 3.5 is `l:fd`, Theorem 3.7 is `t:rc`, Theorem 2.6 is `t:MM`.
- Repo claims used: `kms-minsky-machine-groups-simulate-their-machines` and
  `kms-group-with-stop-relations-simulates-all-words`; for Section 7 also
  clause 1 of `pumped-halting-clocked-minsky-group-is-residually-finite`.

## 0. Statement

Let `M` be a Minsky machine with `K >= 1` glasses (deterministic or not), and
let `p` be a prime.  Let `G_0 = G_0(M)` be the KMS group with the stop
relations `x_(q_0 w) = 1`, `w in U_0`
(`kms-group-with-stop-relations-simulates-all-words`).

**(FC) finite classes.**  Every nonzero `q`-element of `S(M)` is represented
by only finitely many elements of the machine-free semigroup `Š`.

Put:

```text
chi(x)    = x^3 - 2x^2 + x + 1 = x(x-1)^2 + 1,
chi(x+1)  = x^3 + x^2 + 1,
n_0(p)    = lcm of the multiplicative orders of all roots of chi(x) and chi(x+1) in F_p-bar,
q_p       = 4 if p = 2,   q_p = p if p is odd,
pi(p)     = {p} u primes(n_0(p)) u primes(q_p - 1),
d(p)      = max pi(p).
```

Both polynomials have constant term `1`, so their roots are nonzero, and
`n_0(p)` is finite and divides `lcm(p-1, p^2-1, p^3-1)`.

**Theorem.**  Assume (FC).  Then:
- for every `g != 1` in `G_0` there is a finite solvable quotient of `G_0`,
  of order divisible only by primes in `pi(p)`, in which `g` survives;
- consequently `G_0` acts faithfully on the rooted `d(p)`-regular tree.

**Values** (Part B of the experiment script):

| p | n_0(p) | q_p - 1 | pi(p) | d(p) |
|---|---|---|---|---|
| 2 | 7 | 3 | {2, 3, 7} | 7 |
| 3 | 8 | 2 | {2, 3} | 3 |
| 5 | 62 | 4 | {2, 5, 31} | 31 |
| 7 | 114 | 6 | {2, 3, 7, 19} | 19 |
| 11 | 60 | 10 | {2, 3, 5, 11} | 11 |
| 13 | 168 | 12 | {2, 3, 7, 13} | 13 |

**Addendum (where (FC) holds).**  (FC) holds for simple deterministic
clocked universally halting machines (Section 7).  It does NOT follow from
sym-universal halting: Section 7 gives a sym-universally halting 2-glass
machine violating (FC), which also refutes KMS v5 Lemma 3.5(a) as stated.

*Referee correction (2026-09-16).*  The first version of this addendum claimed
(FC) for every sym-universally halting `M`, via KMS Lemma 3.5(a), and hence
for the machines behind KMS Theorems 4.17 and 4.18.  That was wrong, and it has
been replaced.

## 1. Lemma E: bounded composition factors give a regular tree action

Let `C_c` be the class of finite groups whose composition factors all have
order at most `c`.  It is closed under subgroups, quotients, extensions and
finite direct products.

**Lemma E.**  A countable group `G` that is residually `C_c`, with `c >= 2`,
acts faithfully on the rooted `c`-regular tree `T_c`.  Conversely, every
subgroup of `Aut(T_d)` is residually `C_(d!)`.

*Proof.*

1. **A chain of normal subgroups.**  Enumerate `G \ {1} = {g_1, g_2, ...}`.
   For each `g_i` choose a normal subgroup `N(g_i)` with `G/N(g_i)` in `C_c`
   and `g_i` not in `N(g_i)`.  Put `N_k = N(g_1) cap ... cap N(g_k)`.  Then
   `G/N_k` embeds in the product of the `G/N(g_i)`, so it lies in `C_c`, and
   the intersection of all `N_k` is trivial.
2. **Refine to a chain of subgroups.**  Refine `G = N_0 >= N_1 >= ...` by a
   composition series of each finite group `N_(k-1)/N_k`, and delete
   repetitions.  This gives a chain `G = K_0 > K_1 > ...` with
   `d_s = [K_s : K_(s+1)]` in `[2, c]`.  The chain is finite only if `G` is
   finite.  Every `N_k` occurs in it, so the cores of the `K_s` intersect
   trivially.
3. **The coset tree.**  The coset tree `S` has level `s` equal to `G/K_s`,
   and `gK_(s+1)` is a child of `gK_s`.  It is spherically homogeneous with
   branching `d_s`, and `G` acts on it faithfully.
4. **Embedding into `T_c`.**  Number the children at level `s` by
   `0, ..., d_s - 1`.  Then `S` becomes the set of words `x_0 ... x_(r-1)`
   over `{0, ..., c-1}` with `x_s < d_s` for all `s`.
   - Whether a word lies in `S` depends only on the condition `x_s < d_s` at
     each position.
   - For `h in Aut(S)` and `w in T_c`, let `w'` be the longest prefix of `w`
     in `S`, write `w = w'w''`, and put `h~(w) = h(w') w''`.
   - This preserves prefixes and has inverse `(h^-1)~`.
   - If `w'` is maximal, the letter after it is `>= d_(|w'|)`.  So the
     longest prefix of `h(w')w''` in `S` is `h(w')`, and
     `(gh)~ = g~ h~`.
   - `h~ = 1` forces `h = 1`.
   So `Aut(S)` embeds in `Aut(T_c)`, and `G` acts faithfully on `T_c`.
5. **Converse.**  The level-`n` quotient of a subgroup of `Aut(T_d)` embeds in
   the `n`-fold iterated wreath product of `S_d`, which lies in `C_(d!)`.
   The level stabilizers intersect trivially. `∎`

In the terms of `every-fp-rf-group-embeds-in-fp-self-similar-group` (N1): a
group that is residually "solvable with primes at most `d`" is residually
`W_d`, and by Lemma E, if countable, it acts faithfully on `T_d`.

## 2. The structure `G_0 = T_0 x| B`

**Generators and relations** (KMS §4.1).
- `L_0 = {x_u : u in U}`, `L_1 = {A_0, ..., A_K}`,
  `L_2 = {a_i, a_i', ã_i, ã_i' : 1 <= i <= K}`.
- Blocks: `M_0 = {ã_i, ã_i', A_0 : i}` and `M_i = {a_i, a_i', A_i}`.
- G1: `H_0 = <L_0>` and `H_1 = <L_1>` are abelian of exponent `p`, and
  `H_2 = <L_2>` is abelian.
- G2: letters of different blocks commute.
- G3: `(a_i')^-1` is a BR-conjoint of `a_i^-1` with respect to `{A_i}` and
  `f(t) = t - 1`.  Explicitly, with `x^g = g^-1 x g`:
  - `A_i^(a_i^-1) A_i^-1 = A_i^((a_i')^-1)`;
  - `[A_i^(a_i^al), A_i] = 1` for `al in {0, 1, -1}`.
- G4: the same for the `ã_i^-1`, `(ã_i')^-1` with respect to `{A_0}`.
- G5--G8: every relation contains an `x`-letter and becomes trivial when all
  `x_u = 1`.  The stop relations `x_(q_0 w) = 1` do as well.

**Splitting off `T_0`.**  Let `B = <L_1 u L_2 | G1, G2, G3, G4>`, and let `T_0`
be the normal closure of `L_0` in `G_0`.
- `G_0/T_0 ≅ B`.
- The letters define a homomorphism `B -> G_0` whose composite with
  `G_0 -> B` is the identity.

So `G_0 = T_0 x| B`.  The same holds for `G(M)`, as KMS state after Lemma 4.5.

**`B` as a direct product.**  All of G1, G3 and G4 are relations inside single
blocks, apart from commutations between blocks, which G2 implies.  So
`B = B_0 x B_1 x ... x B_K`, where `B_i` is presented by the block `M_i` with
the block's own relations.  This is also the first line of the proof of KMS
Lemma 4.4.

**Explicit blocks.**  For `i >= 1` put

```text
R_i = F_p[s^(±1), (s-1)^(-1)],     U_i = <s, s-1> <= R_i^×,
Q_i = R_i x| U_i                    (U_i acting by multiplication),
```

and send `A_i -> 1 in R_i`, `a_i^-1 -> s`, `(a_i')^-1 -> s - 1`.

- G1 holds: `R_i` has exponent `p`, and `U_i` is abelian.
- The BR relation holds: `1·s - 1 = s - 1`.
- The commutation relations hold, because `R_i` is abelian.

So this defines a surjection `B_i -> Q_i`.  For `i = 0` use

```text
R_0 = F_p[s_k^(±1), (s_k-1)^(-1) : k = 1..K],   U_0 = <s_k, s_k-1 : k>,
A_0 -> 1,   ã_k^-1 -> s_k,   (ã_k')^-1 -> s_k - 1.
```

**Lemma 2.1.**  `B_i ≅ Q_i` for every `i`.  In particular:
- `V = H_1^B = V_0 x ... x V_K` with `V_i ≅ R_i`;
- `H_2 ≅ Z^(4K)`;
- `B = V x| H_2`.

*Proof.*
1. **`H_2` is free abelian.**  In the unique factorization domain
   `F_p[s_1, ..., s_K]` the irreducibles `s_k` and `s_k - 1` are pairwise
   non-associate, so `U_i` is free abelian of rank `2` (rank `2K` for
   `i = 0`).  The abelian group `H_2^(i) = <M_i ∩ L_2>` has that many
   generators and surjects onto `U_i`.  Since free abelian groups are
   Hopfian, `H_2^(i) ≅ U_i`.
2. **`V_i` is a quotient of `R_i`.**  Let `V_i` be the normal closure of the
   `A`-letter in `B_i`.
   - `V_i` is abelian of exponent `p` (KMS Lemma 4.1 applied through G1 and
     G3/G4, as in the proof of KMS Lemma 4.4).
   - `B_i = V_i H_2^(i)`.
   - So `V_i` is a cyclic module over `F_p[H_2^(i)] = F_p[σ^±, τ^±]`,
     generated by the `A`-letter, with `σ = a_i^-1` and `τ = (a_i')^-1`.
   - G3 says the generator is killed by `τ - σ + 1`.
   - `F_p[σ^±, τ^±]/(τ - σ + 1) ≅ R_i`.
3. **`V_i ≅ R_i`.**  The surjection to `Q_i` gives a module map `V_i -> R_i`
   sending the generator to `1`.  The composite `R_i -> V_i -> R_i` is the
   identity, so `V_i ≅ R_i`.
4. **`B_i ≅ Q_i`.**  An element `v h` (`v in V_i`, `h in H_2^(i)`) in the
   kernel of `B_i -> Q_i` has trivial image in `U_i`, so `h = 1`, and then
   `v = 1`. `∎`

## 3. Separating elements outside `T_0` with primes in `{p} u primes(q_p - 1)`

Let `g in G_0 \ T_0`, and let `b != 1` be its image in `B`.

**Case `b` not in `V`.**  `B/V ≅ H_2 ≅ Z^(4K)`.  Reduce modulo `p^m`, with `m`
large, to get a finite abelian `p`-group quotient in which `b` survives.

**Case `b in V`.**  Some component `v_i != 0` of `b` lies in `V_i ≅ R_i`.
Project `B -> B_i ≅ Q_i`.  Choose `ω in F_(q_p)` with `ω ≠ 0, 1`: `ω = -1` for
odd `p`, and `ω` a primitive cube root of unity in `F_4` for `p = 2`.
Evaluate `s_k -> ω`.  This is well defined on `R_i`, because `ω` and `ω - 1`
are units.  Its kernel `m` is maximal, with residue field `F_(q_p)`.

1. **`v_i` avoids `m^j` for large `j`.**  Write `v_i = f/h`, where `f` is a
   polynomial and `h` is a product of the `s_k` and `s_k - 1`.
   - If `v_i in m^j`, then `f h' in (m ∩ F_p[s])^j` for some such product
     `h'`.
   - Over `F_(q_p)[s]`, `m ∩ F_p[s]` lies in the maximal ideal `n` of the
     point `(ω, ..., ω)`.  So `f h' in n^j`.
   - `h'` does not vanish at that point, and `n^j` is `n`-primary, so
     `f in n^j`: `f` vanishes to order `>= j` at the point.
   - For `j > deg f` this is impossible.

   This is Krull's intersection theorem, made explicit.
2. **The quotient is finite.**  `R_i/m^j` is finite, because each `m^r/m^(r+1)`
   is a finite-dimensional `F_(q_p)`-space.
3. **Unit orders.**  For a unit `u` of `R_i`, `u^(q_p - 1) = 1 + y` with
   `y in m`, and `(1+y)^(p^c) = 1 + y^(p^c)`, which is `1` in `R_i/m^j` once
   `p^c >= j`.  So the image `Ū_i` of `U_i` in `(R_i/m^j)^×` is a finite
   abelian group of exponent dividing `(q_p - 1)p^c`.
4. **The finite quotient.**  `Q_i -> (R_i/m^j) x| Ū_i` is a homomorphism,
   because `m^j` is `U_i`-stable.  It keeps `v_i != 0`, and its order has
   prime divisors in `{p} u primes(q_p - 1)`.

Composing `G_0 -> B -> B_i ≅ Q_i -> (R_i/m^j) x| Ū_i` separates `g`.  The
quotient is solvable. `∎`

(KMS's proof of Theorem 4.17 uses instead that finitely generated metabelian
groups are residually finite, which gives no control on primes.)

## 4. The model and the filtration `E_n`

**The model.**  Let `Ḡ = T_1 x| <automorphisms>` be the KMS model:
- `T_1` is elementary abelian with basis `z_(i,u)`, where
  `i in {1,2,3}^K` and `u in W ∪ W_0` is nonzero;
- `z_(i,0) = 1`.

By clauses 1 and 3 of `kms-group-with-stop-relations-simulates-all-words`
there is a surjection `ψ: G_0 -> Ḡ` whose restriction `φ: T_0 -> T_1` is an
isomorphism.  Since `ψ` is a homomorphism,
`φ(g t g^-1) = ψ(g)·φ(t)`.

**Automorphism formulas** (KMS pp. 23--24, formula `(ea)` and the displays
after it), written additively with `j`-th coordinate `i_j`.

- **`a_j`, `u` without `A_j`:**

  ```text
  z_(i,u) -> z_(i,u) + z_(i+e_j,u) + z_(i+2e_j,u) + z_(i,ua_j)   (i_j = 1)
  z_(i,u) -> z_(i,u) - z_(i-e_j,u)                                (i_j = 2)
  z_(i,u) -> z_(i-2e_j,u)                                         (i_j = 3)
  ```

- **`a_j'`, `u` without `A_j`:** `a_j' = a_j - 1`.
- **`a_j`, `a_j'`, `u` containing `A_j`:** both are the identity.
- **`ã_j`:**
  - identity on `u` containing `A_0`;
  - equal to `a_j` on `u` containing neither `A_0` nor `A_j`;
  - for `u = vA_j` without `A_0`, the same display with shift target
    `v a_j A_j`.
- **`ã_j'`:**
  - `ã_j - 1` on `u` without `A_0`;
  - the identity on `u` containing `A_0`.

  This is the reading forced by G5c (`[x_u, z] = 1` for `u` containing `A_0`
  and `z in M_0`).  The literal display `z^(ã_j') = z^-1 z^(ã_j)` would give
  `0` there, which is not an automorphism.
- **`A_j` (`j = 0..K`):** `z_(i,u) -> z_(i,u) + z_(i,uA_j)` if `u` lacks
  `A_j`; the identity otherwise.  For `j = 0` and `u in W` the target is the
  class of `u` in `W_0`.

**Shape of the letters.**  On the part where it is not the identity, each
`L_2` letter has the form `L = D + N`.
- `D` acts on every slice `u` separately.  It is `α ⊗ 1` or `(α - 1) ⊗ 1` on
  the `j`-th tensor factor of `(F_p^3)^(⊗K)`, where

  ```text
  α = [[1,-1,1],[1,1,0],[1,0,0]]    (columns: images of e_1, e_2, e_3).
  ```

- `N = S E_11` sends `e_1` of slice `u` to `e_1` of the slice `u a_j`, and is
  `0` when that element is zero.

`S` commutes with `D`, and `E_11 α^-1 E_11 = E_11 (α-1)^-1 E_11 = 0` (Part A of
the script).  Hence `(N D^-1)^2 = 0` and

```text
L^-1 = D^-1 - D^-1 N D^-1,
```

which has the same shape.  KMS's displayed inverse of `a_j` on the basis
vector with `i_j = 3` does not invert `(ea)`.  In the notation above, the
correct image of `e_3` under `a_j^-1` is `e_1 - e_2 - 2e_3 - S e_3`.  Only the
shape of the inverse is used here, and it follows from the formula for `L^-1`,
not from KMS's display.  The `A_j` letters are `1 + N_A` with `N_A^2 = 0`, and
`N_A` sends slice `u` to slice `uA_j`.

**The weight `ν`.**
- For `u = q a^l A^al in W`, `ν(u) = |l| = l_1 + ... + l_K`.
- For `u in W_0`, `ν(u)` is the maximum of `|l'|` over the elements of `W`
  representing `u` in `S(M)`.  This is finite by (FC).

Then `ν(u a_j) >= ν(u) + 1`, `ν(u A_j) >= ν(u)`, and `ν(class of u) >= ν(u)`,
because right multiplication in `S(M)` respects representatives.

Put `E_n = span{ z_(i,u) : ν(u) >= n }`.

**Lemma 4.1.**
- (a) Every letter and every inverse letter maps `E_n` into `E_n`, so every
  element of `ψ(G_0)` maps `E_n` onto `E_n`.
- (b) `T_1/E_n` is finite.
- (c) `F_n = φ^-1(E_n)` is normal in `G_0`.
- (d) Every `t != 1` in `T_0` lies outside `F_n` for `n` large.

*Proof.*
- (a) `D` preserves slices, `N` raises `ν`, and `N_A` does not lower it.  The
  inverses have the same shape.
- (b) Only finitely many `u in W` have `|l| < n`.  Each class `u in W_0` with
  `ν(u) < n` has a representative with `|l| < n`.
- (c) Normality follows from (a) and `φ(g t g^-1) = ψ(g)·φ(t)`.
- (d) `φ(t)` is a finite combination of basis vectors.  Take
  `n > max ν` over its support. `∎`

## 5. Orders on `T_1/E_n`

Let `ρ_n: B -> GL(T_1/E_n)` be the action through `ψ`, and put
`Γ_n = ρ_n(B)`.

**Lemma 5.1.**  `|Γ_n|` has all prime divisors in `{p} u primes(n_0(p))`.

*Proof.*
1. **Graded pieces.**  On `gr_m = E_m/E_(m+1)` (`0 <= m < n`) the part `N`
   vanishes.
   - `a_j` and `ã_j` act as a direct sum of copies of `α ⊗ 1` and `1`.
   - `a_j'` and `ã_j'` act as a direct sum of copies of `(α - 1) ⊗ 1` and `1`.
2. **Eigenvalues.**  They are `1`, the roots of `χ` (eigenvalues of `α`), and
   the roots of `χ(x+1)` (eigenvalues of `α - 1`).
3. **Orders on the graded pieces.**  By the Jordan decomposition over `F_p`,
   each such matrix has order dividing `n_0(p)·p^k` with `p^k >= 3`.
4. **Orders on `T_1/E_n`.**  So `ρ_n(ℓ)^(n_0 p^k)` is trivial on every
   `gr_m`, hence unipotent with `n` steps, and `ρ_n(ℓ)^(n_0 p^(k+c)) = 1` once
   `p^c >= n`.
5. **The group.**
   - `ρ_n(H_2)` is abelian, generated by `4K` elements of such orders.
   - `ρ_n(V)` is an image of the elementary abelian `p`-group `V`, and it is
     normal in `Γ_n`.
   - `Γ_n = ρ_n(V) ρ_n(H_2)`. `∎`

**Example.**  For `p = 2`, `χ = x^3 + x + 1` and `χ(x+1) = x^3 + x^2 + 1` are
the two irreducible cubics over `F_2`.  Their roots generate `F_8^×`, so
`n_0(2) = 7`.

## 6. Separating elements inside `T_0`

Let `t != 1` in `T_0`, and choose `n` by Lemma 4.1(d).  Define

```text
Φ_n : G_0 = T_0 x| B --> (T_1/E_n) x| Γ_n,     Φ_n(t' b) = (φ(t') + E_n, ρ_n(b)).
```

This is a homomorphism: `E_n` is `ψ(B)`-stable by Lemma 4.1(a), and
`φ(b t' b^-1) = ρ(b)·φ(t')` by equivariance of `φ`.  It sends `t` to
`φ(t) + E_n != 0`.  The target has order `p^(dim) |Γ_n|`, and it is solvable
with prime divisors in `{p} u primes(n_0(p))`.

**Proof of the Theorem.**  Write `g = t b` with `t in T_0` and `b in B`.
- If `b != 1`, use Section 3.
- If `b = 1`, use Section 6.

All the finite quotients used are solvable, with primes in `pi(p)`.  So their
composition factors are cyclic of prime order `<= d(p)`.  `G_0` is finitely
generated, so Lemma E applies. `∎`

## 7. Where (FC) holds, and a counterexample

**Lemma 7.1.**  If every nonzero element of `S(M)` has finitely many divisors,
(FC) holds.

*Proof.*
1. **Divisors of `u`.**  Let `u != 0` be a `q`-element, and let
   `v = q_(j') a^(l') A^(al')` in `W` represent it.  For every `m <= l'`
   (coordinatewise), `u = q_(j') · a^m · (a^(l'-m) A^(al'))`, so `a^m` divides
   `u`.
2. **Distinct `m` give distinct elements.**  Suppose `a^m = a^(m')` in `S(M)`,
   both nonzero.
   - Any derivation between them passes only through nonzero words, since a
     word containing `0` or `q_0` is `0`.
   - So it never uses a 0-relation or the stop relation.
   - Every side of a Minsky relation contains a `q`-letter, so only
     commutativity relations apply to `q`-free words.  These are
     `a_i a_j = a_j a_i`, `a_i A_j = A_j a_i` and `A_i A_j = A_j A_i` for
     `i != j` (KMS v5 §3.1, display `(ec)`).
   - The commutativity relations preserve the exponent of every `a_i`.  Hence
     `m = m'`.
3. **Conclusion.**  The exponents `l'` of representatives of `u` are bounded.
   With finitely many states and `al' in {0,1}^K`, `u` has finitely many
   representatives. `∎`

**A source of (FC).**  Clause 1 of
`pumped-halting-clocked-minsky-group-is-residually-finite`: for a simple
deterministic Minsky machine clocked by a glass `tau` that is universally
halting, every nonzero element of `S(M)` has finitely many representative
words.  The images of these words in `Š` are finitely many, so (FC) holds.  For
such `M` the Theorem of Section 0 applies, and `G_0(M)` acts faithfully on
`T_(d(p))`.

**Counterexample: sym-universal halting does not give (FC)** (referee,
2026-09-16).  Let `M` have `K = 2` glasses, stop state `0`, stop configuration
`(0; 0, 0)`, and the commands

```text
1; e_1 > 0 -> Sub(1); 1        relation  q_1 a_1 = q_1
1; e_1 = 0 -> 2                relation  q_1 A_1 = q_2 A_1
2; e_2 > 0 -> Sub(2); 1        relation  q_2 a_2 = q_1
2; e_2 = 0 -> 0                relation  q_2 A_2 = q_0 A_2
```

1. **Deterministic.**  At each state the two command domains are
   complementary, so the domains are disjoint (KMS v5 §2).
2. **Sym-universally halting.**
   - From `(1; x, y)` the machine empties glass 1, then alternates between
     states 2 and 1, removing one coin from glass 2 each time, and reaches
     `(0; 0, 0)`.  From `(2; x, y)` with `y > 0` it moves to `(1; x, y-1)`.
     So all these configurations are accepted.
   - The rest are not accepted.  `(2; x, 0)` with `x > 0` goes to `(0; x, 0)`
     and stops there.  No command has image `(2; x, 0)` when `x > 0`: the
     only commands entering state 2 are `1; e_1 = 0 -> 2`, which needs `x = 0`.
     So the `Sym(M)`-component is `{(2; x, 0), (0; x, 0)}`.  A configuration
     `(0; x, y)` with `y > 0` has no moves at all.
   - Hence `Sym(M)` halts from every non-accepted configuration.
3. **`q_1 != 0` in `S(M)`.**  Let `C` be the set of words `q_1 a_1^x` and
   `q_2 w`, where `w` is any arrangement of `a_1^x a_2`.
   - `C` is closed under every elementary transformation of the presentation,
     in both directions.  The only Minsky relations whose sides occur are
     `q_1 a_1 = q_1` and `q_2 a_2 = q_1`.  The `A`-letters and `q_0` never
     occur, and the commutativity relations only rearrange `w`.
   - No word in `C` contains `q_0` or a forbidden two-letter subword.
   - So the class of `q_1` is `C`, which avoids `0`.
4. **(FC) fails.**  `q_1 = q_1 a_1^x` for all `x >= 0`.  The words `q_1 a_1^x`
   are pairwise distinct in `Š`, since on nonzero words `Š` only has
   commutativity relations, which preserve `a`-exponents.  By step 2 of
   Lemma 7.1, the `a_1^x` are also pairwise distinct divisors of `q_1`.

**Consequences for KMS.**
- KMS v5 Lemma 3.5(a) (`l:fd`), "if `M` is sym-universally halting, every
  nonzero element of `S(M)` has finitely many divisors", is false as stated.
- Lemma 3.3 (`l:l9`) is also false for this `M`: `W = q_1` is nonzero, is a
  subword of `w(1; 0, 0)`, and lacks both `A`-letters, but it is equal to
  infinitely many words.  Its proof bounds both parts of a `Sym(M)`-computation
  by property (c) of Theorem 2.6 (`t:MM`).  That property is stated only for
  `MM_2`, `MM_3`, and concerns emptying glasses.
- The proof of Theorem 4.17 (`t:rfg1`) uses "Since M is sym-universally
  halting, E is finite" (the set of words equal to given `u_j in W_0`).  For
  this `M` that step has no support.  Whether the conclusion of Theorem 4.17
  holds for this `M` is not decided here.
- The machines behind Theorems 4.17 and 4.18 come from Theorem 2.6(d) and the
  proof of Theorem 3.7 (`t:rc`).  Whether they satisfy (FC) was not checked.
  So this artifact does not cover them.
- The same holds for the machines `M_n` in the proof of Theorem 4.19
  (`t:rhog`), built in the proof of Theorem 3.9 (`t:rho`).

**Script.**  `experiments/kms-groups-bounded-factors-2026-09-16/referee_fc_counterexample.py`
(output `referee_output.txt`, under a second) checks steps 1--2 on the grid
`x, y < 12`, including closure of each non-accepted component.  It also runs a
length-capped search from `q_1` through all relations in both directions.  No
zero word is reached, and `q_1 a_1^x` appears for `x = 0..8`.  This is evidence
only.

## 8. Scope and weakest points

**Not covered.**
- **`G(M)` as displayed, without stop relations.**  Its `T` is not identified
  with `T_1` (the stop-relation claim).  The published version keeps `q_0`
  nonzero, and whether the argument transfers there is unverified.
- **The pumped groups `G_0(P(M))`.**  Their `S(P(M))`-classes are infinite,
  since pumping trades `a_π a_ρ` freely.  So `ν` is infinite on `W_0`, and the
  filtration of Section 4 does not exist.

  The repo's residual finiteness proof for them uses periodic quotients
  `a_π^D = a_π^(2D)`, whose shifts do not vanish on graded pieces.  The
  eigenvalue control of Section 5 is then lost.  For `D = p^k` one expects
  bounded primes again, but this was not checked.
- **Non-FC machines in general**, such as the counterexample of Section 7.
- **The machines behind KMS Theorems 4.17--4.19.**  Whether they satisfy (FC)
  was not checked (Section 7).

**Weakest points, in order.**
1. **The reading of `ã_j'` on `A_0`-words.**  It is taken to be the identity,
   as forced by G5c.
2. **Imported structure.**
   - The exact block `α` is read off KMS `(ea)`, and the shape `D + N`
     (including for `ã_j` on `vA_j`) off pp. 23--24.
   - `T_0 ≅ T_1` equivariantly is imported from the stop-relation claim.
3. **The source of (FC).**  The only machines covered are those with (FC),
   for instance clocked ones through an imported repo claim.
4. **Lemma 2.1, `B_i ≅ Q_i`.**  This uses that G3/G4 are the only relations
   between the letters of a block.

**Experiment.**  `experiments/kms-groups-bounded-factors-2026-09-16/`
(`check_kms_bounded_factors.py`, output in `output.txt`, about 40 s,
single-threaded) builds the automorphisms on `T_1/E_n` explicitly.
- **Machine-free cases** `(K, n, p) = (1,5,2), (1,5,3), (1,4,5), (2,3,2), (2,3,3)`.
- **One-command machine** `q_1 = q_2 a_1`, with `(n, p) = (5,2), (5,3)`.

In each case it checks:
- G2, and that `H_2` and `H_1` are abelian with `H_1` of exponent `p`;
- that twelve random `H_2`-conjugates of `L_1` letters commute and have
  order `p`;
- that generators and 25 random words have order dividing `n_0(p)·p^e`;
- that the prime-to-`p` part of every generator order divides `n_0(p)`
  (for the cases of dimension at most 130);
- (Part E) the BR-conjoint relations G3 (`a_j, a_j', A_j`, each block `j`) and
  G4 (`ã_k, ã_k', A_0`).  Matrices have the images `z^g` as columns, so
  `M_(gh) = M_h M_g`, and `A^(a^-1) A^-1 = A^((a')^-1)` reads
  `M_A^-1 M_a^-1 M_A M_a = M_(a')^-1 M_A M_(a')`.  The script also checks that
  `A` commutes with `A^(a^±1)`.  As a control it evaluates the mirrored
  (left-action) identity, which fails in every case.  So the check is not
  vacuous, and the model is consistent with the right-action reading.

All checks pass.  The observed `a`-letter orders are:
- `56 = 2^3·7` for `p = 2`;
- `36` or `72` for `p = 3`;
- `310 = 2·5·31` for `p = 5`.

These match `n_0(2) = 7`, `n_0(3) = 8` and `n_0(5) = 62`.
