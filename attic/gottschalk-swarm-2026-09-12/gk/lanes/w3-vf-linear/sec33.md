
## 33. Endomorphism-invariant p-cycle tree models, a second derivation of [CG] Theorem 1.1, and the ternary gate (w7-v-cycle-c3; 2e8bf4f44, artifact `p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md`)

I re-derived this at tip 45282c214. The artifact (blob acd9ae31) and the new node (f182b967) are unchanged since 2e8bf4f44.
Since then, the claim node and the law node went ESTABLISHED through w7-v-cycle-c2's routes (f0b103bb41). c3's
Attempts entries on those nodes are unchanged.

### 33.1 Section 0 (Sylvester facts): PASS

* **(S7).** `U_k^2 = 1`, since `e(1−e) = 0`. Then `U_m diag(M,0) U_n = [[eMe, eM(1−e)], [(1−e)Me, (1−e)M(1−e)]]`,
  which is `diag(Me, M(1−e))` when `e` commutes with the entries of `M`.
* **(S8).** By (S5), `col(Y ∪ Y')` and `col(Y')` have the same rank; then delete rows. The augmentation ideal is the
  left ideal of `{1 − [s]}`, because `1 − [gh] = (1 − [g]) + [g](1 − [h])`.
* **(S9).**
  * `x -> x(E)` is multiplicative, by the index computation.
  * `E` is idempotent, and every `E_(g,h)` lies in `ERE`. So `u(E) + (1−E)I` has inverse `u^(-1)(E) + (1−E)I`.
  * `d(E)` is diagonal and carries `r` of the idempotents `E_(g,g)`. They all have the same rank, since
    `E_(g,g) = E_(g,h) E_(h,h) E_(h,g)`, and (S3) gives `rk'(E) = |I| rk'(E_(g,g))`.

### 33.2 Section 1 (second derivation of Theorem 1.1): PASS

* **Step 0.**
  * `T_(gQ)` is well defined: `g^(-1)g'` is the identity on `Q`, so it commutes with anything supported in `Q`.
  * `B` is an exponent-`q` clopen-cycle subgroup, and its supports leave a nonempty complement.
  * `G` permutes the factors of `B`.
* **Step 1.** `[g] e_psi [g]^(-1) = e_(g psi)`, where `(g psi)(b) = psi(g^(-1) b g)`. `E_O`, `D` and `e_1` are
  `G`-invariant sums, and (S7) iterates.
* **Step 2.** `e_(h psi) [k l^(-1)] = [k l^(-1)] e_(l k^(-1) h psi)`, and `e_(l k^(-1) h psi) e_(l psi)` is
  `delta_(h,k) e_(l psi)` on a free orbit. Also `[x] E_O = sum_h E_(xh,h) = lambda(x)(E)`, so `M E_O = lambda(M)(E)`.
* **Step 3.** If `h psi = psi`, then `psi_(hQ)(h b h^(-1)) = psi_Q(b)`. So each `h != 1` fixes at most `|B| q^(-k)`
  characters, and `rk'(D) <= |G|(1 − a) q^(-k)`.
* **Step 4.**
  * `e_1` commutes with `[x]`.
  * (S7) and (S5) give an equality, because `(1 − [x])(1 − e_1)` lies in the left ideal of `1 − e_1`.
  * So `rk'((1 − [x]) e_1) <= (1 − a)/|B|`, and summing over `x` gives `n|G|(1 − a)/|B|`.
* **Step 5.** The three errors are:
  * the orbit mass, at most `(|G| + 1)(1 − a) q^(-k)`, times `rk_reg <= n`;
  * `n|G|(1 − a) q^(-k)`;
  * `n(|G| + 1)(1 − a) q^(-k)`.

  The total is at most `3n(|G| + 1)(1 − a) q^(-k)`.
* **Precision note.** This is the note c2 has already applied. When `G = 1`, the orbit `{1}` is free, so `e_1` is
  counted twice. That case is trivial, but the wording should say "free orbits of nontrivial characters".
* **Remark 1.2** is accurate. The inputs are the same, so this is a cross-check, not an independent verification.

### 33.3 Section 2: Lemmas 2.1–2.2 and Proposition 2.3 PASS; the Consequence overreaches

* **Construction.** The coefficient of `u^s` in `exp_m(au) exp_m(bu)` is `sum_(i+j=s) a^i b^j/(i! j!) = (a+b)^s/s!`
  for `s < m <= p`. So `rk_m` is the pullback of the normalized rank on `M_m(L)`. `rk_1` is the augmentation rank,
  and for `p = 2`, `rk_2` is [CG] Section 3.
* **Lemma 2.1.**
  * Columns that are independent over `F_p` stay independent over `F`.
  * Only finitely many variables occur. Complete the substitution to an invertible one: that is an automorphism of
    `F[t_(I_0)]`, and it extends to the fraction fields.
  * Rank is invariant under field extension.
  * The lemma covers every `V`-conjugacy between subgroups of `E`, which is more than "basis-shaped tuples".
* **Lemma 2.2.** `1 − exp_m(lambda u)` is `u` times a unit. The kernel of `col(u w_i)` is `u^(m−1) L`, so the
  column has rank `m − 1` and `phi = 1/m`.
* **Proposition 2.3.**
  * **(1)** Take `w_m = m(d_(m−1) − d_m)`. Then `sum_m w_m = sum_j d_j = 1`. [FW] Proposition 4.2(b) says exactly
    that `d` is non-increasing, nonnegative and sums to 1.
  * **(2)** `j = m` forces `phi = 1`, and then `j = 1` gives `(m − 1)/m != 0`.
  * **(3)**
    * `rho_2(M_i)` is a `2n_i`-square matrix over `F_p[t]` with entries of degree at most 1, so a maximal
      nonvanishing minor has degree at most `2n_i`.
    * Specialization never raises rank. Schwartz–Zippel and a union bound give
      `sum_(i<=k) 2i/p^k = k(k+1)/p^k`.
    * The quotient description needs `lambda_k != 0` on `E_r`. That holds at large `k`, since `1 − [tau_1]` is
      enumerated.
  * **(4)** By Theorem 1.1, `phi_(E_r) = phi_V + (1 − phi_V) p^(-r)`, since the kernel of `col Reg(1 − [tau_i])` is
    the constants. A mixture gives `sum_m w_m/m`, which is constant in `r`. So `phi_V = 1` and `w_1 = 1`. This needs
    `|I| >= 2`.
* **Premise audit.**
  * **Existence of `s`.** `s` cycles `p` disjoint cylinders `U_i` that leave a nonempty complement, and
    `tau_i = s^i tau_0 s^(-i)`.
  * **Mackey.** The restriction of the induced module to `E_p` is the direct sum of twists, whose average is `rk_m`
    by Lemma 2.1. The restriction to `<s>` is the free module `L[<s>]^m`, with profile `(p − j)/p`.
  * **The conflict.** At `j = m`, `s` has rank `(p − m)/p > 0` and `tau_1` has rank 0, yet [TS] Lemma 1.1 makes
    them `V`-conjugate.
  * **`m = p`.** Single elements agree, as stated.
* **Scope correction needed before ESTABLISHED.**
  * **What is proved.** The models are built only on elementary abelian `p`-groups. The only extension to the
    nonabelian `p`-group `W = E_p ⋊ <s>` that the audit examines is induction, and it breaks `V`-conjugacy. No
    coherent extension to `W` is built.
  * **The overclaim.** "No argument confined to `p`-groups of `V` and their injective endomorphisms forces the law
    for `p >= 3`, or trivial-plus-regular restrictions for any `p`" is proved only for elementary abelian
    `p`-subgroups (`E_infinity`, the trees `E_n`) and injective homomorphisms between them.
  * **Not covered.** Data at `W` together with the `V`-conjugacy `s ~ tau_1` is exactly where the model breaks, and
    nothing here says whether it forces the law.
  * **Where to fix it.** The same scope applies to:
    * the node title ("data inside p-groups");
    * the first "Why it matters" bullet;
    * the artifact's Section 2 Consequence;
    * the Section 3 bullet "3-groups alone don't give the law";
    * the ternary gate's "The law needs a prime other than 3".

    The law itself is ESTABLISHED through `q != p`, so these statements are about methods, and they should be
    scoped.

### 33.4 Section 3 (ternary gate): PASS

* **Convexity.** `phi_V` is affine. If `phi_V(rk) < 1`, then `(rk + rk_aug)/2` has `phi_V` in `[1/2, 1)`. [FR]
  Corollary 1.3(3) reads "`rk` is the augmentation rank iff `phi_V = 1`". So the equivalence holds.
* **Settled items.**
  * Every locally finite subgroup follows from its finite subgroups, because `rk_reg` is coherent under inclusion
    (the regular module restricts to a free one).
  * [FR] Theorem 2.3 is cited correctly (§30).
  * The inert item holds by [FW] Theorem 1.2 (§31).
* **Step 2** is honestly OPEN.

### 33.5 Scan, node displays and verdict

* **Scan.** I ran `git grep` over `research/*.md` without truncation for `exp_m`, truncated exponential, constant
  Jordan type, Frobenius-allowed, Frobenius inequality, endomorphism-invariant, level-coherent, p-cycle tree,
  `A/m^2`, wreath configuration and `E_infinity`: 54 files.
  * **ESTABLISHED hits.** `leavitt-unit-hosts-need-nilpotents-of-unbounded-index`, the Sylvester compress, descend
    and Kazhdan nodes, `ternary-anti-central-two-root-defect-has-a-uniform-gap`,
    `ternary-cylinder-defect-products-descend-in-sign-sectors`, and two Maslov nodes. They match only on the
    Frobenius inequality or on an unrelated `E_infinity` (inside `Sp_4`).
  * **Result.** No ESTABLISHED node covers claims 1–6, and the `distinct_from` entries are accurate.
* **Node displays.**
  * The new node's claims 1–6 and Attempts match the artifact.
  * The law node's "Next test for p >= 3" matches Section 2.
  * The claim node's "Second derivation" matches Section 1.
  * The ternary gate's entry matches Section 3, but it still calls the cylinder-group node a "candidate". That node
    has been ESTABLISHED since f0b103bb41.
* **Not decision-level.** No rank function on `F[V]` is built (item 4 proves non-extension), and no identity proof is
  given.
* **Verdict.**
  * Section 1: PASS, as a cross-check.
  * Section 2: Lemmas 2.1–2.2, Proposition 2.3(1)–(4) and the premise-audit computations PASS. Claims 1–6 of
    `p-cycle-tree-invariance-cannot-force-order-char-law` may go ESTABLISHED once "p-groups" is restricted to
    elementary abelian `p`-subgroups in the title, in "Why it matters", in the artifact's Consequence and in the
    ternary-gate bullet.
  * Section 3: PASS.
  * Both gates stay OPEN.
