# Monomial Hilbert--Schmidt models of the Kun--Thom wreath kill a fibre-even lamp

Lane `ex-q34-kt-wreath-soft-kernel`, 2026-09-13.  Everything below is proved in
full here.  Nothing was run.  Unreviewed by an independent verifier.

## 0. Summary

`W = F_2[G/Gamma] x| G` is the Kun--Thom wreath over the Theorem E pair.  A
*monomial HS model* is a homomorphism `rho : W -> prod_omega (U(1) wr S_n)`
into the tracial ultraproduct of monomial unitaries.  No trace condition is
assumed.

1. **The soft kernel contains the fibre-even lamps (Lemma 1).**  In every
   block-monomial model, of any block size, the permutation part kills
   `K_even`.  This is the sofic radical of `W`, read through the permutation
   part.
2. **A Kazhdan-invariant fibre-even configuration (Lemma 2).**  For a
   compressor `s in SL_d(Z)` with positive entries and `h = e_12(x_1^(-1))`,
   the coset `s^(-1) h Gamma` has a finite `Gamma`-orbit `O`.  With a parity
   correction at the `Gamma`-fixed coset `s^(-1) Gamma`, this gives a nonzero
   `Gamma`-invariant configuration `u` in `K_even`.
3. **Theorem 3.**  For every monomial HS model `rho` of `W` and every
   `n in EL_r(R)`, `rho(u + n.u) = 1`.  So no monomial HS model of `W` is
   injective.  In particular `W` has no regular monomial HS model, and no
   regular HS microstates that approximately normalize a full masa.
4. **Reading for Q3.4.**  Partly-soft models were the one case left open by
   `block-monomial-coordinate-collapse` (all lamps soft) and by the
   soft-kernel split.  They do not exist.  Lemma 1 already shows that "only
   part of the lamp module is soft" means `K_even <= U <= P`.  Lemma 2 shows
   that `K_even` itself carries the rigid invariant that Kun--Thom 4.1
   detects.  The Kun--Thom wreath now joins the binary Leavitt unit group and
   the `q = 2` double: any hyperlinear model of it is frame-incoherent.

The phases play no role.  Covariance of a diagonal under conjugation by a
monomial is exact, whatever the phases.

## 1. Setting

`q` is a prime power, `r, d >= 3`, `R_+ = F_q[x_1..x_d]`,
`R = F_q[x_1^(±1)..x_d^(±1)]`, `SL_d(Z)` acts on `R` by monomial substitution
`s.x^a = x^(sa)`, and

```text
Gamma = EL_r(R_+)  <  G = EL_r(R) x| SL_d(Z),        N = <<Gamma>>_G = EL_r(R).
```

This is the pair of `kun-thom-nonsofic-wreath` (Theorem E: `Gamma`, `G`
residually finite Kazhdan, `Gamma` infranormal).  `N = EL_r(R)` is Step 0 of
`kun-thom-wreath-sofic-radical-fibre-parity-proof`.  Put

```text
P = F_2[G/Gamma] (basis e_x),     W = P x| G,
K_even = configurations meeting every fibre of G/Gamma -> G/N evenly.
```

`Rad_sof(W) = K_even` (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`).

Monomial matrices: `M = (c; sigma)` acts by `M e_x = c(x) e_(sigma x)`, with
`c(x) in U(1)`.  The permutation part `pi(M) = sigma` is a homomorphism.  The
frame-extraction artifact (`research/artifacts/ex-q34-frame-extraction-2026-09-12.md`,
Lemma 1) proves, for block size `k` and normalized HS norm,

```text
d_H(pi M, pi M') <= ||M - M'||_2^2 / 2,        ||M - (c; id)||_2^2 = 2 d_H(sigma, id).   (HC)
```

So `pi` induces a homomorphism `pi_omega` into `S_omega = prod_omega (S_n, d_H)`.
`D_omega = prod_omega (l^inf_n, tr)` is the diagonal ultraproduct.  Two exact
identities are used throughout.  For a monomial `M = (c; sigma)` and a
diagonal `f`,

```text
M f M^* = f o sigma^(-1),                  E_D(M X M^*) = M E_D(X) M^*.          (COV)
```

The first holds because the phases cancel, `c(x) f(x) c(x)^(-1) = f(x)`.
The second holds because `(M X M^*)_(sigma x, sigma x) = c(x) X_(xx) c(x)^(-1)`.

## 2. The soft kernel contains K_even

**Lemma 1.**  Let `rho : W -> prod_omega (U(k_m) wr S_(n_m))` be any
homomorphism, with arbitrary block sizes and no trace condition.  Then
`psi = pi_omega o rho` kills `K_even`.  Hence for `k_m = 1` every `rho(v)`,
`v in K_even`, lies in the unitary group of `D_omega`.

*Proof.*  `psi(W)` is a countable subgroup of `S_omega`, hence sofic (Pestov,
arXiv:0804.3968, Definition 3.1).  Every homomorphism from `W` to a sofic group
kills `Rad_sof(W) = K_even`.  For the second statement, a representative
`(c_m; sigma_m)` of `rho(v)` has `d_H(sigma_m, id) -> 0`, so by (HC) the
diagonal `(c_m; id)` represents the same element.  ∎

The same argument gives `ker psi ⊇ K_even / U` for every lamp quotient
`W / U` with `U <= K_even` (Theorem A of
`research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md`).

## 3. A Gamma-invariant fibre-even configuration

**Lemma 2.**  Let `s in SL_d(Z)` have all entries positive, and put
`h = e_12(x_1^(-1)) in N`.  Then:
(a) `s Gamma s^(-1) <= Gamma`, so the coset `s^(-1) Gamma` is fixed by `Gamma`;
(b) the coset `c = s^(-1) h Gamma` has a finite `Gamma`-orbit `O`, which lies
    in the fibre of `s^(-1) Gamma` and does not contain it;
(c) `u = 1_O` if `|O|` is even and `u = 1_O + e_(s^(-1) Gamma)` if `|O|` is
    odd is a nonzero `Gamma`-invariant element of `K_even`;
(d) for every nonzero `v in P` there is `n in N` with `n.v != v`.

Such `s` exist: `s = UL` with `U` upper and `L` lower unitriangular, all
entries on and above (resp. below) the diagonal equal to `1`, has
`(UL)_(ij) = d + 1 - max(i, j) >= 1` and determinant `1`.

*Proof.*  (a) `S' := s(R_+) = F_q[y_1..y_d]` with `y_j = x^(s e_j)`.  The
columns of `s` are positive, so `S' <= R_+`, and `s Gamma s^(-1) = EL_r(S') <= Gamma`.
Then `gamma s^(-1) Gamma = s^(-1) Gamma` iff `s gamma s^(-1) in Gamma`, which
holds.

(b) `gamma c = c` iff `h^(-1) (s gamma s^(-1)) h in Gamma`.  Conjugation by
`s` maps `Gamma` onto `EL_r(S')`, so

```text
[Gamma : Stab_Gamma(c)] = [EL_r(S') : EL_r(S') ∩ h Gamma h^(-1)].
```

Let `I = (y_1^2, ..., y_d^2) S'`.  Each `y_j` is divisible by `x_1`, since
`s_(1j) >= 1`, so `I <= x_1^2 R_+`.  And `S'/I` is finite, of size
`q^(2^d)`.  Let `gamma' = 1 + B in EL_r(S')` with `B in M_r(I)`.  With
`h^(±1) = 1 ± x_1^(-1) E_12`,

```text
h^(-1) B h = B + x_1^(-1) (B E_12 - E_12 B) - x_1^(-2) E_12 B E_12  in  M_r(R_+).
```

So `h^(-1) gamma' h in SL_r(R_+)`, which equals `EL_r(R_+) = Gamma` by
Suslin's theorem (`SL_r(k[x_1..x_d]) = E_r(k[x_1..x_d])` for a field `k` and
`r >= 3`; A. A. Suslin, Izv. Akad. Nauk SSSR Ser. Mat. 41 (1977) 235--252).
Hence `EL_r(S') ∩ h Gamma h^(-1)` contains the kernel of
`EL_r(S') -> SL_r(S'/I)`, whose index is at most `|SL_r(S'/I)| < infinity`.
So `O` is finite.  `c = (s^(-1) h s) s^(-1) Gamma` with `s^(-1) h s in N`, so
`c` lies in the fibre of `s^(-1) Gamma`, and so does `O`, because `Gamma <= N`
preserves fibres.  If `s^(-1) Gamma in O`, then `c in Gamma . s^(-1) Gamma = {s^(-1) Gamma}`,
so `h in Gamma`.  But `x_1^(-1) notin R_+`.

(c) `O` and `s^(-1) Gamma` are `Gamma`-invariant and disjoint, all inside one
fibre, and the parity correction makes the count even.

(d) The `N`-orbit of a coset `g Gamma` is `N / g Gamma g^(-1)`, which is in
bijection with `N / Gamma` by conjugation.  `N / Gamma` is infinite, since the
cosets `e_12(x_1^(-k)) Gamma` are distinct.  A finitely supported
`N`-invariant configuration has a finite `N`-invariant support, so it is `0`.  ∎

## 4. The theorem

**Theorem 3.**  Let `rho : W -> prod_omega (U(1) wr S_(n_m))` be any
homomorphism.  Let `Gamma' = g Gamma g^(-1)` be a conjugate of `Gamma`, and
`v in K_even` be `Gamma'`-invariant.  Then `rho(n.v) = rho(v)` for every
`n in N`.  With `u` from Lemma 2 and `n` from Lemma 2(d),
`u + n.u` is a nonzero element of `K_even ∩ ker rho`.

*Proof.*  By Lemma 1, `b := rho(v)` is a unitary in `D_omega`, and `b^2 = rho(2v) = 1`.
For `gamma in Gamma'`, (COV) gives

```text
psi(gamma) . b = rho(gamma) rho(v) rho(gamma)^* = rho(gamma . v) = b,
```

so `b in D_omega^(psi(Gamma'))`.  `psi|G` need not be a sofic representation,
so tensor.  `G` is residually finite, so it has a sofic representation
`lambda : G -> prod_omega Sym(Z_m)` with `tr lambda(x) = 0` for `x != 1`,
along the same `omega`.  Put `sigma'(x) = psi(x) × lambda(x)` on
`Y_m × Z_m`, and `b' = b ⊗ 1`.  Hamming defects add, so `sigma'` is a
homomorphism.  Its traces are products, so `tr sigma'(x) = 0` for `x != 1`.
And `sigma'(gamma) . b' = (psi(gamma) . b) ⊗ 1 = b'`.  `Gamma'` is infranormal
in `G`, both groups are Kazhdan, and `<<Gamma'>>_G = N`.  By part 2 of
`normal-closure-fixes-gamma-fixed-algebra` (Kun--Thom 4.1), every element of
`N` acts trivially on `D^(sigma'(Gamma'))`.  So
`(psi(n) . b) ⊗ 1 = b ⊗ 1`, so `psi(n) . b = b`, and by (COV) again
`rho(n.v) = rho(n) rho(v) rho(n)^* = b = rho(v)`.  Then
`rho(v + n.v) = rho(v)^2 = 1`.  For `v = u`, choose `n` with `n.u != u`.
Both `u` and `n.u` lie in `K_even`, because `n` preserves fibres.  ∎

**Corollary 4.**
(a) No monomial HS model of `W` is injective.  In particular `W` has no
    regular monomial HS model.
(b) There are a finite window `F <= W` and `delta > 0` such that no
    `(F, delta)`-almost multiplicative, `delta`-trace-separating unitaries
    `U_w in U(n)` satisfy `def_D(U_w) <= delta` for the full diagonal masa
    and all `w in F`.  So `W` has no regular HS microstates that
    approximately normalize a full masa.
(c) By Lemma 1, every block-monomial model of `W`, of any block size, has
    soft kernel containing `K_even`.  For block size `1` no model is
    injective on `K_even`, so partly-soft models, with
    `K_even <= soft lamps < P`, do not exist.

*Proof.*  (a) is Theorem 3.  (b) By the standard diagonal argument, finitary
microstates along windows exhausting `W` with `delta -> 0` assemble into a
regular ultraproduct model.  Clause 1 of `diagonal-normalizer-rigidity` moves
each `U_w` within `3 sqrt(delta)` of a monomial, which changes multiplicative
defects and traces by `O(sqrt(delta))`.  This contradicts (a).  (c) Regular
models are injective.  ∎

## 5. Model tests and scope

- *A real object satisfies the hypothesis.*  `W_N = F_2[G/N] x| G` is residually
  finite, and its permutation models pulled back to `W` are monomial models.
  They kill all of `K_even`, as Theorem 3 requires.
- *The Kazhdan pair is load-bearing.*  For the lamplighter `F_2 wr Z`, a
  sofic approximation of the Bernoulli shift, with lamps as diagonal
  coordinate signs and `Z` acting by permutations, is a regular monomial
  model, and it kills nothing.  There is no infranormal Kazhdan pair there.
- *Where Kun--Thom enters.*  Only through part 2 of
  `normal-closure-fixes-gamma-fixed-algebra`, applied to a genuine sofic
  representation `psi × lambda`.  The monomial phases never enter, by (COV).
  So the extension of Kun--Thom 4.1 to monomial matrices is not needed.
- *Block size `k >= 2`.*  Lemma 1 holds, but (COV) fails: conjugating a
  block-diagonal element by a block-monomial one rotates inside blocks.  The
  bounded-block case for `W` is not settled here.
- *Intermediate wreaths `W_K`, `Gamma <= K <= N`.*  Lemma 1 holds with
  `K_even / U_K`.  Theorem 3 needs a `Gamma`-invariant element of
  `K_even / U_K` that `N` moves.  The image of `u` may vanish there, and no
  claim is made.
- *What is not claimed.*  Nothing here says `W` is not hyperlinear.  The
  theorem says any hyperlinear model of `W` is frame-incoherent in the sense
  of `hyperlinear-implies-sofic-via-frame-extraction`.
