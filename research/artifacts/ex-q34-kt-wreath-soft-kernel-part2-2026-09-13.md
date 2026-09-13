# Monomial HS models of the Kun--Thom wreath factor through the fibre-parity quotient

Lane `ex-q34-kt-wreath-soft-kernel`, 2026-09-13, part 2.  Continues
`research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md`, which is
cited as part 1 (notation, (HC), (COV), Lemma 1).  Everything is proved in
full here.  Nothing was run.  Unreviewed.

## 0. Summary

1. **Transport lemma (Theorem M).**  Let `Lambda <= G <= H` with `Lambda` and
   `G` Kazhdan, `Lambda` infranormal in `G`, and `G` sofic.  Let `rho` be a
   monomial HS model of `H`.  If `a in C_H(Lambda)` has trivial permutation
   part, then `rho(n a n^(-1)) = rho(a)` for every `n in <<Lambda>>_G`.
   The phases never enter.
2. **Deep congruence conjugates (Lemma 6).**  For the Theorem E pair, every
   finite set of cosets in the fibre `N/Gamma` is fixed by some conjugate of a
   congruence subgroup `Gamma(m^k)`.  That conjugate is infranormal and
   Kazhdan, with normal closure `N`.
3. **Theorem 7.**  Every monomial HS model of `W` kills all of `K_even`.  So
   the intersection of the kernels of all monomial HS models of `W` is
   `K_even = Rad_sof(W)`: U(1)-phases detect exactly what permutations
   detect.  The same holds for every lamp quotient `W/U` with `U <= K_even`.

Part 1's Lemma 2 (finite orbits) and Theorem 3 remain correct.  Theorem 7
supersedes their conclusion.

## 1. The transport lemma

**Theorem M.**  Let `H` be countable.  Let `Lambda <= G <= H` with `Lambda`
and `G` Kazhdan, `Lambda` infranormal in `G`, and `G` sofic.  Let
`rho : H -> prod_omega (U(1) wr S_(n_m))` be a homomorphism, with permutation
part `psi`.  Let `a in H` commute with `Lambda` and have `psi(a) = 1`.  Then

```text
rho(n a n^(-1)) = rho(a)        for every n in <<Lambda>>_G.
```

*Proof.*  By (HC), `b := rho(a)` lies in the unitary group of `D_omega`.  For
`l in Lambda`, (COV) gives `psi(l) . b = rho(l a l^(-1)) = b`.  Let `lambda` be a
sofic representation of `G` along `omega` (`tr lambda(x) = 0` for `x != 1`),
and `sigma' = psi|G × lambda`.  `sigma'` is a homomorphism into
`prod_omega Sym(Y_m × Z_m)` with vanishing traces off the identity, and
`b ⊗ 1` is fixed by `sigma'(Lambda)`.  Part 2 of
`normal-closure-fixes-gamma-fixed-algebra` (from Kun--Thom 4.1) makes
`<<Lambda>>_G` act trivially on `D^(sigma'(Lambda))`.  So
`psi(n) . b = b`, and `rho(n a n^(-1)) = rho(n) b rho(n)^* = psi(n) . b = b`
by (COV).  ∎

The Hamming row (`sofic-groups-kill-rigid-compression-defects`) transports
every centralizing element along all of `G`.  Theorem M transports only soft
centralizing elements, and only along the normal closure.  But it does so
for monomial models, whose soft kernel is abelian and can be nontrivial.

## 2. Deep congruence conjugates

Notation of part 1: `R_+ = F_q[x_1..x_d]`, `Gamma = EL_r(R_+)`,
`G = EL_r(R) x| SL_d(Z)`, `N = EL_r(R)`, `r, d >= 3`.  Let
`m = (x_1..x_d) <= R_+` and

```text
Gamma(m^k) = ker( EL_r(R_+) -> SL_r(R_+/m^k) ).
```

**Lemma 6.**
(a) `Gamma(m^k)` is Kazhdan and infranormal in `G`, and
    `<<Gamma(m^k)>>_G = N`.
(b) Let `h_1..h_p in N`.  There are `k` and `s in SL_d(Z)` such that
    `Lambda = s Gamma(m^k) s^(-1)` fixes every coset `h_i Gamma`, and also
    `Gamma`.

*Proof.*  (a) `R_+/m^k` is finite, so `Gamma(m^k)` has finite index in the
Kazhdan group `Gamma` and is Kazhdan.
- *Compressors.*  `Gamma` normalizes `Gamma(m^k)`.  Let `t in SL_d(Z)` have
  nonnegative entries.  Then `t(R_+) <= R_+`.  Every column of `t` is nonzero,
  so `|t a| >= |a|` for `a in N^d`, where `|a|` is the coordinate sum, and
  `t(m^k) <= m^k`.  So `t Gamma(m^k) t^(-1) = t(Gamma(m^k)) <= Gamma(m^k)`.
- *Generation.*  The nonnegative matrices include the elementary matrices
  `e_ij(1)` of `SL_d(Z)`, which generate `SL_d(Z)`.  Every `c in Z^d` has the
  form `t a` with `a in N^d` and `t in SL_d(Z)`: write `c = mu p` with `p`
  primitive, move `p` to `e_1`, and use transitivity on primitive vectors.  So
  `<Gamma, SL_d(Z)>` contains every `e_ij(x^c)`, hence `N`, hence `G`.  So the
  compression semigroup of `Gamma(m^k)` generates `G`.
- *Normal closure.*  It lies in `N`.  It contains `e_ij(x^a)` for `|a| >= k`.
  Every `c != 0` is `t a` with `|a| >= k`: take `a = mu p'` with `p'` primitive,
  `|p'| >= k`, and `t p' = p`.  Steinberg commutators
  `[e_il(x^c), e_lj(x^(-c))] = e_ij(1)`, with `l notin {i, j}` possible since
  `r >= 3`, give the constants.  So the normal closure contains all
  elementary matrices, and equals `N`.

(b) Choose `b in N^d` with `h_i^(±1) in x^(-b) M_r(R_+)` for all `i`.  Let `s`
have all entries positive (part 1, §3), and take `k >= 2 max_j b_j`.  For
`gamma = 1 + B in Gamma(m^k)`, the entries of `B` are sums of monomials `x^a`
with `|a| >= k`.  So the entries of `s(B)` are sums of `x^(s a)` with
`(s a)_j >= |a| >= k` for every `j`, and `s(B) in x^(k(1,..,1)) M_r(R_+)`.
Hence

```text
h_i^(-1) s(gamma) h_i = 1 + h_i^(-1) s(B) h_i  in  1 + x^(k(1,..,1) - 2b) M_r(R_+)  <=  M_r(R_+).
```

It has determinant `1`, so it lies in `SL_r(R_+) = EL_r(R_+) = Gamma` (Suslin).
So `Lambda = s(Gamma(m^k)) <= h_i Gamma h_i^(-1)`, i.e. `Lambda` fixes
`h_i Gamma`.  Also `Lambda <= s(Gamma) <= Gamma`.  `Lambda` is a conjugate of
`Gamma(m^k)`, so (a) passes to it.  ∎

## 3. The theorem

**Theorem 7.**  Let `rho : W -> prod_omega (U(1) wr S_(n_m))` be any
homomorphism.  Then `rho(K_even) = 1`.  So `rho` factors through
`W_N = W / K_even`, and

```text
∩ { ker rho : rho a monomial HS model of W }  =  K_even  =  Rad_sof(W).
```

*Proof.*  For `h in N` put `f(h) = rho(e_Gamma + e_(h Gamma))`.  It depends only
on `h Gamma`.  By part 1 Lemma 1 it is a diagonal self-adjoint unitary, and
the values commute because `K_even` is abelian.
- *Transport.*  Fix `h, h' in N`.  By Lemma 6(b) some infranormal Kazhdan
  `Lambda` with `<<Lambda>>_G = N` fixes `Gamma` and `h' Gamma`.  So
  `a = e_Gamma + e_(h' Gamma)` commutes with `Lambda`.  It has trivial
  permutation part (Lemma 1), and `G` is residually finite, hence sofic.
  Theorem M with `n = h` gives `rho(e_(h Gamma) + e_(h h' Gamma)) = f(h')`.
- *Homomorphism.*  In `P`,
  `e_Gamma + e_(h h' Gamma) = (e_Gamma + e_(h Gamma)) + (e_(h Gamma) + e_(h h' Gamma))`.
  So `f(h h') = f(h) f(h')`, and `f` is a homomorphism from `N` into an abelian
  group.
- *Perfectness.*  `N = EL_r(R)` is perfect for `r >= 3`, since
  `e_ij(p) = [e_il(p), e_lj(1)]`.  So `f = 1`.
- *Conclusion.*  The pairs `e_Gamma + e_(h Gamma)` span the fibre-even
  configurations on `N/Gamma`.  Conjugating by `G`, and using that `ker rho` is
  normal, `rho` kills the fibre-even configurations on every fibre, which
  span `K_even`.

For the displayed equality, the right side is contained in the left.
`W_N` is residually finite
(`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`, part 2), so its
permutation models, which are monomial models, separate its points.  ∎

**Corollary 8.**
(a) No monomial HS model of `W` is injective.  `W` has no regular monomial HS
    model, and no regular HS microstates approximately normalizing a full masa
    (part 1, Corollary 4(b)).
(b) For every `G`-submodule `U <= K_even`, every monomial HS model of `W/U`
    kills `K_even/U`.  The proof is the same: Lemma 1 uses Theorem A of
    `research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md`, and
    Theorem M is applied to the images of pairs.  So the intermediate coset
    wreaths `W_K`, `Gamma <= K <= N`, and all lamp quotients inside the
    radical behave the same way.

## 4. Remarks

- *The phases add nothing.*  For `W`, a model with `U(1)` phases cannot see a
  single lamp configuration that no permutation model sees.  This is the exact
  answer to the partly-soft question: the soft lamps are always all of
  `K_even`, and a model is always trivial on them.
- *Where 4.1 is used, and where permutations are.*  Kun--Thom 4.1 is applied
  only to the genuine sofic representation `psi × lambda`.  Permutation
  structure enters only through (HC), which makes the permutation part a
  homomorphism, and (COV), which makes diagonal covariance phase-blind.  No
  monomial extension of the Kun--Thom counting argument is needed.
- *The general mechanism.*  Theorem M plus a supply of infranormal Kazhdan
  subgroups fixing soft elements plus perfectness of the normal closure.  The
  congruence subgroups supply what `Gamma` alone cannot: `Gamma` fixes at most
  one coset per fibre, while deep congruence conjugates fix any finite set.
- *Scope.*  Block size `k >= 2` is not covered, since (COV) fails inside
  blocks.  The trust surface of arXiv:2608.06222 travels through
  `normal-closure-fixes-gamma-fixed-algebra`.
