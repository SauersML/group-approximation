---
rg: 2
id: fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2-proof
kind: route
title: Pushing kernel products to the quotient, FKG insertion on cosets and Kesten diagonal powers identify the relative Russo-BK radius with the quotient critical operator norm
target: fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2
requires:
  - fpbs-bk-majorant-integrated-sensitivity-is-critical-l2
  - fpbs-fibre-summed-connectivity-operator
  - fpbs-relative-gap-along-any-subgroup-separates
  - fpbs-critical-l2-implies-nonuniqueness
---

Complete written proof. No computation is used. Notation as in the claim.

**Imports.**

- `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2` (ESTABLISHED),
  through its proof route: Step 1 (FKG insertion), the Lemma of Step 3
  (operator norm from diagonal powers), and Step 4e, which states verbatim:
  "`tau_(p_c+delta)(o,x) <= sum_k (d delta)^k [T(PT)^k](o,x)`". It is proved
  there for `d delta M<1` with `M=||T_(p_c)||<infinity` and `p_c+delta<=1`.
- `fpbs-fibre-summed-connectivity-operator` (ESTABLISHED), verbatim:
  "`||T_p||_{l2(Gamma) -> l2(Gamma)}  <=  ||S_p||_{l2(Q) -> l2(Q)}     (in [0, infinity])`".
- `fpbs-relative-gap-along-any-subgroup-separates` (ESTABLISHED), verbatim:
  "the following are equivalent, and each implies `p_c(G) < p_u(G)`:
  1. `p_c(G) < p_c(I;G)`; 2. `chi^I_p < infinity` for some `p > p_c(G)`."
- Harris-FKG, as imported in the BK-majorant proof route.
- Duminil-Copin and Tassion, *A new proof of the sharpness of the phase
  transition for Bernoulli percolation and the Ising model*, Comm. Math.
  Phys. 343 (2016). With `phi_p(S) = p sum_{(x,y) in ∂_E S} P_p(o <-> x in S)`
  for a finite set `S` containing `o`, they prove `p_c = sup{p : phi_p(S)<1
  for some finite S containing o}`.
- Følner's criterion for amenability of `Q`.
- `fpbs-critical-l2-implies-nonuniqueness` (ESTABLISHED, Hutchcroft's
  published sufficient condition): critical L2 boundedness
  `||T_(p_c)||<infinity` implies a nonuniqueness interval, so `p_c<p_u`.
  It is used only for the consequence sentence of part (2).

All functions on `Q` or `Gamma` are nonnegative. Convolutions
`(f*g)(q)=sum_(r) f(r) g(r^(-1) q)` take values in `[0,infinity]`. They are
associative and entrywise monotone in each factor, by Tonelli.

We write `tau(z)=tau_(p_c)(o,z)` and `u=1_S/d`. By invariance the kernels are
`T(x,y)=tau(x^(-1)y)` and `P(x,y)=u(x^(-1)y)`, and a kernel product
evaluated at `(o,x)` is a convolution on `Gamma`:
`(K L)(o,x)=sum_y k(y) l(y^(-1)x)=(k*l)(x)`.

## Step 1. Pushforward is a convolution homomorphism (part 1)

For nonnegative `f` on `Gamma` put `(pi_* f)(q)=sum_(x in q) f(x)`. For
nonnegative `f,g`, Tonelli gives

```text
pi_*(f*g)(q) = sum_y f(y) sum_(x in q) g(y^(-1)x) = sum_y f(y) (pi_* g)(pi(y)^(-1) q)
             = sum_(r in Q) (pi_* f)(r) (pi_* g)(r^(-1) q).
```

The second equality holds because `x -> y^(-1)x` is a bijection from the
coset `q` onto the coset `pi(y)^(-1)q`, since `N` is normal. Since
`pi_* tau = sigma` and `pi_* u = mu_Q`, we get
`pi_*[tau*(u*tau)^(*k)] = sigma*(mu_Q*sigma)^(*k)`. Evaluating at `e`, whose
coset is `N`, gives `B^(k) = [sigma*(mu_Q*sigma)^(*k)](e)`. ∎

## Step 2. Three properties of sigma_p

Fix `p in (0,1]`.

**(2a) Symmetry.** `sigma_p(q^(-1))=sigma_p(q)`. Indeed
`tau_p(o,x^(-1))=tau_p(x,o)=tau_p(o,x)` by invariance and symmetry, and
`x -> x^(-1)` maps `q` bijectively onto `q^(-1)`.

**(2b) Coset insertion.** Step 1a of the imported route gives, entrywise,
`P T_p >= p T_p` and `T_p P >= p T_p`. In convolution form these read
`u*tau_p >= p tau_p` and `tau_p*u >= p tau_p`. Pushing forward with Step 1
(monotone) gives `mu_Q*sigma_p >= p sigma_p` and `sigma_p*mu_Q >= p sigma_p`.
Hence, by monotonicity of convolution,

```text
sigma_p*(mu_Q*sigma_p)^(*k) >= p^k sigma_p^(*(k+1))          (k>=0).        (2.1)
```

**(2c) Spreading along the quotient.** Let `|q|_Q` be the word length of `q`
in the generators `pi(S)`. Then `sigma_p(q) >= p^(|q|_Q) sigma_p(e)`. Indeed,
write `q=pi(s_1...s_m)` with `m=|q|_Q` and `g=s_1...s_m`. The map `z -> zg`
maps `N` bijectively onto `Ng=q`. For `z in N`, the event `{o<->zg}` contains
the intersection of `{o<->z}` with the event that the path
`z, zs_1, ..., zg` is open. Harris-FKG gives `tau_p(o,zg) >= p^m tau_p(o,z)`.
Summing over `z in N` gives the claim.

## Step 3. Majorant forces quotient critical l2 (part 2)

Let `sigma=sigma_(p_c)` and suppose `M^N(delta)<infinity` for some
`delta>0`. By Step 1 and (2.1),
`M^N(delta) >= sum_k (d delta p_c)^k sigma^(*(k+1))(e)`, so

```text
sigma^(*(k+1))(e) <= (d delta p_c)^(-k) M^N(delta)        (k>=0).       (3.1)
```

**Lemma (diagonal powers on Q).** Let `K(q,r)=sigma(q^(-1)r)`. This is the
kernel of `S_(p_c)`, since `(f*sigma)(q)=sum_r f(r) sigma(r^(-1)q)
=sum_r K(q,r) f(r)` by (2a). Then
`||S_(p_c)||=limsup_m (sigma^(*m)(e))^(1/m)` in `[0,infinity]`.

*Proof.* `K` is nonnegative, symmetric by (2a), invariant under left
translation by `Q`, and `K(e,e)=sigma(e)>=1`. Also `K^m(e,e)=sigma^(*m)(e)`.
The proof of the Lemma in Step 3 of the imported route uses only these
properties of a kernel on a countable group acting on itself by left
translation. It is: even trace powers of finite sections `1_F K 1_F` give
`||K_F||^m <= |F| K^m(e,e)`, and `<K^m delta_e,delta_e> <= ||K||^m`. So the
proof applies verbatim with `Gamma` replaced by `Q`. ∎

By the Lemma and (3.1),
`||S_(p_c)|| <= limsup_k ((d delta p_c)^(-k) M^N(delta))^(1/(k+1)) = 1/(d delta p_c)`.
The import `fpbs-fibre-summed-connectivity-operator` gives
`||T_(p_c)|| <= ||S_(p_c)||`. This proves the displayed chain of part (2).
The consequence `p_c<p_u` is `fpbs-critical-l2-implies-nonuniqueness`. ∎

## Step 4. Quotient critical l2 gives the majorant and the gap (part 3)

Assume `||S_(p_c)||=M_Q<infinity`. By the import
`fpbs-fibre-summed-connectivity-operator`, `M=||T_(p_c)|| <= M_Q`. Let
`0<delta<1/(d M_Q)` with `p_c+delta<=1`. Then `d delta M<1`, and imported
Step 4e gives, entrywise,
`tau_(p_c+delta)(o,x) <= sum_k (d delta)^k [T(PT)^k](o,x)`. Summing over
`x in N` (Tonelli) gives `chi^N_(p_c+delta) <= M^N(delta)`.

**Series bound.** Let `R_f h = h*f` be right convolution, so that
`R_sigma = S_(p_c)` has norm `M_Q`, and `R_(mu_Q)` has norm at most
`||mu_Q||_1=1` by Young's inequality. For nonnegative `h in l2(Q)` and
nonnegative `f` with `R_f` bounded, `R_f h` is computed by sums of
nonnegative terms and lies in `l2(Q)`. So, by associativity,

```text
B^(k) = (delta_e * sigma * mu_Q * ... * sigma)(e) = <R_sigma (R_(mu_Q) R_sigma)^k delta_e, delta_e> <= M_Q^(k+1).
```

Hence `M^N(delta) <= M_Q/(1-d delta M_Q)`.

**Gap.** Nonamenable Cayley graphs have `p_c<1` (Benjamini-Schramm,
*Percolation beyond Z^d*, Electron. Comm. Probab. 1 (1996), Thm 2:
`p_c <= 1/(1+h)` with `h>0` the edge Cheeger constant). So some admissible
`delta>0` exists, and `chi^N_p<infinity` for `p=p_c+delta>p_c`. The import
`fpbs-relative-gap-along-any-subgroup-separates` (2 => 1, with `I=N`, which is
infinite) gives `p_c(G)<p_c(N;G)`.

**Radius.** Let `delta^N_* = sup{delta>=0 : M^N(delta)<infinity}`. The series
bound gives `delta^N_* >= 1/(d M_Q)`. Part (2) gives `M_Q <= 1/(d delta p_c)`
whenever `M^N(delta)<infinity`, so `delta^N_* <= 1/(d p_c M_Q)`. If
`M_Q=infinity`, part (2) gives `M^N(delta)=infinity` for every `delta>0`, so
`delta^N_*=0`. ∎

## Step 5. One-factor vacuity under relative collapse (part 4)

Assume `p_c(G)=p_c(N;G)` and let `s>p_c`. If `chi^N_s<infinity`, the import
`fpbs-relative-gap-along-any-subgroup-separates` (2 => 1) would give
`p_c(G)<p_c(N;G)`. So `sigma_s(e)=chi^N_s=infinity`, and by (2c),
`sigma_s(q) >= s^(|q|_Q) · infinity = infinity` for every `q`.

Let `F=f_1*...*f_m` with each `f_i in {delta_e, mu_Q, sigma_q : q in [0,1]}`
and `f_j=sigma_s`, `s>p_c`. Each factor is nonnegative and not identically
zero, and a convolution of such functions is not identically zero, because
`(f*g)(ab) >= f(a)g(b)`. Put `L=f_1*...*f_(j-1)` and `R=f_(j+1)*...*f_m`
(empty products are `delta_e`). Choose `a,b` with `L(a)>0` and `R(b)>0`. Then

```text
F(e) = sum_(a',b') L(a') sigma_s(a'^(-1) b'^(-1)) R(b') >= L(a) R(b) sigma_s(a^(-1) b^(-1)) = infinity.
```

**Picard remainders.** Step 5 of the imported route records the integrated
inequality `tau_q <= T + d int_(p_c)^q T_s P T_s ds`, and its Picard iterates
replace factors `T_s` by the right-hand side. Summing any term over `x in N`
and using Step 1 (with Tonelli for the `ds`-integrals) turns it into an
integral of values at `e` of convolution products of the kind above. Every
remainder term contains a factor `sigma_s` with `s` ranging over an interval
`(p_c, q')` of positive length. So its integrand is `+infinity` on a set of
positive measure, and the term is `+infinity`. ∎

## Step 6. Amenable quotient (part 5)

**(6a) `chi_(p_c)=infinity`.** Suppose `sum_x tau_(p_c)(o,x)<infinity`. Let
`B_n` be the ball of radius `n`. Each edge of `∂_E B_n` has its inner endpoint
on the sphere `S_n`, and each vertex has at most `d` edges. So
`phi_(p_c)(B_n) <= p_c d sum_(x in S_n) tau_(p_c)(o,x) -> 0`. Choose `n` with
`phi_(p_c)(B_n)<1`. Since `B_n` is finite, `p -> phi_p(B_n)` is a polynomial,
so `phi_p(B_n)<1` for some `p>p_c`. This contradicts the imported
Duminil-Copin--Tassion identity. By monotone convergence,
`||sigma_(p_c)||_1 = chi_(p_c) = infinity`.

**(6b) `||S_(p_c)|| >= ||sigma_(p_c)||_1`.** Let `A` be finite, `sigma^A = sigma 1_A`,
and `F` finite with `f=1_F |F|^(-1/2)`. Then

```text
<f*sigma^A, f> = sum_(r in A) sigma(r) |F r ∩ F| / |F|.
```

`Q` is amenable, so it has right Følner sets, i.e. `|Fr ∩ F|/|F| -> 1` for
each `r` (the inverses of left Følner sets). This gives
`||S_(p_c)|| >= sum_(r in A) sigma(r)`, using entrywise monotonicity of the
norm for nonnegative kernels. Letting `A` increase to `Q` gives
`||S_(p_c)||=infinity`. By part (2), `M^N(delta)=infinity` for all `delta>0`. ∎
