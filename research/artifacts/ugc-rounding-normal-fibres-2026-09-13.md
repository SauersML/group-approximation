# Galois games, part 3: normal fibres round linearly over M-groups; free subgroups fail for non-normal fibres

Date: 2026-09-13. Lane `ex-ugc-rounding-pgroups`. Continues
`research/artifacts/ugc-galois-games-2026-09-12.md` (Theorems 1--4, formula
(3.1)) and `research/artifacts/ugc-galois-games-part2-2026-09-12.md`
(Theorems 7, 8, 10). Status: complete proofs of Lemma 11, Lemma 12a,
Theorem 12, Proposition 13 and Theorem 14 below. The sequel removes the
monomial hypothesis of Theorem 12. **No bearing on the truth of UGC is
claimed.**

## 0. Summary

The open question `free-subgroup-rounding-is-universal-at-bounded-exponent`
asks for `C(m)` such that, for every finite `G` of exponent `m`, every `K <= G`
and every symmetric conjugation-invariant `mu`, `SDP Gal(G,K,mu) >= 1 - eps`
yields `H` acting freely on `G/K` with `mu(G \ H) <= C(m) eps log k`.

* **For non-normal `K` the answer is no** (Proposition 13). At exponent `4`,
  with `k = 2`, the best free subgroup loses `N` times more than `eps`, while
  the value is still `1 - O(eps)` by permutable rounding.
* **For normal `K` over M-groups the answer is yes** (Theorem 12), with the
  abelian constant of Corollary 9: `C(m) = 3/(1 - cos(2 pi/m))`, and `log_q k`
  with `q` the least prime divisor of `k`. Every nilpotent group, in particular
  every `p`-group, is an M-group (Lemma 12a). Large irreducible
  representations cost nothing.
* **The mechanism.** Theorem 7 used kernels of the irreducibles carrying the
  certificate, and paid their dimension. Use instead the kernel of the linear
  character that *induces* the irreducible. For conjugation-invariant `mu`,
  the normalized character of an induced representation has exactly the
  `mu`-value of its inducing character (Lemma 11). No dimension appears.
* **For arbitrary `K`** the same subgroups give free-subgroup rounding at an
  extra factor `r = [G : N_G(K)]`, the number of conjugates of `K`
  (Theorem 14). Proposition 13 shows this factor is necessary.

The p-group search the lane was asked to run is therefore settled by proof:
large irreducibles of `p`-groups never obstruct subgroup rounding for normal
fibres, because they are monomial.

## 1. Lemma 11: induced certificates

For a representation `rho` of `G` and a measure `mu` put
`lambda_rho(mu) = sum_g mu(g) chi_rho(g)/d_rho`.

**Lemma 11.** Let `mu` be a conjugation-invariant probability measure on `G`,
`H <= G`, `sigma` a representation of `H`, and `rho = Ind_H^G sigma`. Then

```text
lambda_rho(mu) = sum_(h in H) mu(h) chi_sigma(h)/d_sigma.                      (11.1)
```

If moreover `mu` is symmetric, `G` has exponent `m`, and `sigma = theta` is a
linear character, then

```text
1 - lambda_rho(mu) >= mu(G \ H) + (1 - cos(2 pi/m)) mu(H \ ker theta)
                   >= (1 - cos(2 pi/m)) mu(G \ ker theta).                    (11.2)
```

*Proof.* Extend `chi_sigma` by zero to `chidot_sigma` on `G`. The induced
character formula gives `chi_rho(g) = |H|^-1 sum_(x in G) chidot_sigma(x^-1 g x)`,
and `d_rho = [G:H] d_sigma`. So
`chi_rho(g)/d_rho = |G|^-1 sum_x chidot_sigma(x^-1 g x)/d_sigma`. Sum against
`mu` and substitute `g = x g' x^-1`. Since `mu(x g' x^-1) = mu(g')`, every `x`
contributes `sum_(g') mu(g') chidot_sigma(g')/d_sigma`, which is (11.1).

For (11.2), symmetry of `mu` and `theta(h^-1) = conj theta(h)` make
`lambda_rho` real, so
`1 - lambda_rho = sum_g mu(g) (1 - Re thetadot(g))`. The summand is `1` off `H`
and `0` on `ker theta`. On `H \ ker theta`, `theta(h)` is an `m`-th root of
unity other than `1`, so the summand is at least `1 - cos(2 pi/m)`. Finally
`1 >= 1 - cos(2 pi/m)`. `square`

**Remark (the stability lemma of the open node).** `thetadot(g)` is the matrix
coefficient `<rho(g) e_H, e_H>` of the basis vector `e_H` of the induced module.
So (11.1) says that, against conjugation-invariant noise, the class-averaged
certificate `chi_rho/d_rho` is exactly as good as the single vector `e_H`. The
elements fixing `e_H` form the subgroup `ker theta`, and (11.2) is Markov for
that one vector. This is the stability statement asked for in the open node's
Attempts ("a vector almost fixed by `mu`-most elements yields a subgroup of
large mass"), in the monomial case.

## 2. Theorem 12: normal fibres over M-groups

A finite group is an **M-group** if each irreducible representation is induced
from a linear character of some subgroup.

**Lemma 12a.** Every finite nilpotent group is an M-group.

*Proof.* First let `G` be a `p`-group, and argue by induction on `|G|`. Let
`chi` be irreducible and non-linear. Replacing `G` by `G/ker chi` (inducing
data lift), we may assume `chi` is faithful, so `G` is non-abelian. Let `A` be
a maximal abelian normal subgroup. Then `C_G(A) = A`: otherwise
`C_G(A)/A` is a nontrivial normal subgroup of the `p`-group `G/A`, so it meets
`Z(G/A)` nontrivially. Pick `xA` of order `p` there. Then `<A, x>` is abelian,
because `x` centralizes `A`, and normal, because `<A,x>/A` is central. This
contradicts maximality. By Clifford's theorem,
`chi|_A = e (theta_1 + ... + theta_s)` over one `G`-orbit of linear characters.
If `s = 1`, `A` acts by scalars; faithfulness puts `A` in `Z(G)`, so
`G = C_G(A) = A` is abelian, a contradiction. So `s > 1`, and the inertia
group `I` of `theta_1` is proper. By the Clifford correspondence
`chi = Ind_I^G psi` with `psi` irreducible for `I`. By induction `psi` is
induced from a linear character, and so is `chi` (induction in stages).

A nilpotent group is the direct product of its Sylow subgroups. Its
irreducibles are tensor products `chi_1 x ... x chi_r` of irreducibles of the
factors. If `chi_i = Ind_(H_i) theta_i`, then the tensor product is
`Ind_(H_1 x ... x H_r)(theta_1 x ... x theta_r)`. `square`

Supersolvable groups are also M-groups (Huppert) [recalled; not used below].

**Theorem 12.** Let `G` be finite of exponent `m`, `K` a normal subgroup of order
`k`, `q` the least prime dividing `k`, and `mu` symmetric and
conjugation-invariant. Let `phi` be admissible in (3.1) with
`sum_g mu(g) phi(g) >= 1 - eps`; for instance `SDP Gal(G,K,mu) >= 1 - eps`
supplies one (Theorem 3). Suppose each irreducible `rho` with
`lambda_rho >= 1 - 3 eps` is monomial, which holds when `G` is an M-group,
in particular when `G` is nilpotent. Then there are `t <= log_q k` subgroups
`L_1, ..., L_t`, each a conjugate of the kernel of a linear character of a
subgroup of `G`, whose intersection `L` satisfies `L cap K = {e}` and

```text
mu(G \ L) <= 3 t eps/(1 - cos(2 pi/m)) <= 3 eps log_q k/(1 - cos(2 pi/m)).       (12.1)
```

So `L` acts freely on `G/K`, and `val Gal(G,K,mu) >= 1 - 3 eps log_q k/(1 - cos(2 pi/m))`.

*Proof.* (i) **Good isotypic components.** As in Theorem 7 (i)--(ii), split
the GNS vector of `phi` into isotypic components with weights `w_rho`. Then
`sum_rho w_rho (1 - lambda_rho) <= eps`. Put
`calG = { rho : w_rho > 0, lambda_rho >= 1 - 3 eps }`. On
`K cap (intersection over calG of ker rho)` the certificate has
`Re phi >= 1/3`. Since `phi` vanishes on `K \ {e}`, that intersection is `{e}`.

(ii) **Kernels of the inducing characters.** Write `rho = Ind_(H_rho)^G theta_rho`
for `rho in calG`. An element `g` acts trivially on the induced module iff it
fixes every basis vector `e_(xH)` with eigenvalue `1`, that is iff
`x^-1 g x in ker theta_rho` for all `x`. So
`ker rho = intersection over x in G of x (ker theta_rho) x^-1`. Hence for every
`a notin ker rho` some conjugate `x (ker theta_rho) x^-1` omits `a`.

(iii) **The chain.** Put `N_0 = K`. While `N_(i-1) != {e}`, pick
`a in N_(i-1) \ {e}`. By (i) some `rho in calG` has `a notin ker rho`. By (ii)
some `L_i = x (ker theta_rho) x^-1` omits `a`. Put `N_i = N_(i-1) cap L_i`.
It is a proper subgroup of `N_(i-1)`, so `|N_i| <= |N_(i-1)|/q`. After
`t <= log_q k` steps, `K cap L = N_t = {e}`.

(iv) **Cost.** By conjugation invariance,
`mu(G \ L_i) = mu(G \ ker theta_rho)`. By (11.2) this is at most
`(1 - lambda_rho)/(1 - cos(2 pi/m)) <= 3 eps/(1 - cos(2 pi/m))`. The union
bound over `i` gives (12.1).

(v) **Freeness.** `K` is normal, so `L cap x K x^-1 = L cap K = {e}` for all
`x`. Theorem 8 gives the value bound. `square`

**Sharpness.** Khot--Vishnoi (Proposition 6) attains `1 - val = Theta(eps log k)`,
so the `log k` factor is necessary. Proposition 5 (`Z_(2n)`) shows that some
dependence on `m` is necessary. Theorem 7 paid `d_(rho_1) + ... + d_(rho_t)`
where Theorem 12 pays `t`.

**Checks against the open node's tests.**

* *Extraspecial `2^(1+2n)`, `K = Z(G)`.* The big irreducible is
  `Ind_A theta` with `A` maximal abelian and `theta(z) = -1`. For
  non-central `a in A`, `mu(a) = mu(az)` and `theta(az) = -theta(a)`, so
  (11.1) returns `lambda = mu(e) - mu(z)`, as in the node.
  Here `ker theta cap Z = {e}`.
* *`Q_8`, `K = {1,-1}`, `mu = (1-delta) delta_e + delta` uniform on `{i,-i}`.*
  The 2-dimensional irreducible is `Ind_(<i>) theta` with `theta(i) = sqrt(-1)`,
  so `lambda = 1 - delta`, `SDP = 1 - delta/2`, `ker theta = {e}`, and
  `mu(G \ L) = delta = 2 eps <= 3 eps`. Every nontrivial subgroup of `Q_8`
  contains `-1`, so `L = {e}` is optimal. The transversal `{1,i,j,k}` shows
  `val = 1 - delta/2`.

## 3. Proposition 13: free subgroups fail for non-normal fibres

Let `n >= 1`, `N = 2^n`, and let `P = F_2^n` act on the index set `F_2^n` by
translation. Put `B = F_2^N` (coordinates indexed by `F_2^n`) and
`G = B x| P = F_2 wr F_2^n`. It has exponent `4`, since
`(b,t)^2 = (b + t.b, 0)` lies in `B`. Let `e_j` be the coordinate vectors,
`K = <e_0>` (so `k = 2`), and let `mu_delta` be the law of independent
coordinate flips with probability `delta`, supported on `B`. It is symmetric,
and conjugation-invariant because `B` is abelian and `P` permutes coordinates.
The conjugates of `K` are the `N` subgroups `<e_j>`, so `K` is not normal.

**Proposition 13.** (a) `SDP Gal(G,K,mu_delta) >= 1 - delta` and
`val Gal(G,K,mu_delta) >= 1 - delta`.
(b) Every `H` acting freely on `G/K` has
`mu_delta(G \ H) >= N delta (1 - delta)^(N-1)`.
(c) Take `delta = N^-2` and `eps = delta`. Every free `H` has
`mu(G \ H) >= (N - 1) eps log_2 k`. So no `C(4)` exists, and
`free-subgroup-rounding-is-universal-at-bounded-exponent` is false as stated.

*Proof.* (a) `L = { b in B : b_0 = 0 }` meets `K` trivially. Both lie in the
abelian group `B`, so `KL = B` is a subgroup, and `mu_delta(L) = 1 - delta`.
Theorem 10(a) gives the SDP bound and Theorem 10(b) the value bound.
(b) `H` acts freely iff it meets every conjugate `<e_j>` trivially, i.e.
contains no `e_j`. So `mu(G \ H) >= sum_j mu(e_j) = N delta (1 - delta)^(N-1)`.
(c) Bernoulli's inequality gives `N (1 - N^-2)^(N-1) >= N - (N-1)/N > N - 1`.
`square`

So "acts freely on `G/K`" is the wrong target for non-normal fibres: the value
is `1 - O(eps)` through a permutable subgroup that is not free. The
irreducible-kernel rounding of Theorem 7 is tight here: the certificate lives on
`Ind_B^G chi_(e_0)`, of dimension `N`, whose inducing kernel is `L`.

## 4. Theorem 14: free-subgroup rounding pays the number of conjugates

**Theorem 14.** Keep the hypotheses of Theorem 12, except that `K <= G` is
arbitrary. Put `r = [G : N_G(K)]`. Then some `H` acting freely on `G/K` has

```text
mu(G \ H) <= 3 eps r log_q k/(1 - cos(2 pi/m)).                                  (14.1)
```

*Proof.* Let `K_1, ..., K_r` be the conjugates of `K`. Each `ker rho` is normal,
so step (i) of Theorem 12 gives `K_j cap (intersection over calG of ker rho) = {e}`
for every `j`. Run the chain of step (iii) on `K_1`, then continue it on
`K_2 cap L`, and so on. Each step divides one of the orders `|K_j cap L|` by at
least `q`, so there are at most `r log_q k` steps. The final `L` meets every
conjugate of `K` trivially, and step (iv) bounds the cost. `square`

In Proposition 13, `r = N` and `k = 2`, and the best free subgroup costs at least
`(N-1) eps`. So (14.1) is tight up to the constant.

## 5. What this says for rounding

* **Normal fibres.** A Galois game with normal `K` is `Max-2Lin(K)` on a Cayley
  graph of `G/K`, with constraints given by the extension `K -> G -> G/K`. Over
  nilpotent groups of bounded exponent the basic SDP loses at most
  `O_m(eps log k)`, exactly as over abelian groups, however large the
  irreducibles carrying the certificate are. Such symmetric instances are gap
  instances only in the Khot--Vishnoi regime `eps log k -> infinity`.
* **The rounding is structured.** Take the good isotypic components of the
  certificate, write each as induced from a linear character, and intersect at
  most `log_q k` conjugates of the inducing kernels. The output labeling is the
  orbit-representative transversal of Theorem 8.
* **Non-normal fibres.** Free subgroups are not enough, and the loss of the
  natural free rounding grows with the number of conjugates of `K`. Whether the
  *value* still rounds linearly for arbitrary `K` at bounded exponent is open;
  in Proposition 13 it does, through a permutable subgroup.

## 6. Scope and literature (bounded)

Lemma 11 is the induced character formula applied to a class function, and
Lemma 12a is the textbook fact that `p`-groups are M-groups. I did not look for
Theorem 12 or Proposition 13 in the literature beyond the searches recorded in
`research/artifacts/ugc-galois-games-2026-09-12.md` Section 7. No novelty is
claimed beyond that check.
