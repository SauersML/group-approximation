# Galois games, part 4: a trace gap for primitive representations, and linear rounding for normal fibres over every finite group

Date: 2026-09-13. Lane `ex-ugc-rounding-pgroups`. Continues
`research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md` (Lemma 11,
Theorems 12 and 14, Proposition 13). Status: complete proofs of Theorem 15,
Theorem 16 and Corollary 17. The textbook inputs are Clifford's theorem,
Skolem--Noether for matrix algebras, Burnside's theorem (an irreducible
image spans the full matrix algebra), and the Schur multiplier of a direct
product of perfect groups [recalled]. The classification of finite simple
groups enters only Remark 18, and only for uniformity in `m` over
non-solvable groups. **No bearing on the truth of UGC is claimed.**

## 0. Summary

Theorem 12 needed monomial certificates. Every irreducible is induced from a
*primitive* one, and Lemma 11 reduces the cost to the primitive part. So the
question becomes: in a primitive representation, can a non-scalar element have
normalized trace close to `1`?

* **Theorem 15 (trace gap).** Let `sigma` be an irreducible primitive projective
  representation of a finite group `X`, and let `sigma(h)` be non-scalar. Then
  `|tr sigma(h)| <= gamma(X) dim sigma`. Here `gamma(X) = 2^(-1/2)` when `X` is
  solvable, and in general `gamma(X) = max(2^(-1/2), gamma(T))` over the
  nonabelian simple sections `T` of `X`, where `gamma(T) < 1` is a finite-data
  constant of `T`. The bound `2^(-1/2)` is attained by `GL(2,3)`. The standard
  representation of `S_n` shows that `gamma(A_n) -> 1`.
* **Theorem 16.** For normal `K`, the conclusion of Theorem 12 holds for every
  finite group, with `1 - cos(2 pi/m)` replaced by
  `c(G,m) = min(1 - cos(2 pi/m), 1 - gamma(G))`. For solvable `G` and `m >= 8`
  this is exactly the abelian constant.
* **Corollary 17.** For arbitrary `K`, free-subgroup rounding holds with the
  extra factor `[G : N_G(K)]`, which Proposition 13 shows is necessary.

So `free-subgroup-rounding-is-universal-at-bounded-exponent` is **true for
normal `K`** (uniformly in `m` for solvable groups, and for all groups granted
Remark 18) and **false for non-normal `K`**.

## 1. Theorem 15: primitive projective representations have a trace gap

A projective representation `sigma : X -> GL(V)` satisfies
`sigma(x) sigma(y) in C^x sigma(xy)`. Rescale so every `sigma(x)` is unitary for
a fixed inner product; then `|tr sigma(x)|` is well defined. It is **primitive**
if no decomposition `V = V_1 + ... + V_r` (`r >= 2`) is permuted by all
`sigma(x)`.

For a nonabelian simple group `T` put

```text
gamma(T) = max |tr A| / dim tau,
```

over irreducible projective representations `tau` of `T` with `dim tau >= 2`
and non-scalar unitaries `A` with `A tau(T) A^-1 subset C^x tau(T)`.
**`gamma(T) < 1`.** If `A` and `A'` induce the same automorphism of `T`, then
`A^-1 A'` commutes with each `tau(t)` up to a scalar `lambda(t)`. Such a
`lambda` is a homomorphism `T -> C^x`, and `T` is perfect, so `lambda = 1` and
`A' in C^x A`. There are finitely many `tau` up to equivalence and finitely many
automorphisms, so the maximum runs over finitely many values of `|tr A|`, each
`< dim tau` because `A` is unitary and non-scalar. Put
`gamma(X) = max(2^(-1/2), max gamma(T))` over nonabelian simple sections `T` of
`X`, and `gamma(X) = 2^(-1/2)` if there are none (`X` solvable).

**Theorem 15.** Let `sigma` be an irreducible primitive projective representation
of the finite group `X`, `d = dim sigma`, and `h in X` with `sigma(h)` not
scalar. Then `|tr sigma(h)| <= gamma(X) d`.

*Proof.* Induction on `|X|`. Let `Z = { x : sigma(x) in C^x }`, a normal
subgroup. Since `sigma(h)` is not scalar, `Z != X`. Choose `N` normal in `X` with
`Z < N` and `N/Z` minimal normal in `X/Z`.

(a) **Homogeneity.** The isotypic components of `V` under `N` are permuted by
`sigma(X)`. By primitivity there is only one, so `V = V_tau (x) W`, where `N`
acts as `tau (x) 1` with `tau` irreducible, and `span sigma(N) = End(V_tau) (x) 1`
by Burnside.

(b) **Factorization.** Each `sigma(x)` normalizes `End(V_tau) (x) 1`. By
Skolem--Noether its action there is `Ad(taut(x))` for some unitary `taut(x)`. Then
`(taut(x)^-1 (x) 1) sigma(x)` commutes with `End(V_tau) (x) 1`, so it is
`1 (x) pit(x)`. Hence `sigma(x) = taut(x) (x) pit(x)` and
`tr sigma(h) = tr taut(h) tr pit(h)`. For `n in N`, `pit(n)` is scalar, so `pit` is
a projective representation of `X/N`. It is irreducible, and it is primitive:
a system `W = sum W_i` gives the system `V = sum V_tau (x) W_i` for `sigma`.

(c) **Scalar case.** If `taut(h)` is scalar, then `pit(h)` is non-scalar and
`|tr sigma(h)|/d = |tr pit(h)|/dim W`. Apply induction to `(X/N, pit, hN)`.
Simple sections of `X/N` are simple sections of `X`.

(d) **Non-scalar case.** It suffices to show `|tr taut(h)| <= gamma(X) dim V_tau`.
An element of `N` is scalar on `V_tau` iff it lies in `Z`, so `tau` is a faithful
projective representation of `N/Z`. There are two cases.

**Case A: `N/Z` is elementary abelian of order `p^s`.** Lifts commute up to a
scalar: `tau(x) tau(y) tau(x)^-1 = omega(x,y) tau(y)`. The form `omega` is
bimultiplicative, alternating, `p`-th-root-valued and `X`-invariant. Its radical
is an `X`-invariant subgroup of `N/Z`. If it were all of `N/Z`, then
`span tau(N) = End(V_tau)` would be commutative, so `dim V_tau = 1` and `N <= Z`.
So `omega` is nondegenerate and `s = 2a`. Choose unitary lifts `U_v`,
`v in F_p^(2a)`. For `v != 0`, some `w` has `U_w U_v U_w^-1 = omega U_v` with
`omega != 1`, so `tr U_v = 0`. Since `U_v^* U_w in C^x U_(w-v)`, the `U_v` are
orthonormal for `<A,B> = tr(A^* B)/dim V_tau`. They span `End(V_tau)`, so they form a
basis. Write `A = taut(h) = sum_v c_v U_v`; then `sum |c_v|^2 = 1` and
`tr A/dim V_tau = c_0`. Conjugation by `h` acts on `N/Z` by a linear map `g`, and
`A U_w A^-1 = lambda_w U_(gw)` with `|lambda_w| = 1`.

* If `g = 1`, then `w -> lambda_w` is a character of `F_p^(2a)`, so by
  nondegeneracy it is `omega(v_0, .)` for some `v_0`. Then `U_(v_0)^-1 A`
  commutes with all `U_w`, so `A in C^x U_(v_0)`. As `A` is non-scalar,
  `v_0 != 0` and `tr A = 0`.
* If `g != 1`, compare coefficients of `U_u` in `A U_w = lambda_w U_(gw) A`, using
  `U_v U_w in C^x U_(v+w)` with unimodular constants. This gives
  `|c_(u-w)| = |c_(u-gw)|`, that is, `|c_v| = |c_(v + (g-1)w)|` for all `v, w`.
  So `|c|` is constant on cosets of `Im(g - 1)`, a subgroup of order at least
  `p`. Hence `p |c_0|^2 <= 1` and `|tr A|/dim V_tau <= p^(-1/2) <= 2^(-1/2)`.

**Case B: `N/Z = T_1 x ... x T_s` with `T_i` isomorphic to a nonabelian simple
`T`.** The multiplier of a product of perfect groups is the product of the
multipliers [recalled], so `tau` lifts to a linear representation of a product
of covering groups, and `V_tau = V_1 (x) ... (x) V_s` with
`tau = tau_1 (x) ... (x) tau_s`. Each `dim V_i >= 2`: otherwise `T_i` would act by
scalars and lie in `Z`. The algebras `calA_i = span tau(T_i) = End(V_i)` are
permuted by `Ad A` according to the permutation `pi` that `h` induces on the
`T_i`. They are all isomorphic, of common dimension `d_0^2`. Identify all `V_i`
with `C^(d_0)` and let `P_pi` permute tensor slots. Then `Ad(P_pi^-1 A)` preserves
each factor, hence is a tensor product of inner automorphisms, and
`A in C^x P_pi (A_1 (x) ... (x) A_s)`.

* If `pi != 1`, the trace of `P_pi (A_1 (x) ... (x) A_s)` is a product over the
  cycles of `pi` of traces of products of the `A_i` on one slot. So
  `|tr A| <= d_0^(#cycles) <= d_0^(s-1)`, and the ratio is at most `1/2`.
* If `pi = 1`, some `A_j` is non-scalar, and it normalizes `tau_j(T_j)` up to
  scalars. So `|tr A| <= |tr A_j| d_0^(s-1) <= gamma(T) d_0^s`.

In every case `|tr taut(h)| <= gamma(X) dim V_tau`. `square`

**Sharpness.** `GL(2,3)` has a faithful 2-dimensional irreducible. Its
restriction to `SL(2,3)`, the only subgroup of index 2, is irreducible, so it is
primitive. Elements of order 8 have eigenvalues `zeta_8, zeta_8^3` and
`|tr|/2 = 2^(-1/2)` (Case A with `p = 2` and `rank(g - 1) = 1`).
The standard representation of `S_n` is primitive for `n >= 5` (the only
subgroup of index below `n` is `A_n`, and the restriction to it is irreducible),
and a transposition has `tr/dim = (n-3)/(n-1)`. So no bound uniform over all
finite groups exists; Case B must depend on `T`.

## 2. Theorem 16: normal fibres round linearly over every finite group

**Theorem 16.** Let `G` be finite of exponent `m`, `K` normal of order `k`, `q`
the least prime dividing `k`, `mu` symmetric and conjugation-invariant, and `phi`
admissible in (3.1) with `sum mu phi >= 1 - eps`. Put
`c = c(G,m) = min(1 - cos(2 pi/m), 1 - gamma(G))`. Then there are `t <= log_q k`
conjugates `L_i` of kernels of primitive representations of subgroups, whose
intersection `L` has `L cap K = {e}` and

```text
mu(G \ L) <= 3 t eps / c <= 3 eps log_q k / c(G,m).                               (16.1)
```

So `val Gal(G,K,mu) >= 1 - 3 eps log_q k/c(G,m)`. For solvable `G`,
`c = min(1 - cos(2 pi/m), 1 - 2^(-1/2))`, which equals `1 - cos(2 pi/m)` when
`m >= 8`.

*Proof.* Every irreducible `rho` is `Ind_H^G sigma` with `sigma` a primitive
irreducible representation of some `H`: take `H` minimal among the subgroups
from which `rho` is induced, and use transitivity of induction. By (11.1),

```text
1 - lambda_rho = sum_g mu(g) (1 - Re chidot_sigma(g)/d_sigma).
```

The summand is `1` off `H` and `0` on `ker sigma`. On `H \ ker sigma`, either
`sigma(h) = zeta I` with `zeta != 1` and `zeta^m = 1`, so the summand is at least
`1 - cos(2 pi/m)`, or `sigma(h)` is non-scalar, and then Theorem 15 for `H` gives
`Re chi_sigma(h)/d_sigma <= gamma(H) <= gamma(G)`. So

```text
mu(G \ ker sigma) <= (1 - lambda_rho)/c(G,m).                                    (16.2)
```

The module `Ind sigma` is the sum of the translates `x V_sigma`, and `g` acts
trivially on it iff `x^-1 g x in ker sigma` for all `x`. So `ker rho` is the
intersection of the conjugates of `ker sigma`. Now run steps (i), (iii), (iv) and
(v) of Theorem 12 with `ker theta_rho` replaced by `ker sigma_rho` and (11.2)
replaced by (16.2). `square`

**Corollary 17 (arbitrary `K`).** Under the hypotheses of Theorem 16 without
normality, some `H` acting freely on `G/K` has
`mu(G \ H) <= 3 eps [G : N_G(K)] log_q k / c(G,m)`.

*Proof.* Theorem 14's proof, with (16.2) in place of (11.2). `square`

**Remark 18 (uniformity in `m`) [uses CFSG; recalled].** For each `m` only
finitely many nonabelian finite simple groups have exponent dividing `m`:
`A_n` contains an element of order at least `n - 1`, groups of Lie type contain
elements whose order grows with the field size and the rank, and there are 26
sporadic groups. Hence `gamma_m = sup { gamma(G) : exp G | m } < 1`, and
Theorem 16 gives `C(m) = 3/min(1 - cos(2 pi/m), 1 - gamma_m)` for every finite
group of exponent `m`. Without the classification, the constant is uniform in `m`
over solvable groups, and over any class of groups whose nonabelian simple
sections come from a fixed finite list.

## 3. What either answer means for rounding

* **Normal fibres: linear rounding is universal at bounded exponent.** A Galois
  game with normal `K` is `Max-2Lin(K)` on a Cayley graph of `G/K`, with
  constraints coming from the extension `K -> G -> G/K`. With conjugation-invariant
  noise its basic SDP rounds to `1 - O_m(eps log k)`, over every finite group,
  however large the irreducibles carrying the certificate are. The rounding
  intersects at most `log_q k` conjugates of primitive inducing kernels and outputs
  the orbit-representative transversal of Theorem 8. Symmetric quotient
  constructions with normal fibres therefore separate SDP from value only in the
  Khot--Vishnoi regime `eps log k -> infinity`. This is the same as over `F_2^N`:
  non-abelian symmetry of bounded exponent adds no integrality gap.
* **Where square-root loss can come from.** The loss can grow only through
  `1/c(G,m)`: long cycles (`1 - cos(2 pi/m)` small, Proposition 5) or large
  alternating sections (`gamma(A_n) -> 1`). The `S_N` example in
  `free-subgroup-rounding-is-universal-at-bounded-exponent` is the second
  mechanism, and there point stabilizers still round.
* **Non-normal fibres.** The natural free rounding pays `[G : N_G(K)]`, and
  Proposition 13 shows free subgroups cannot avoid that. Whether the *value* of a
  symmetric Galois game rounds linearly for every fibre at bounded exponent is
  open (`galois-games-round-linearly-for-every-fibre-at-bounded-exponent`).
* **Relation to `smooth-design-rich-2to1-hardness`.** Nothing here bears on the
  truth of SD-Rich. It does restrict one design choice. A dictatorship-style test
  whose label-extended graph is a Cayley graph of a bounded-exponent group, with
  normal folding subgroup and conjugation-invariant noise, is a symmetric Galois
  game. By Theorem 16, SDP value `1 - eps` forces value `1 - O_m(eps log k)`. So
  such a test cannot exhibit an integrality gap unless `eps log k -> infinity`,
  whatever non-abelian group replaces `F_2^N`. The proved 2-to-2 instances are
  2-to-2 rather than unique games, and their `GL_n(F_2)`-type symmetry has
  unbounded exponent, so they are outside this scope.
* **SoS at completeness one half.** Theorem 16 concerns completeness near `1` and
  is vacuous at `1/2`. I found nothing that bears on
  `sos-cannot-refute-unique-games-at-completeness-one-half`.

## 4. Literature (bounded)

Theorem 15 is a density analogue of Blichfeldt's theorem that, in a finite
primitive linear group, an element whose eigenvalues lie in an arc of length less
than `pi/3` is scalar [recalled]. Blichfeldt constrains *all* eigenvalues; Theorem
15 constrains the *average*, which is what Markov-type rounding needs. Bounds on
`dim [V,g]` for primitive linear groups are also classical (Hall--Liebeck--Seitz,
1992 [recalled; not read]). I did not locate Theorem 15 in this form. The check
was limited to recall, and no novelty is claimed for it.
