# Learnability of pairing designs and the reach of test transparency

Date: 2026-09-11. Status: complete proofs of Theorems 1 and 2. **Neither
proves nor disproves the Unique Games Conjecture.** No proof-assistant
verification or priority claim is made. Author: fork `ugc-2`.

Notation follows
[unique-games-bkm-test-transparency-2026-09-11.md](unique-games-bkm-test-transparency-2026-09-11.md):
`Psi` is a regular 2-to-1 game with left alphabet `[2n]` and right alphabet `[n]`;
`P_e` is the fiber matching of edge `e`; `R_(rho,m)` is the folded long-code noise
test of Braverman--Khot--Minzer (ITCS 2021, Section 5); `K_rho` is the noise
kernel. For a matching `P`, a *noisy pullback* is `x = K_rho(A)`, where `A` is
uniform on `P`-pair-constant vectors in `Z_m^(2n)`.

## 1. Question

Transparency (`bkm-test-transparent-on-learnable-games`) says the test adds no
soundness on instances whose edge matchings can be decoded from one noisy
pullback. Pullback smoothness forces a family to have at least about `m^n`
members (lane `ugc-1`, Theorem C of the smooth-design artifact). The question
asked here is whether exponentially large smooth designs are still learnable,
and what a hardness source has to avoid. Two results answer it.

- **Theorem 1 (coarsening transparency).** Transparency does not need the whole
  matching, only a decodable *feature* of it. The test is no sounder than the
  game split along any decodable feature.
- **Theorem 2 (random exponential families are unlearnable).** Families of
  independent uniform pairings with `M >> (1+rho^2(m-1))^n` members defeat every
  list decoder, exponentially fast. Random smooth designs, and their
  compositions with permutation designs, therefore escape the member-level
  transparency barrier.

## 2. Theorem 1: coarsening transparency

Fix, at each left vertex `u`, a partition `c_u` of the matchings occurring at
`u` into classes, and a decoder `D_u : Z_m^(2n) -> classes` that is invariant
under `x -> x + t 1`. Write `e_c` for the largest probability, over `u` and over
edges `e` at `u`, that `D_u` fails to return the class of `P_e` on a noisy
pullback of `P_e`.

The **coarsened game** `Psi_c` has left vertices `(u,K)` for the classes `K` at
`u`, left alphabet `[2n]`, the right side of `Psi`, and one edge `((u,K_e),v)`
for each edge `e=(u,v)`, where `K_e` is the class of `P_e`, with constraint
`pi_e`. Then `val(Psi) <= val(Psi_c) <= val(UG_der(Psi))`. The first inequality
uses the labeling `a(u,K)=a(u)`. The second labels `(u,P)` by the pair of `P`
containing `a(u,K_P)`.

**Theorem 1.** For every `m >= 2` and `0 < rho < 1`,

```text
val(R_(rho,m)(Psi)) >= 1/m + (1-1/m) rho^3 val(Psi_c)^2 - 2 e_c.
```

*Proof.* Fix an optimal labeling `a(u,K)`, `beta(v)` of `Psi_c` and put
`F_u(x) = x_(a(u, D_u(x)))`. This is folded because `D_u` is shift invariant.
Condition on `v,u,w`. The ideal outputs `I = x_(a(u,K_(u,v)))` and
`J = y_(a(w,K_(w,v)))` read right coordinates `pi_(u,v)(a(u,K_(u,v)))` and
`pi_(w,v)(a(w,K_(w,v)))`.

- If both coarsened edges are satisfied, both coordinates equal `beta(v)`, and
  `Pr[I=J] = 1/m + (1-1/m) rho^3` by composition of three symmetric kernels.
- Otherwise the probability is at least `1/m`.

`F_u(x) != I` only when `D_u(x)` fails, which has probability at most `e_c`; the
same holds for `y`. Independence of `u` and `w` given `v`, regularity and
Cauchy--Schwarz give `E_v[s_v^2] >= val(Psi_c)^2`. ∎

**Special cases.**

- `c` = identity: `Psi_c` is equivalent to `UG_der(Psi)`, which recovers
  `derived-unique-game-lower-bounds-the-noise-test`.
- `c` = one class per vertex: `e_c = 0` and `Psi_c = Psi`. This is the dictator
  bound `val(R) >= 1/m + (1-1/m) rho^3 val(Psi)^2`.

**Consequence (soundness must survive every decodable split).** If
`val(R(Psi)) <= epsilon` on NO instances, then every decodable feature satisfies

```text
val(Psi_c) <= sqrt((epsilon + 2 e_c) / ((1-1/m) rho^3)).
```

So the NO-case hardness has to survive splitting each left vertex along
**every** feature the noisy pullback reveals. Test-based routes to UGC are
blocked whenever some decodable feature yields an easy coarsened game, even when
the matching itself is unlearnable.

**Barrier for ancestral enrichment.** Suppose an enrichment reduction takes a
learnable hard instance `Psi_0` (for example `F_lin`-rich) to `Psi'`, and the
enriched matching at each edge still reveals, decodably, its parent's matching
or any coarse function of it, such as the affine direction. Then the test on
`Psi'` is no sounder than `Psi'_c`, split along that ancestral feature. For the
enrichment to help, `Psi'_c` must be hard *after* the ancestral information is
exposed. Keeping the parent's structure recoverable buys nothing through the
test.

## 3. Theorem 2: random exponential families are unlearnable

Let `Q = (P_1, ..., P_M)` be independent uniform perfect matchings of `[2n]`. The
planted index `i_0` is uniform in `[M]`, and `x` is a noisy pullback of
`P_(i_0)`. A **list decoder** is any map `List_Q : Z_m^(2n) -> [M]^L`, which may
depend on `Q`.

**Theorem 2.** For every `m >= 2`, `0 < rho < 1`, `L >= 1` and `M >= 2`,

```text
E_Q Pr_(i_0,x)[ i_0 in List_Q(x) ] <= 2 sqrt( (2L+4) A^n / (M-1) ),
A = 1 + rho^2 (m-1) < m.
```

*Proof.* The likelihood ratio of `x` under `P` against the uniform measure is

```text
L_P(x) = prod_({i,j} in P) (1 + rho^2 psi(x_i,x_j)),     psi(s,t) = m 1(s=t) - 1,
```

because two `K_rho` copies of one uniform symbol have joint law
`m^(-2)(1 + rho^2 psi)`. Each factor lies in `[1-rho^2, A]`, so `L_P <= A^n`.
The posterior of index `i` given `(Q,x)` is `L_(P_i)(x) / Z`, with
`Z = sum_j L_(P_j)(x)`. Hence

```text
Pr[i_0 in List_Q(x) | Q, x] <= min(1, L A^n / Z) <= min(1, L A^n / Z'),
Z' = sum_(j != i_0) L_(P_j)(x).
```

Condition on `(i_0, P_(i_0), x)`. The other `M-1` matchings are independent,
uniform and independent of `x`, so `Z'` is a sum of `M-1` independent copies of
`L_P(x)` with `P` uniform. Put `mu(x) = E_P L_P(x) = m^(2n) nu(x)`, where `nu` is
the noisy pullback law for a uniform matching. Since `E_P[L_P^2] <= A^n mu(x)`,
Chebyshev's inequality gives

```text
Pr[Z' < (M-1) mu(x)/2] <= 4 A^n / ((M-1) mu(x)).
```

Outside this event `L A^n / Z' <= 2 L A^n / ((M-1) mu(x))`. Therefore

```text
Pr[success | x] <= min(1, (2L+4) A^n / ((M-1) mu(x))).
```

`P_(i_0)` is a uniform matching, so `x` has law `nu`. The set
`{x : nu(x) < tau m^(-2n)}` has at most `m^(2n)` points and hence `nu`-mass at
most `tau`. Splitting the expectation at that threshold,

```text
E[success] <= tau + (2L+4) A^n / ((M-1) tau).
```

Taking `tau = sqrt((2L+4) A^n / (M-1))` proves the bound. ∎

**Corollaries.**

1. *Random smooth designs.* The random family of the smooth-design artifact
   (Remark 1 there) has `M >= 3 m^n (2n ln m + 1) / C(K,m)`. Its expected list-L
   success is at most `O(sqrt(L C(K,m)/(n ln m)) (A/m)^(n/2))`, which decays
   exponentially in `n` because `A < m`. By Markov's inequality, all but a
   `theta` fraction of such families have success at most that bound divided by
   `theta`.
2. *Composition with permutation designs.* For `D o Q = {sigma(P) : sigma in D,
   P in Q}`, run the same proof with the planted `sigma_0`: the matchings
   `sigma_0(P_j)`, `j != i_0`, are independent and uniform. Other blocks only
   increase `Z`. The same bound holds, so the `t`-wise uniform smooth designs of
   that artifact are member-unlearnable.
3. *Thresholds.* Members of separated families of size
   `exp(rho^4 delta_0^2 n/96)` can be decoded
   (`separated-pairing-families-admit-noisy-decoders`). Random families above
   `A^n = exp(n log(1+rho^2(m-1)))` cannot. Smooth designs need at least `m^n`
   members, above both thresholds.

## 4. The barrier answer

Can t-wise uniform, smooth pairing distributions come from a bounded-entropy
(learnable) source?

- **By counting, no.** Smoothness forces `log|F| >= n log m - O(1)`, while
  union-bound decodability needs `log|F| <= rho^4 delta_0^2 n/96`.
- **Generic smooth designs escape member-level transparency (Theorem 2).**
  Transparency is therefore not an obstruction to `smooth-design-rich-2to1-hardness`
  as such.
- **Transparency still bites through features (Theorem 1).** An outer
  construction reaches UGC through the test only if every decodable feature of
  its per-vertex matching distribution leaves a hard coarsened game. In
  particular, an enrichment that keeps the affine direction of the Grassmann
  2-to-1 instances recoverable must make the direction-split game hard on its
  own.

**Remark (label-preserving local refinement is gauge).** Let `Psi'` be built from
`Psi_0` with each left, right and edge object having a parent, left labels
re-encoded by bijections `lambda_(u')` and right labels by bijections `h_(v')`.
Require local completeness: every child edge is satisfied whenever its parent
is, for every labeling. Then `pi_(e') = h^(-1) o pi_e o lambda` and
`P_(e') = lambda^(-1)(P_e)`, so each child family is a conjugate of a parent
subfamily. Such refinements cannot enrich, which formalizes the "relabel per
vertex or edge" dead end.

## 5. Provenance

Theorems 1 and 2 were derived by `ugc-2` on 2026-09-11 in coordination with lane
`ugc-1`, whose smooth-design transfer and count bound are cited, not reproved.
Theorem 2 uses only Chebyshev's inequality and a mass-splitting argument. No
exhaustive literature review was made.
