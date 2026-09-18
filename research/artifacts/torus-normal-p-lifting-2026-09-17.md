# Torus automata: fixed tori of infinite-index normal subgroups and lifting through normal p-subgroups (2026-09-17)

Author: swarm-0917-w10-w10-gs-break. Notation as in
`research/artifacts/torus-alphabet-degree-2026-09-17.md` Section 0: `X_d(G) = (T^d)^G`,
a *torus automaton* is a continuous `G`-equivariant self-map (no finite memory assumed),
`D = D(tau) in M_d(Z[G])` is its degree matrix, `tau^*(xi) = xi D` on Čech
`H^1(X_d(G); Z) = Z[G]^d`. For `N <| G`, `p_N : Z[G] -> Z[G/N]` is the quotient ring map.
A group `G` is *TS at d* if every injective torus automaton on `X_d(G)` is onto.

**Result in one line.** The periodic-point lemma of the parent artifact used only
finite-index normal subgroups. It works verbatim for *every* normal subgroup, provided one
replaces invariance of domain by what the graph already knows about the quotient. Combined
with a nilpotent-lifting step through normal `p`-subgroups, this settles the "smallest open
host" `Z(2^inf) x Z(3^inf)` and `Q/Z`, and in fact **every abelian group, at every d**. It
answers the concrete test of `torus-degree-regular-on-prime-power-residual-support`
negatively: no injective `tau` on `T^(Q/Z)` has `D(tau) = s + s^2 - t`.

Imported (ESTABLISHED in the graph; statements quoted from the node files).
- **(C1)** `torus-automata-with-regular-degree-are-surjective`: "Let `G` be a countable
  group, `d >= 1`, `T = R/Z`, and `tau: (T^d)^G -> (T^d)^G` any continuous `G`-equivariant
  map. No finite memory, injectivity or linearity is assumed. [...] If `xi -> xi D` is
  injective on `Q[G]^d`, then `tau` is surjective."
- **(RPP)** `torus-degree-regular-on-prime-power-residual-support`, claim (a): "If `H` is
  RPP, then `xi -> xi D` is injective on `Q[G]^d`, so `tau` is onto." Here `H = <supp D>`
  and RPP means "every finite subset of `H` embeds in some finite `p`-group quotient of
  `H`, the prime allowed to depend on the subset". Also its artifact Lemma 2: "For a
  finite `p`-group `P`, the augmentation ideal `I` of `F_p[P]` is nilpotent."
- **(PPL)** the proof of the periodic-point lemma of
  `torus-automata-over-rf-or-domain-groups-are-surjunctive` (parent artifact Section 2).
  We reuse its two computations: `Fix(N)` is identified with `(T^d)^(G/N)` by
  `i_N(y) = y o quotient`, and "On `H^1`, `i_N^*` sends `e_(h,i)` to `e_(hN,i)`, so
  `i_N^* = p_N`." Neither computation uses that `N` has finite index.

## 1. Restriction to the fixed torus of any normal subgroup

**Lemma 1.** Let `tau` be an injective torus automaton on `X_d(G)` and `N <| G` any normal
subgroup (possibly of infinite index). Put `Fix(N) = {x : n x = x for all n in N}`. Then
`tau(Fix(N)) subset Fix(N)`, and `tau_N = i_N^-1 o tau o i_N` is an **injective torus
automaton on `X_d(G/N)`** over the countable group `G/N`, with degree matrix `p_N(D)`.

*Proof.*
- `Fix(N)` is closed. It is `G`-invariant: for `x in Fix(N)`, `n (g x) = g (g^-1 n g) x
  = g x` since `g^-1 n g in N`.
- `n tau(x) = tau(n x) = tau(x)` for `x in Fix(N)`, so `tau` preserves `Fix(N)`.
- A configuration is `N`-fixed iff it is constant on the cosets `N g = g N`, so `i_N` is a
  homeomorphism `X_d(G/N) -> Fix(N)`, and it intertwines the `G/N`-shift with the
  `G`-shift restricted to `Fix(N)`. Hence `tau_N` is continuous, `G/N`-equivariant and
  injective.
- Degree: `tau o i_N = i_N o tau_N`, so `tau_N^* i_N^* = i_N^* tau^*`. With
  `i_N^* = p_N` (PPL, valid for any `N`), `tau_N^*(p_N xi) = p_N(xi D) = p_N(xi) p_N(D)`
  because `p_N` is a ring map, and `p_N` is onto. So `tau_N^*` is right multiplication by
  `p_N(D)`. QED.

**Lemma 2 (bijective torus automata have unit degree).** If a torus automaton `sigma` on
`X_d(Gamma)` is bijective, then `D(sigma) in GL_d(Z[Gamma])`.

*Proof.* A continuous bijection of a compact Hausdorff space is a homeomorphism, and
`sigma^-1` commutes with the shift, so `sigma^-1` is a torus automaton. Pullback is
contravariant: `(a o b)^*(xi) = b^*(a^*(xi)) = xi D(a) D(b)`, so `D(a o b) = D(a) D(b)`.
Applying this to `sigma o sigma^-1 = sigma^-1 o sigma = id`, whose degree is `1`, gives
`D(sigma) D(sigma^-1) = D(sigma^-1) D(sigma) = 1`. QED.

So an injective torus automaton is onto iff it is a homeomorphism iff (by C1 in one
direction and Lemma 2 in the other) its degree is invertible, and then regularity and
invertibility coincide for injective automata.

## 2. Lifting invertibility through a locally normal p-subgroup

**Definition.** A normal subgroup `N <| G` is a **locally normal `p`-subgroup** if every
finite subset of `N` lies in a finite `p`-subgroup `P subset N` with `P <| G`. Examples:
every finite normal `p`-subgroup; the `p`-primary component of the torsion subgroup of an
abelian group; every central locally finite `p`-subgroup.

**Lemma 3 (nilpotent lifting).** Let `N <| G` be a locally normal `p`-subgroup and
`D in M_d(Z[G])`. If `p_N(D) in GL_d(Z[G/N])`, then the reduction `D-bar` of `D` mod `p`
is invertible in `M_d(F_p[G])`, and `xi -> xi D` is injective on `Q[G]^d`.

*Proof.*
1. *Kernel.* The kernel of `F_p[G] -> F_p[G/N]` is spanned by the `g n - g = g(n - 1)`,
   `g in G`, `n in N`, so every kernel element is a finite sum `sum_i g_i (n_i - 1)`.
2. *Approximate inverse.* Let `E-bar in M_d(F_p[G/N])` invert `p_N(D) mod p`, and lift it
   entrywise to `E in M_d(F_p[G])`. Then `D-bar E = 1 - M` and `E D-bar = 1 - M'` with all
   entries of `M, M'` in the kernel.
3. *Finite normal p-subgroup.* The finitely many `n_i` occurring in the entries of `M` and
   `M'` lie in one finite `p`-subgroup `P <| G`, `P subset N`. So `M, M' in M_d(J)` with
   `J = F_p[G] omega(P)`, where `omega(P)` is the augmentation ideal of `F_p[P]`.
4. *J is nilpotent.* Since `P <| G`, `g (n - 1) = (g n g^-1 - 1) g`, so
   `F_p[G] omega(P) = omega(P) F_p[G]` and `J` is a two-sided ideal. Then
   `J^k = omega(P)^k F_p[G]`, by moving each `F_p[G]` factor to the right. By (RPP)
   artifact Lemma 2, `omega(P)^k = 0` for some `k`. So `J^k = 0` and
   `M_d(J)^k subset M_d(J^k) = 0`.
5. *Invertibility.* `1 - M` and `1 - M'` are invertible (inverse `sum_(j<k) M^j`). So
   `D-bar` has the right inverse `E (1 - M)^-1` and the left inverse `(1 - M')^-1 E`, and is
   invertible.
6. *Regularity.* Let `0 != xi in Q[G]^d` with `xi D = 0`. Clear denominators and divide by
   the largest power of `p` dividing all coefficients (`Z[G]^d` is torsion-free), so
   `xi in Z[G]^d` has some coefficient prime to `p`. Then `xi-bar != 0` and
   `xi-bar D-bar = 0`, so `xi-bar = xi-bar D-bar D-bar^-1 = 0`, a contradiction. QED.

**Theorem 4 (extension closure).** Let `tau` be an injective torus automaton on `X_d(G)`
and `N <| G` a locally normal `p`-subgroup. If the restriction `tau_N` of Lemma 1 is onto,
then `tau` is onto. In particular, **if `G/N` is TS at `d`, then `G` is TS at `d`.**

*Proof.* `tau_N` is an injective torus automaton over `G/N` (Lemma 1). It is onto by
hypothesis, so it is bijective and `p_N(D) = D(tau_N) in GL_d(Z[G/N])` (Lemmas 1, 2).
By Lemma 3, `xi -> xi D` is injective on `Q[G]^d`. By (C1), `tau` is onto. QED.

**Corollary 5 (series).** Let `1 = N_0 <= N_1 <= ... <= N_r` be normal subgroups of `G`
such that, for each `j`, `N_j / N_(j-1)` is a locally normal `p_j`-subgroup of
`G / N_(j-1)`. Let `tau` be an injective torus automaton on `X_d(G)`. If `tau_(N_r)` is
onto, then `tau` is onto.

*Proof.* For `N <= M` both normal in `G`, `Fix(M) subset Fix(N)`, and under
`i_N : X_d(G/N) ~ Fix(N)` the set `Fix(M)` corresponds to `Fix(M/N)`. So
`(tau_(N_(j-1)))_(N_j/N_(j-1))` is conjugate to `tau_(N_j)` by the canonical
identification `G/N_j = (G/N_(j-1)) / (N_j/N_(j-1))`. Descending induction on `j` with
Theorem 4 applied to `tau_(N_(j-1))` over `G/N_(j-1)` shows every `tau_(N_j)` is onto,
down to `tau_(N_0) = tau`. QED.

**Corollary 6 (finite solvable normal subgroups).** If `L <| G` is finite and solvable and
`G/L` is TS at `d`, then `G` is TS at `d`.

*Proof.* Refine the derived series `L = L^(0) > L^(1) > ... > L^(m) = 1`. Each `L^(i)` is
characteristic in `L`, hence normal in `G`. The finite abelian group
`A_i = L^(i) / L^(i+1)` is the direct sum of its Sylow subgroups `S_(i,1), ..., S_(i,k)`.
Each partial sum `S_(i,1) + ... + S_(i,j)` is characteristic in `A_i`, and `A_i` is normal
in `G / L^(i+1)`, so its preimage in `G` is normal in `G`. Listing these preimages from the
bottom up gives a chain `1 = N_0 <= ... <= N_r = L` of normal subgroups of `G` with each
factor `N_j / N_(j-1)` a finite `p_j`-group normal in `G / N_(j-1)`, hence a locally normal
`p_j`-subgroup. For an injective `tau`, `tau_L` is an injective torus automaton over `G/L`
(Lemma 1), onto by hypothesis. Corollary 5 applies. QED.

## 3. Every abelian group is torus-surjunctive

**Theorem 7.** Every countable abelian group `G` is TS at every `d >= 1`.

*Proof.* Let `tau` be injective on `X_d(G)` with degree `D`, and let `A = <supp D>`, a
finitely generated abelian group. Its torsion subgroup `A_tor` is finite; let
`p_1, ..., p_r` be the primes dividing `|A_tor|` (so `r = 0` if `A` is torsion-free). Let
`G_p` denote the `p`-primary component of the torsion subgroup of `G`, and put
`N_j = G_(p_1) + ... + G_(p_j)`.
1. *The series.* `N_j / N_(j-1) = G_(p_j)` (the sum of primary components is direct). A
   finite subset of `G_(p_j)` generates a finite `p_j`-group, normal because `G` is
   abelian. So the hypotheses of Corollary 5 hold.
2. *The top quotient is torsion-free on the support.* `tau_(N_r)` has degree `p_(N_r)(D)`,
   whose support generates the image `A-bar` of `A` in `G/N_r`. If `a in A` and `m a in N_r`
   for some `m >= 1`, then `m a` is torsion, so `a in A_tor subset N_r` (every element of
   `A_tor` has order divisible only by `p_1, ..., p_r`). So `A-bar = A / (A cap N_r)` is a
   finitely generated torsion-free abelian group, `A-bar = Z^k`.
3. *Z^k is RPP.* For a finite `S subset Z^k` choose `n` with `2^n` larger than twice the
   absolute value of every coordinate of every element of `S`; then `Z^k -> (Z/2^n)^k` is injective on `S`, and `(Z/2^n)^k`
   is a finite `2`-group.
4. By (RPP) applied to `tau_(N_r)` (an injective torus automaton over `G/N_r`, Lemma 1),
   `tau_(N_r)` is onto. By Corollary 5, `tau` is onto. QED.

**Corollary 8 (the concrete test is answered).** On `G = Q/Z` or
`G = Z(2^inf) x Z(3^inf)`, with `s` of order 3 and `t` of order 2, no injective torus
automaton on `T^G` has degree `D = s + s^2 - t`. More sharply: an injective torus
automaton on any `X_d(G)`, over any abelian `G`, has `D in GL_d(Z[G])`.

*Direct check for `D = s + s^2 - t`.* Take `N = G_2` (the 2-primary part). Then
`p_N(D) = s + s^2 - 1` in `Z[G/N]`, supported in the cyclic 3-group `<s>`, which is RPP. By
(RPP) and Lemma 1, `tau_N` is onto, so by Lemma 2 `s + s^2 - 1` would be a unit of
`Z[<s>] = Z[Z/3]`. It is not: under the character `s -> omega` it maps to
`omega + omega^2 - 1 = -2`, not a unit of `Z[omega]`. (Equivalently, the congruence
`D(t = -1) = D(t = 1) mod 2` makes `D` invertible mod 2 as soon as `D(t = 1)` is a unit,
which is Lemma 3 in this instance.)

*Proof of the sharp form.* Theorem 7 gives surjectivity; Lemma 2 then gives invertibility.

## 4. What changes in the graph

**Belief broken.** `torus-degree-regular-on-prime-power-residual-support` (Consequence 2)
and `injective-torus-automata-have-regular-degree` (Attempts) record that "the smallest open
host is the divisible, locally finite abelian group `Z(2^inf) x Z(3^inf)` (or `Q/Z`)", that
"torus surjunctivity over `G` is **not known** from any tool in the graph", and that
`every-group-is-torus-surjunctive` "is open even on countable abelian locally finite
groups". All three are now false: TS holds for **every** abelian group, at every `d`
(Theorem 7). The heuristic those notes were used to refute (TS is the easier
characteristic-zero shadow of GOT) is therefore *not* refuted by the abelian hosts; the
refutation needs a host where GOT is easy and TS is still open, and the candidates move to
groups with few normal subgroups (below).

**Why the old obstruction does not apply.** The old dichotomy concerned
*augmentation-only* proofs, which see only `Fix(G)`, the circle of constants. The proof
above sees `Fix(N)` for every locally normal `p`-subgroup `N`, a full shift over `G/N`
(infinite-dimensional, so invariance of domain is not used), and imports surjectivity there
from (RPP) or by induction. The Bezout witness `a P_s + b P_t` is defeated because its
image modulo the `q`-part is `a P_s + b q`, which is not a unit (Part C of the experiment).

**Descent of counterexamples.** Theorem 4 read backwards: if `tau` is an injective,
non-surjective torus automaton over `G`, then for every locally normal `p`-subgroup `N`,
`tau_N` is an injective, non-surjective torus automaton over `G/N`. So a counterexample to
C2 pushes down to `G/O` for every finite solvable normal `O` and every chain as in
Corollary 5. Minimal counterexample hosts may be taken to have no nontrivial locally normal
`p`-subgroup for any `p`, and in particular no nontrivial finite solvable normal subgroup.

**New smallest open host.** The finitary alternating group `Alt_fin(N)` (even permutations
of `N` with finite support). It is countable, locally finite, amenable, not residually
finite, and simple, so Lemma 1 gives only `Fix(G)` (constants) and `Fix(1)`. Every finite
group embeds in it, so it carries the Bezout witnesses of every non-prime-power order.
Finite-alphabet surjunctivity over it is elementary (it is locally finite). New concrete
test: construct, or rule out, an injective torus automaton on `T^(Alt_fin(N))` whose degree
is the Bezout witness `2 P_t - P_s` for `s` a 3-cycle and `t` a double transposition in a
copy of `A_4`.

**What this does not do.** It does not touch finite-alphabet Gottschalk (the transfer step
`torus-surjunctivity-implies-finite-alphabet-surjunctivity` remains OPEN with its
obstructions O1–O3), and it adds no non-sofic host: every group covered is abelian, or a
finite-solvable (more generally, locally-normal-`p`) extension of a host already covered.

## 5. Computation

`experiments/torus-normal-p-lifting-2026-09-17/check_normal_p_lifting.py` (pure Python,
exact arithmetic) checks Lemma 3 and the mechanism of Corollary 8.
- Part A: all `5^6 - 1` nonzero `D in Z[Z/6]` with coefficients in `[-2, 2]`. The 600 with
  unit image in `Z[G/<t>]` and the 1368 with unit image in `Z[G/<s>]` are all invertible
  mod `p` and regular over `Q`. The 60 zero divisors of augmentation `+-1` in the box all
  have non-unit image in both quotients.
- Part B: 80 random `D` at `d = 1, 2` for each of `Z/6` (`N = <t>`, `<s>`), `S_3`
  (`N = A_3`), `A_4` (`N = V_4`), `Z/2 x Z/6` (`N = Z/2 x Z/2`), built as a lift of a
  product of trivial units and elementary matrices plus a random element of
  `M_d(omega(N) Z[G])`. All are invertible mod `p` and regular over `Q`.
- Part C: the Bezout witness `2 P_t - P_s` on each of these groups is a zero divisor of
  augmentation 1 whose image in `Z[G/N]` is not a unit.
