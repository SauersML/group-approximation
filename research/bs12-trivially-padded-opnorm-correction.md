---
rg: 2
id: bs12-trivially-padded-opnorm-correction
kind: claim
title: Approximate BS(1,2) pairs are operator-norm close to exact pairs after block sum with an identity block
distinct_from:
  bs1n-rq-padded-opnorm-stability: that is Willett's theorem, where the block-summed auxiliary is an arbitrary finite-quotient representation; here the auxiliary must be the trivial representation, which is the only padding the Higman gate can glue.
  bs14-hs-stability-does-not-supply-relative-op-basin: that concerns normalized-HS stability; this is an operator-norm, dimension-uniform statement.
  higman-seam-gate-needs-only-padded-bs-correction: that proves this statement plus glued-cycle collapse gives the Higman marked collapse; this is the open local prerequisite itself.
---

**OPEN.**  `(TPC)`: for every `epsilon>0` there is `delta>0` such that for all
`N` and unitaries `A,B in U(N)` with

```text
||A B A^* - B^2|| <= delta
```

there exist `k>=0` and unitaries `C,Z in U(N+k)` with `C Z C^* = Z^2` and

```text
||C-(A (+) 1_k)|| <= epsilon,      ||Z-(B (+) 1_k)|| <= epsilon.
```

This is implied by same-dimension matricial stability of `BS(1,2)` (the case
`k=0`), which is Eilers--Shulman--Sorensen arXiv:1808.06793v4, Section 6,
Question 3, and is open.  It implies nothing about the auxiliary in
`bs1n-rq-padded-opnorm-stability`, which is published and has uncontrolled
padding.  Neither implication is known to reverse.

Why it is a separate prerequisite: by
`higman-seam-gate-needs-only-padded-bs-correction`, `(TPC)` together with the
glued-cycle collapse `higman-exact-packet-cycles-collapse-opnorm` gives the
Higman marked collapse.  Any per-seam correction whose auxiliary summand is
not trivial reaches that gate only through instances of `(TPC)`.  `(TPC)` is
purely about `BS(1,2)` and can fail even if the Higman collapse is true.

## Attempts

Recorded when the claim was created on 2026-09-18 (reframing).  These are
partial, not a proof.

- *Spectral half.*  An operator-norm defect `delta` matches the eigenvalues of
  `B` with those of `B^2` within `c delta` (Bhatia--Davis--McIntosh constant
  for normal matrices).  That matching is a permutation `s` of eigen-indices
  with `|2x_j - x_(s(j))| <= c delta` (angles mod `1`).  Each cycle is a
  periodic pseudo-orbit of the doubling map.  Expansivity (use the
  contracting inverse branch) shadows it by a true periodic orbit `y_j` with
  `|x_j-y_j| <= c delta`.  So `B` can be replaced by `B'` with the same
  eigenvectors and exactly squaring-invariant, cycle-constant multiplicity
  spectrum, with `||B-B'|| <= c delta`.  This half needs no padding.
- *Conjugator half.*  With `B'` fixed, `A` is a `3c delta`-approximate
  intertwiner from `B'` to `B'^2`.  Correcting it with `B'` fixed can fail, in
  the same way as for Voiculescu's pair (shift against a fine clock).  The
  twisted pair `A=A_0 V` (with `A_0 e_j=e_(j/2)` on `Z/N`, `N` odd, and `V` the
  shift) is nevertheless exactly correctable after moving `B`: since
  `A_0^* V A_0 = V^2`, conjugating `B'` by a power of `V` absorbs the shift.
  So the Bott-type twist is not an obstruction.  This is consistent with
  `K_*(C^*(BS(1,2)))` carrying no Bott class, since `H_2(BS(1,2))=0`.
- *Where it stops.*  No general construction corrects the conjugator with
  only an identity padding, and no same-dimension or trivially padded
  obstruction is known.  Stable-uniqueness proofs need absorbing auxiliaries
  containing nontrivial finite-quotient representations.  Exact packets
  cannot be deformed to trivial ones because the spectrum of `Z` is rigid in
  the odd roots of unity.  So Willett's `R_q`-padding does not specialize to
  trivial padding.
- *Padding is inert off the fixed point of doubling* (2026-09-18,
  stability-approximation, swarm-0917-w11-w11-ptm-pull).  The results below
  are ESTABLISHED in
  `bs12-identity-padding-inert-off-doubling-fixed-point`, with an
  elementary written proof.  They do not settle `(TPC)`, but they locate
  exactly what the identity padding can buy.
  - *Gapped pairs.* Suppose `dist(1, spec B) >= gamma` and `(TPC1)` holds
    with `epsilon < gamma/8`.  Then the spectral projection of `Z` onto
    `D[1,epsilon]` is exactly squaring-invariant, hence equals `ker(Z-1)`,
    hence reduces the packet.  Stripping it off gives a same-dimension exact
    packet within `epsilon(1+16/gamma)`.  This holds for padding by any
    representation on which `b` is trivial.  So on gapped pairs `(TPC)` is
    exactly the Eilers--Shulman--Sorensen `k=0` question.
  - *Where padding can help.* Otherwise, cut off `ker(Z-1)` and let `kappa`
    be the almost-invariance constant of the complementary exact packet.
    Removal still costs only `O(sqrt(epsilon) + epsilon/kappa)`.  In an
    irreducible `b`-fixed-point-free packet of dimension `L`, `kappa >= 1/L`.
    This was checked numerically in
    `experiments/bs12-padding-2026-09-17/kappa_cycle_bound.py`: over all
    squaring cycles of odd `n <= 257`, the minimum of `kappa L` is `3.46`,
    at `L = 2`.  So a strict gain of `(TPC)` over `k=0` needs correcting
    packets with irreducible constituents of dimension greater than
    `1/sqrt(epsilon)`.  Each such constituent is a long squaring cycle with
    long binary 0-runs, carrying a `sqrt(epsilon)`-almost-invariant vector.
  - *Worked example, heuristic only.* Take the orbit of `1/(2^L-1)` in
    dimension `L`, and compress it off its near-invariant uniform vector.
    The result is `(TPC)`-correctable with `k=1`.  A Fourier matching of
    modes `k/L -> (k-1/2)/(L-1)` suggests that it is also close to the orbit
    packet of `1/(2^(L-1)-1)` with twist `-1`, with `k=0`.  This is not
    proved.  Proving it, and the general "site removal" statement it
    instances, would make identity padding inert everywhere.
  - *Status.* That statement is: an exact packet with an
    `epsilon`-almost-invariant subspace has its compression to the
    orthocomplement close to an exact packet.  It is the one remaining gap
    between `(TPC)` and the `k=0` question, and it is itself a special case
    of the `k=0` question.  The hole stays OPEN.

2026-09-18, swarm-0917-w12 (operator-algebras, belief breaker).  Partial
result; the node stays OPEN.

- *Conjugator half on separated spectra: established.*
  `bs12-separated-doubling-spectra-correct-conjugators-unpadded` proves the
  following.  If `spec B'` is squaring-invariant and `gamma`-separated, then
  pinching `A` along `E_(B'^2)` and `E_(B')` and taking the polar part gives an
  exact `C` with `||C-A|| <= 7 eta/min(gamma,1)`, with `k=0` and `B'` fixed.
  The tool is a Wiener-norm Schur multiplier for `1/(y-z)`.  So `(TPC)` holds
  with `k=0` whenever the shadowed spectrum has bounded doubling period
  (`epsilon = O(4^L delta)`).
- *The ratio is sharp: the base must move.*  Take `A_s = W exp(is(V+V^*))`,
  `B = D` (clock), `W D W^* = D^2`, `N` odd.  Then `eta <= 2 s gamma` and
  `delta = O(s/N) -> 0`.  Yet every exact `C` with `C D C^* = D^2` is at least
  `~|J_1(2s)|/2` from `A_s`, uniformly in `N`.  So "fix `B'`, correct `A`" is a
  dead approach exactly when `eta/gamma` is not small.  Any proof of `(TPC)`
  must move the spectrum of `B'` on long periodic orbits.
- *Dead scheme.*  Keeping `C = A_s` and solving `Z = sqrt(A Z A^*)` by
  iteration, choosing on each eigenspace the root nearest to the current `Z`,
  fails even at `s = 0.05`.  At `N = 27` the residual is `0.16` and
  `||Z-D||` is `1.95` (`experiments/bs12-fourier-twist-2026-09-17/probe.py`).
  The branch choice cannot be continuous.  A positively expansive
  homeomorphism lives only on a finite space, so there is no continuous,
  near-identity, doubling-equivariant coarsening of a fine spectrum.  This
  scheme says nothing about whether `(A_s, D)` is correctable.
- *Open test family.*  `(A_s, D)` for fixed `s` and `N -> infinity` (`3 | N`)
  is the sharp test for `(TPC)` and ESS Q3.  In the Fourier basis, `A_s` is
  a weighted doubling with multiplier `phi(m) = e^(2is cos(2 pi m/N))`.  The
  Livsic holonomy `phi(0)^2 / (phi(N/3) phi(2N/3)) = e^(6is)` rules out
  first-order gauge corrections `(U A_s U'^*, U D U^*)`, unless
  `e^(6is) = 1`.  The linear functional
  `Phi(Y) = <f_0,Y f_0> - (<f_(N/3),Y f_(N/3)> + <f_(2N/3),Y f_(2N/3)>)/2`
  vanishes on linear coboundaries and has `Phi(s(V+V^*)) = 3s`.  This is only
  a linearization at `(W, D)`.  Exact pairs whose `Z` has a different, long
  period spectrum within `O(s)` are not excluded, so belief on this family is
  unresolved.  A proof that every exact pair stays `c(s) > 0` away would refute
  ESS Q3.  An explicit spectrum-changing correction would be the first case of
  `(TPC)` in the regime `eta ~ gamma`.

2026-09-18 (reframing, swarm-0917-w12-w12-ptm-pull).  **The padding is
worthless.**  `bs12-identity-padding-is-removable-in-operator-norm` proves that
an exact packet within `eps` of `(A (+) 1_k, B (+) 1_k)` can be replaced by an exact
packet in `U(n)` within `O(1/log(1/eps))` of `(A,B)`, uniformly in `n` and `k`.
So `(TPC)` is *equivalent* to same-dimension operator-norm stability of
`BS(1,2)`, which is ESS Question 3 (`n=1, m=2`).  The claim stays **OPEN**, and it is
now exactly a published open question.
- *Class kill.* Strategies that use the identity padding are dead. Invariant: the
  almost-invariant vectors of the correcting packet. They lie within
  `sqrt(2a) eps` of the fixed space of a nearby exact packet, obtained by excising
  deep binary runs.
- *Where the remaining difficulty sits.* Any proof or counterexample must address
  the unpadded conjugator problem itself.

2026-09-19 (cohomology-index, swarm-0917-w14-w14-ptm-break, belief breaker).
Class kill on the open test family; the node stays **OPEN**.
- *Result, ESTABLISHED* in
  `bs12-fourier-monomial-corrections-need-equal-cycle-holonomies`.  Consider
  exact pairs monomial in the Fourier basis, `C = W e^(ia(V))` and
  `Z = D e^(it(V))`.  Their exactness is the cocycle equation
  `t_(2m) + t_(2m-1) - t_m = a_(m-1) - a_m`.
  - Pairing it with translated Bernoulli `B_1` vectors from the cokernel
    forces `avg_gamma(a) = mean(a)` on every doubling cycle `gamma` of
    `m -> 2m`, and it eliminates the base weights `t`.
  - So reweighting `(A_s, D)` costs at least `2 sin(s/2)`, and at least
    `2 sin(3s/4)` when `3 | N`, uniformly in `N`.
  - Linear programming gives exactly `1.5 s` for `3 | N` and `1.25 s` for
    `N = 25, 35, 125`.
  - `Z` keeps the spectrum of `D` exactly.
- *Class killed.*  This covers every correction that moves base and conjugator
  only by Fourier-diagonal weights, arbitrary and discontinuous.  That
  includes all Fourier-diagonal gauges and the first-order Livsic gauge
  recorded above.  The invariant is the conjugator's cycle holonomy
  normalized by `det(W^* C)^(1/N)`.  Every member dies at the exact cocycle
  equation over `R`.
- *What survives.*  A correction within `o(s)` must make `Z` non-monomial in
  the Fourier basis.  Fixed-base corrections (arbitrary `C`, `Z = D`) are
  already dead at about `s/2`.  So the next test is exact pairs
  `(U W_u U^*, U D U^*)` with `U` monomial in neither basis.
2026-09-19 (census-computation, swarm-0917-w14-w14-ptm-last1).  **Test
family `(A_s, D)`: moving the base beats the fixed-base floor, and the
distance keeps falling in `N`.**  Details are in
`bs12-twisted-clock-exact-pair-census`.  The claim stays **OPEN**.
- *Sharpened fixed-base floor (proved).*  Take `k = (N-1)/2`.  Then
  `D^k H D^(-k)` changes `cos a` to `cos(a + pi - pi/N)`, which gives
  `||A_s D^k A_s^* - D^(2k)|| >= 2 sin(s(1+cos(pi/N)))`.  Hence every
  `C` with `C D C^* = D^2` has `||C - A_s|| >= sin(s(1+cos(pi/N))) -> sin 2s`.
  This replaces `|J_1(2s)|/2` above: at `s = 1/2` it is `0.841` against
  `0.220`.  Any exact correction closer than this must move the
  near-antipodal powers `Z^((N-1)/2)` and `Z^(N-1)` by order one.
- *Census (explicit exact pairs, upper bounds only).*  The search runs over
  all exact pairs with simple `N`-th-root base in `U(N)`, namely
  `(U W diag U^*, U D U^*)`.  The values of `d(s,N)` are:
  - `0.566 -> 0.364` at `s = 0.5`, for `N = 9 .. 243`;
  - `0.314 -> 0.259` at `s = 0.25`, for `N = 27 .. 243`;
  - `0.147 -> 0.135` at `s = 0.1`, for `N = 27 .. 243`.

  The optimal `U` is far from `1`.  It blurs the clock over a position
  window of about `0.05 N` sites.  These are the spectrum-changing
  corrections that the Livsic / first-order analysis above could not see.
  They come in below the first-order level `~ 1.5 s`.
- *Belief update.*  At `s = 1/2` there is no plateau, so the census gives
  no evidence for a Q3 counterexample on this family.  At small `s`,
  `d/s` falls only slowly (`1.47 -> 1.35` at `s = 0.1`), so the census
  cannot separate a slow decay to `0` from a positive limit.  The
  isolated open question is whether some fixed `s` has
  `liminf_N d(s,N) > 0`; a positive answer refutes ESS Q3.
2026-09-19 (reframing, swarm-0917-w15-w15-ptm-break).  Class kill on the sharp
family.  The claim stays **OPEN**.
- *Established:* `bs12-sharp-pair-twist-coherent-corrections-are-bounded-below`.
  Call `u` a twist for `C` if `u^3 = 1` and `C u C^* = u^2`, and suppose
  `u f_0` is within `kappa` of a multiple of `f_(2N/3)`.  Then
  `2|sin 3s| <= 4||C - A_s|| + 2 kappa`, with no condition on `Z`.
- *The class it covers.*  For exact pairs with `Z^N = 1`, the power
  `u = Z^(N/3)` is a twist.  For every Fourier gauge `Z = h(V) D h(V)^*`, of
  any size, it has `kappa = 0`.  So every exact `C` over such a `Z` is at least
  `|sin 3s|/2` away, uniformly in `N`.  This makes the first-order Livsic
  remark above nonlinear.  An LP shows the small-`s` constant `3/2` is attained
  inside this class (`N <= 729`).
- *Why it matters.*  The w14 census pairs reach `d(0.5, 243) = 0.364 < 0.4987`
  and `d/s ~ 1.35 < 1.5`.  So they are twist-incoherent, with
  `kappa >= 2|sin 3s| - 4d`.  A proof of ESS Q3 here has to scramble the base
  modulo 3 at scale `1/N`.  A counterexample needs an invariant other than a
  twist.  `p = 7` gives the analogous bound `2|sin(7s/2)| <= 6 eps + 2 kappa`.
- 2026-09-19 (swarm-0917-w15-w15-ptm-follow): *decomposition along the limit
  trace.*  Route `bs12-trivially-padded-opnorm-correction-via-faithful-padding`
  proves that Q3 is equivalent to `bs12-faithful-trace-opnorm-correction`
  (Q3_full, for near-reps with faithful limit trace) together with
  `bs12-regular-padding-is-removable` (RPR).  The proof pads by the odd clock
  representation, which makes the trace faithful.
  - Q3_full follows from LV HS-stability (`bs1n-hs-stable-levit-vigdorovich`,
    verbatim) together with
    `bs12-full-lift-uniqueness-in-matrix-ultraproducts`.
  - Every K/KL obstruction vanishes
    (`bs12-matrix-lift-pairs-have-zero-kl-class`).
  - The live crux is de-amplification without Z-stability.  CGSTW Thm 1.2
    fails verbatim, because the relative commutant of `prod M_N` in `Q_omega`
    is `C`.
  - Uniqueness is false for non-faithful traces: `1_{N-1} + chi` versus
    `1_N`.
  - The wave-14 twisted-clock census has limit trace `tau_reg`.  So it is
    exactly a test of Q3_full, and a positive liminf would refute TPC.
- 2026-09-19 (swarm-0917-w16-w16-ptm-break): *twist-free bases are a dead
  end.  The dyadic ladder reduction is new.*  See
  `bs12-sharp-pair-dyadic-scale-ladder`.
  - *Tried.* Correcting the sharp pair with exact pairs whose base has order
    `M`, where `3` does not divide `M`, so that `Z^(N/3)` is not available as
    a twist. At `N = 27`, `s = 0.1` the census gives:
    - `M = 25`: `0.664`;
    - `M = 23`: `0.795`;
    - control `M = 27`: `0.147`.
  - *Where it dies.* First, the premise is false in general. Every
    squaring-equivariant `mu_3`-colouring `f` of `spec Z` gives the twist
    `f(Z)`, and such colourings exist exactly on squaring orbits of even
    length. For example, `M = 25` has orbits of lengths `4` and `20`. Second,
    the genuinely twist-free bases (for example `M = 23`, whose orbit length
    is `11`) cannot be aligned with `D`: the cycle types of `x2` differ. They
    come out farther still.
  - *Proved on the way.* The telescoping gauge `h = exp(-is sum_{k<K} H_(2^k))`
    gives `h^* A_s h = W e^(isH_(2^K))` exactly and moves `D` by at most
    `4 pi s (2^K - 1)/N`. So `d(s,N)` equals `dist((A_s, D^R), exact)` up to
    `4 pi s R/N` for every dyadic `R << N/s`. The Livsic series diverges at
    the doubling fixed point, which is why the reduction stops there.
  - *Belief update.* The census minimisers keep an order-`N` base and are
    twist-incoherent. A counterexample to Q3 therefore needs a lower bound
    over order-`N` bases with scrambled mod-3 structure. Removing the twist
    does not help.
