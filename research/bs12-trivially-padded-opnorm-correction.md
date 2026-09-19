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
