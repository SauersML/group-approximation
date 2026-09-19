---
rg: 2
id: mf-radical-is-blind-to-degree-two-windings
kind: claim
title: Realification keeps the kernel of every MF approximation and kills all its degree-two windings, so no winding or conjugation-odd index certificate can prove MF-radical membership
distinct_from:
  kazhdan-mapping-tori-have-proper-stably-finite-radical: That kills certificates valid in every stably finite target, using a trace-small wrap block; this kills index certificates in the norm corona itself, with the realification as the killing step, and applies to every group.
  exel-loring-mark-quantization: That is the open programme of pinning a central mark by its Exel--Loring winding; this shows that its final step (a nonzero pairing forced by group data) is false for the realification of every corona representation, which keeps the mark nontrivial.
  mod-s2-quasirep-windings-vanish-on-fixed-window: That proves windings vanish for one group because its H_2 is torsion; this makes windings vanish for every group, for one explicit approximation in each kernel class.
  dadarlat-linear-groups-have-nonzero-h2-windings: That produces some approximation with a nonzero winding, an existence statement pointing toward MF; this shows that the universal form a non-MF proof would need is false.
  leavitt-copy-centralizing-units-are-self-doubling: That concerns Leavitt units and additive invariants of rings; this concerns quasi-representations of groups and conjugation-odd index invariants.
---

**ESTABLISHED.** Proof: `mf-radical-is-blind-to-degree-two-windings-proof`.

**Setting.**
- An **MF approximation** of a countable group `G` is a sequence `Pi = (pi_n : G -> U(k_n))`
  with `||pi_n(st) - pi_n(s) pi_n(t)|| -> 0` for all `s, t`.
- It induces a homomorphism `Pi' : G -> U(prod M_(k_n) / (+) M_(k_n))`, and
  `Rad_MF(G)` is the intersection of the kernels `ker Pi'`.
- The **realification** `r : M_k(C) -> M_(2k)(C)` is given by
  `r(A + iB) = [[A, -B], [B, A]]` for real `A, B`.

**(R1) Realification keeps the kernel.**
- `r o Pi` is again an MF approximation, and it takes values in the orthogonal groups
  `O(2 k_n)`.
- The defects and the displacements are unchanged:
  `||r(pi_n(g)) - 1|| = ||pi_n(g) - 1||` for every `g`.
- So `ker (r o Pi)' = ker Pi'`.
- `r(X)` is unitarily equivalent to `X (+) Xbar`, by the same fixed unitary `W_k` for all `X`.

**(R2) Conjugation-odd invariants vanish on it.** Let `I` assign to each quasi-representation
`rho` (defect below some `eps` on a fixed finite window) an element of an abelian group. Suppose:
- (a) `I(u rho u^*) = I(rho)` for every unitary `u`;
- (b) `I(rho (+) sigma) = I(rho) + I(sigma)`;
- (c) `I(rhobar) = -I(rho)`.

Then `I(r o rho) = 0`.

**(R3) The Exel--Loring--Dadarlat winding is such an invariant.** For `x in H_2(G; Z)` written as
`prod [a_i, b_i]`, the winding is
`w_rho(x) = (1/2 pi i) Tr log prod_i [rho(a_i), rho(b_i)]`. It satisfies (a), (b) and (c).
Its tracial form `(1/2 pi i) tau log (...)`, with any trace `tau` satisfying
`tau(Xbar) = conj tau(X)`, does too. So for every MF approximation `Pi` of any group `G` there
is an MF approximation `r o Pi` with:
- the same kernel in the corona;
- every degree-two winding and every tracial winding equal to zero, on every `x`, for all
  large `n`.

**(R4) Degree bookkeeping (remark, not part of the established statement).**
- Rational almost-flat index invariants in cohomological degree `2j` scale by `(-1)^j` under
  conjugation. So those of degree `2 mod 4` vanish on realifications, and those of degree
  `0 mod 4` need not.
- If the rational cohomological dimension of `G` is at most 3, the only rational index
  invariant left on `r o Pi` is the rank, which carries no information. This covers the
  Titz--Witzel kernel `K = Gamma_1^2` (a 2-dimensional complex) and the groups `K x Z` and
  `K semidirectProduct_phi Z` (dimension 3).
  The sign rule is the Chern-character identity `ch_j(Ebar) = (-1)^j ch_j(E)`. The
  identification of the degree-two part with the winding is Dadarlat's (arXiv:2111.05755,
  Thm 1.1). Only degree two is used below.

## What this kills

**The class.** Index certificates for membership in the MF radical. Such a certificate proves
`g in Rad_MF(G)`, or proves that a simple group is not MF, in two steps:
- (i) every MF approximation `Pi` with `g notin ker Pi'` has winding vector
  `(w_(pi_n)(x))_x` in some set `B`, for all large `n`;
- (ii) `0 notin B`.

The winding vector may be taken on `G`, on a subgroup, or after any operation `O` on
approximations that is **conjugation-natural**, meaning:
- `O(Pibar) ~ conj O(Pi)` and `O(Pi (+) Pi_2) ~ O(Pi) (+) O(Pi_2)`, where `~` is unitary
  equivalence;
- examples: restriction, precomposition with an automorphism, direct sum and tensor product with
  real representations, and functional calculus by functions with `f(zbar) = conj f(z)`.

**Invariant.** The complex-conjugation parity of the index.

**Step where every member dies.** Evaluation at the realification `r o Pi`.
- `r o Pi` is nontrivial on `g` whenever `Pi` is (R1).
- It has `O(r o Pi) ~ r o O(Pi)` (use (a), (b), (c) and the fixed unitary `W_k`), so its
  winding vector is `0` (R2, R3).
- So (i) and (ii) together say exactly that no `Pi` is nontrivial on `g`. That is the
  conclusion itself, proved with no help from the index.

**Members.**
1. **`exel-loring-mark-quantization` and its route `torsion-free-non-mf-from-exel-loring-mark`.**
   The programme needs the lifted pairing to be forced nonzero by the group data `<c,x> != 0`.
   - For `r o Theta`, with `Theta` any corona representation nontrivial on the mark `zeta`, the
     lifted winding is `0`. The mark stays nontrivial. The spectrum of `r(Theta(zeta))` is
     symmetric under conjugation, so its tracial argument is also `0`.
   - The quantization identity then reads `0 = 0`. The programme's contradiction never arises
     on `r o Theta`, so it cannot prove that every corona representation kills `zeta`.
2. **Winding proofs that the Titz--Witzel kernel `K` is not MF** (`titz-witzel-smallest-kernel-not-mf`).
   `H_2(K; Q) = Q^6` makes windings the natural index. If `K` is MF through `Pi`, then `r o Pi`
   is an injective model with all windings zero. So no certificate of the form (i)+(ii) can
   prove "`K` not MF", which is equivalent to (GAP) of
   `simple-kazhdan-mf-lives-in-gap-near-representations`. By (R4) no other rational almost-flat index is available on `K`.
3. **Wang-sequence certificates for exact radicals of mapping tori.** Take
   `G = K semidirectProduct_phi Z`, with `pi_n = Pi|K` and `u_n = Pi(t)`.
   - The expected constraint is `w_(pi_n) o (1 - phi_*) = 0` on `H_2(K)`. It would follow because
     `rho o phi` is close to `Ad(u) o rho`, using conjugation invariance and the homotopy
     invariance of Dadarlat's pushforward `pi_#`. That invariance is not verified here, and
     nothing below uses the constraint.
   - By the Wang sequence, over `Q` this is the whole degree-two winding content of `G`, since
     `H_1(K; Q) = 0` for Kazhdan `K`.
   - The constraint is satisfied by `0`. By (R1) the zero-winding approximations realize every
     kernel. So windings add nothing to (XMF) of
     `mf-kazhdan-quotientless-mapping-torus-exact-radical`, or to (EKL1) of
     `exact-kazhdan-radical-kernel-cannot-be-lef`.

**What survives.**
- **Conjugation-breaking operations.** For example, cutting `Pi` by the spectral projection of a
  non-real arc. This separates `Pi` from `Pibar` inside `r o Pi`, and a nonzero winding can
  reappear on the corner. Such a corner is an approximate subrepresentation only if the element
  cut along is almost central. So this lever needs a central or almost-central mark, and it is
  unavailable for the centreless simple `K` unless it is supplied extrinsically.
- **Invariants of degree `0 mod 4`**, which are absent in dimension at most 3.
- **Real (KO) and torsion invariants** that are even under conjugation.
- **Non-index arguments.**
