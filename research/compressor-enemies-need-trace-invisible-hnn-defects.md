---
rg: 2
id: compressor-enemies-need-trace-invisible-hnn-defects
kind: claim
title: An enemy in a unitary matrix model of the Theorem E group needs a trace-invisible defect on a fixed finite HNN relator set, so gap transports of finite carriers carry none
distinct_from:
  ccr-holds-for-all-genuine-fd-coordinate-models: that proves (CCR) for ultraproducts of genuine representations of G; this needs exactness only on the finite set F, so the coordinates may be approximate on every other relation of G. The mechanism (dimension count plus a Kazhdan-pair lift) is the same and is credited there.
  monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable: its mixed-return estimate shows that Pauli wall models of P_X semidirect V_T cannot be corners of genuine V_T representations; this states the model-level consequence for arbitrary unitary models of G and turns it into a condition on finite carriers and their representations.
  kt-gamma-saturation-is-gamma-or-contains-e: that proves hyperlinearity of W_Gamma is equivalent to one enemy in one canonical CE model; this says where in a matrix model such an enemy must break exactness.
artifacts:
  - research/compressor-enemies-need-trace-invisible-hnn-defects-proof.md
---

**ESTABLISHED (proposed; proof in
`compressor-enemies-need-trace-invisible-hnn-defects-proof`).** Corollary 3(e)
cites Gluck's character-ratio theorem; everything else is proved in full.

This is an obstruction for a whole class of attacks on
`approximate-collapse-for-kt-compressor`. It answers the wave step "does a
weakly sofic enemy survive passage to unitary matrix models?" for every
passage that goes through a unitary representation of the finite carrier and
sees the carrier's defects at the relator set F.

## Setting

- Let `q` be a prime power and `r, d >= 3`.
- `R_+ = F_q[x_1..x_d]`, `R` is its Laurent ring, `Gamma = EL_r(R_+)`,
  `E = EL_r(R)`, and `G = E ⋊ SL_d(Z)`.
- Fix `t` in `SL_d(N) \ A_d`, so `Lambda = t Gamma t^-1 <= Gamma`, and set
  `u = e_12(x_1^-1)`.
- `S_Gamma = {e_ij(1), e_ij(x_k)}` is a finite generating set of `Gamma`.
- For each `s` in `S_Gamma`, fix a word `w_s` over `S_Gamma` with
  `t s t^-1 = w_s` in `G`. These are the compression relators `C_t`.
- By Shalom (`fpbs-shalom-property-t-is-open`), fix a finite set `R_0` of
  relators of `Gamma` such that `Gamma~ = <S_Gamma | R_0>` has (T). Let `kappa`
  be its Kazhdan constant for `S_Gamma`.
- Put `F = R_0 ∪ C_t`. This is a finite set of words over `S_Gamma ∪ {t}` and
  a finite presentation of an ascending HNN cover `V~_T` of `V_T = <Gamma, t>`.
- A **model** is a homomorphism `sigma : G -> U(M)` into
  `M = prod_omega (M_(d_n), tr)`. The trace need not be canonical.
- An **enemy** is an element of `sigma(Gamma)' ∩ M` that does not commute with
  `sigma(u)`.

## Theorem 1 (finite exactness kills the enemy)

Suppose `sigma(s)` for `s` in `S_Gamma` and `sigma(t)` have unitary
representatives `U_n(s)` and `T_n` that satisfy every relator in `F`
**exactly** for omega-almost every `n`. Then:

- `sigma(Lambda)' ∩ M = sigma(Gamma)' ∩ M`, which is (CCR) for `t`;
- `sigma(Gamma)' ∩ M = sigma(E)' ∩ M`;
- `sigma` has no enemy.

Nothing is assumed about the other relators of `G` beyond the fact that
`sigma` is a homomorphism. Equivalently: if the restriction of `sigma` to
`V_T` is an ultraproduct of genuine representations of the finitely presented
cover `V~_T` in the same dimensions, there is no enemy.

## Theorem 2 (location of the defect in a transported model)

Let `Q_n` be finite groups, `phi_n : S -> Q_n` arbitrary maps on a finite
generating set `S` of `G` that contains `S_Gamma ∪ {t}`, and
`rho_n : Q_n -> U(d_n)` unitary representations. Suppose
`sigma_n = rho_n ∘ phi_n` defines a model `sigma`. Every relator of `G` then
holds asymptotically in normalized Hilbert--Schmidt norm, and the lamps and
any other structure of the carrier are arbitrary.

For `w` in `F`, write `z_(n,w)` for the value of `w` on `phi_n` in `Q_n`.

If `sigma` has an enemy, then some `w` in `F` has `rho_n(z_(n,w)) != 1` (in
particular `z_(n,w) != 1`) for omega-almost every `n`, and for that `w`

```text
Re tr rho_n(z_(n,w)) -> 1 .
```

So the enemy lives on a nontrivial carrier defect at a fixed finite relator
set of `V~_T`, and that defect is invisible to the trace of `rho_n`.

## Corollary 3 (killed transport classes)

General form: if there is `c < 1` with `Re tr rho_n(q) <= c` for every
`q in Q_n` with `rho_n(q) != 1` (omega-almost every `n`), the transported model
has no enemy. In each case below, the transported model `rho_n ∘ phi_n` has no
enemy. Hence
it cannot be the `G`-part of a canonical matrix model of `W_Gamma`, of the
Clifford cover `E_S`, or of any CE actor with an enemy.

- **(a) Regular transports.** `rho_n` is the left regular representation, or
  any representation with `tr rho_n(q) = 0` for `q != 1`.
- **(b) Fixed-point-ratio permutation transports.** `rho_n` is a permutation
  representation on a set `Y_n`, and nontrivial defects fix at most a fraction
  `c < 1` of `Y_n`.
  - This includes `GL(V)` or `AGL(V)` acting on the vectors of an
    `F_q`-space, where the fixed ratio is at most `1/q`. So rank-metric
    (linear sofic) carriers transported this way are killed.
- **(c) Tensor-permutation transports.** `Q_n <= Sym(X_n)` acts on
  `(C^k)^(⊗X_n)` with `k >= 2`, where `tr = k^(c(q) - |X_n|) <= 1/k`. This is
  the Bernoulli or Pauli-string transport.
- **(d) Weil/Clifford transports.** `Q_n` lies in the n-qubit Clifford group
  with phases in `mu_8`, and `rho_n` is its defining representation on
  `C^(2^n)`. Here `Re tr rho_n(q) <= 2^(-1/2)` for `q != 1`.
- **(e) Bounded products of non-abelian simple groups, any representation.**
  `Q_n = S_(n,1) x ... x S_(n,k)` with `k` fixed and each factor a finite simple
  group of Lie type, a sporadic group, or an alternating group of bounded
  degree. The factors may have arbitrary rank
  and field, and `rho_n` may be **any** unitary representation.
  - The proof splits off the factors on which `rho_n` is asymptotically
    trivial.
  - It then uses Gluck's bound `|chi(x)/chi(1)| <= 19/20` for `x != 1` and
    nontrivial irreducible `chi` (Gluck, J. Algebra 174 (1995), as in
    Liebeck's survey, Thm 2.4).

## What survives, and the next step

A surviving enemy model must, infinitely often along omega, map some relator
of the finite set `F` to a nontrivial carrier element whose trace under
`rho_n` tends to 1. Such an element acts as the identity on all but a
vanishing fraction of the space. This is the Hamming or wall defect profile of
`wall-models-avoid-norm-microstates`.

Among finite carriers, this points to:

- alternating factors of unbounded degree;
- unboundedly many factors, as in the Hamming type;
- large abelian or solvable pieces.

Groups of Lie type with bounded products, Clifford groups and fixed-point-free
actions are excluded.

Equivalently, the `V_T`-part of an enemy model is not an ultraproduct of
genuine `V~_T` representations: it is a non-liftable almost representation
with `Ad sigma(e) != 0` for the Kazhdan projection
`e = t p_Gamma t^-1 - p_Gamma`.

**The sharpest remaining step is the extension problem.** Can one sofic wall
model of `V_T` (such as the Pauli models of
`monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable`, which have
`Ad sigma(e) != 0`) be extended to an HS-almost representation of `G`, that
is, adjoin `sigma(u)` and `SL_d(Z)`? By the all-or-nothing theorem,
`sigma(u)` would then automatically fail to commute with the commutant.

## Relation to the Clifford-cover ratio filter

The route `clifford-cover-hilbert-embeddable-route` records a character-ratio
constraint that needs a uniform ratio bound on the **whole** carrier and
concludes that the witness would be LEF. This node needs the bound only at the
finitely many carrier elements where the relators of `F` land. It puts no
condition on lamps or on the other relators of `G`, and it concludes that the
unitary model of `G` has no enemy at all. It also kills carriers that are not
quasirandom: Weil/Clifford, fixed-point-ratio permutation, tensor-permutation,
and bounded products of simple groups with any representation.

## Calibration

- Hamming or sofic transports (`Sym` with its permutation representation)
  have fixed-point ratio tending to 1, so they are not killed. This is
  consistent with the sofic Pauli wall models of `P_X ⋊ V_T`.
- In the dyadic world `Gamma` lacks (T). There the lift in Theorem 1 fails,
  and enemies exist in sofic models, as they should.
- Genuine representations of `G` satisfy the hypothesis of Theorem 1, which
  recovers `ccr-holds-for-all-genuine-fd-coordinate-models`.
