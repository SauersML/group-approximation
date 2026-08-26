---
rg: 2
id: hnn-over-infinite-cyclic-subgroups-preserves-mf
kind: claim
title: HNN extensions over infinite cyclic subgroups of matricially regular groups are MF
distinct_from:
  profinite-synchronized-hnn-is-regular-mf: that needs finite quotients of the base with equal edge kernels; this needs no finite quotients and no synchronization, only that the base has finite-dimensional approximations with regular traces and that the edge is infinite cyclic, the conjugating unitary coming from spectral equidistribution.
  regular-mf-central-hnn-closure: that is the identity edge; this allows any two infinite-order elements to be made conjugate.
  crossed-product-by-corona-inner-automorphism-is-mf: that is a global automorphism of the base; this is a conjugacy between two cyclic subgroups.
---

ESTABLISHED.  Call a countable group `A` *matricially regular* if there are
maps `rho_n : A -> U(d_n)` such that `rho = [rho_n]` is an injective
homomorphism into `prod M_(d_n) / (+) M_(d_n)` and `tr_(d_n)(rho_n(g)) -> 0`
for every `g != 1`.  Residually finite groups are matricially regular (left
regular representations of a cofinal chain of finite quotients), and so are
amenable groups (the regular UHF embeddings used in Shulman's Theorem 19).

**Theorem.**  Let `A` be matricially regular and let `a, b in A` have
infinite order.  Then

```text
H = < A, q | q^-1 a q = b >
```

is regularly operator-MF realized; in particular `H` is MF.

By contrast, such extensions destroy residual finiteness in general: for `A =
Z` they are the Baumslag--Solitar groups `BS(m,n)`, residually finite only
when `|m| = 1`, `|n| = 1` or `|m| = |n|`, yet all MF by the theorem.  The
same applies to `< F_2, q | q^-1 a q = b >` for any two infinite-order
elements of a free group, and to every HNN extension of an amenable group
over an infinite cyclic subgroup.

## Proof

*Spectral equidistribution.*  For `g` of infinite order, `g^k != 1` for `k
!= 0`, so `tr(rho_n(g)^k) -> 0` for all `k != 0`: the empirical eigenvalue
distribution of `rho_n(g)` converges weakly to Haar measure on the circle.
Since the Haar distribution function is continuous, the Kolmogorov--Smirnov
discrepancy `D_n(g)` tends to `0`, so after sorting eigenvalues by argument
the `k`-th eigenvalue of `rho_n(g)` lies within `2 pi D_n(g)` of `e^(2 pi i
k/d_n)`.  Matching `k`-th eigenvectors of `rho_n(a)` and `rho_n(b)` gives
unitaries `u_n` with

```text
|| u_n rho_n(a) u_n^* - rho_n(b) || <= 2 pi (D_n(a) + D_n(b)) -> 0.
```

Thus `u = [u_n]` is a corona unitary with `u rho(a) u^* = rho(b)`.

*Assembly.*  Let `D = C*(rho(A))`, `B_0 = C*(rho(a)) ~= C(T)`, `B_1 =
C*(rho(b))`, `alpha = Ad(u) : B_0 -> B_1`.  Exactly as in the proof of
[[profinite-synchronized-hnn-is-regular-mf]] (Ueda's full-corner
identification of the universal C-star HNN algebra with a corner of `M_2(D)
*_(B (+) B) M_2(B)`, and Shulman's Theorem 20 with the compatible embeddings
`M_2(D) <= M_2(Q)` and `x -> diag(1,u) x diag(1,u)^*`), the universal C-star
HNN algebra `HNN(D, B_0, alpha)` is MF.  The ultralimit trace `tr` of the
`tr_(d_n)` is the regular character of `A` on `D`, `alpha` preserves it on
`B_0` (both sides vanish off the identity), and the trace-preserving
conditional expectations of the GNS von Neumann algebra of `(D, tr)` onto
the two edge von Neumann algebras kill `rho(g)` for `g` outside `<a>`
respectively `<b>`, by regularity.  The reduced von Neumann HNN normal form
then sends every nonidentity Britton-reduced word of `H` to an element of
trace zero, so `H` embeds in the unitary group of the MF algebra `HNN(D,
B_0, alpha)` with the regular character.  That is the assertion.

## Remarks

The realization of `H` obtained this way carries a regular trace on an MF
algebra, but it is not shown to be matricially regular along a matrix
sequence, so the theorem is stated for one edge; iterating it requires
re-establishing matricial regularity at each stage.  For edges of rank at
least two (free subgroups with prescribed bases) the spectral argument has
no analogue, and that is precisely the single remaining edge in
[[boone-base-semidirect-product-is-hnn-over-free-subgroups]].
