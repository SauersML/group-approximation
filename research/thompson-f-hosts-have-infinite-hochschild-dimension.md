---
rg: 2
id: thompson-f-hosts-have-infinite-hochschild-dimension
kind: claim
title: A ring with Q in its centre that contains Z[F] for Thompson's F has infinite Hochschild dimension over every finitely generated central subfield; so no finite-dimensional host class (quasi-free, Leavitt/Cohn localizations, Cantor crossed products by finite-cd groups, their tensor products and corners) can serve the projective-simple host hole
distinct_from:
  quasi-free-algebras-have-no-trdeg-two-subfields: that excludes transcendence-degree-two subfields inside Hochschild-dimension-one algebras and needs invertibility of all nonzero polynomials; this excludes commuting independent families of any size with no invertibility, bounds them by the Hochschild dimension d for every d, and applies it to hosts of group rings.
  non-ibn-rational-hosts-have-infinite-elementary-centre: that kills non-IBN rational hosts through the scalar group in Z(EL_n); this kills finite-Hochschild-dimension hosts through commuting rank, including stably finite ones (Cantor crossed products by finite-cd groups) that the non-IBN kill does not reach.
  leavitt-tensor-global-dimension-bound: that is the upper bound gl.dim(B ⊗ L^(⊗d)) <= gl.dim B + d for Leavitt factors; this uses the same Eilenberg--Rosenberg--Zelinsky upper bound for an arbitrary algebra and pairs it with a Koszul lower bound.
---

**ESTABLISHED** by `thompson-f-hosts-have-infinite-hochschild-dimension-proof`
(swarm-0917-w19-w19-z-pull, 2026-09-19; unreviewed).

Notation: for a field `k` and a `k`-algebra `A`, `hd_k A = pd_(A ⊗_k A^op) A`. A *commuting independent family*
of size `n` in `A` is a set of commuting `a_1, ..., a_n ∈ A` with `P(a) ≠ 0` for every nonzero `P ∈ k[x_1..x_n]`.

1. **Commuting rank is bounded by Hochschild dimension.** If `hd_k A = d < ∞`, then no commuting independent
   family of size `d + 1` exists in `A`. The same holds in every `M_r(A)` and in every corner `pAp`, and for
   every injective, possibly non-unital, `k`-algebra map `k[Z^(d+1)] -> A`.
2. **Base change of the centre.** If `K ⊆ Z(L)` is a subfield that is finitely generated over `Q`, of
   transcendence degree `e`, then `hd_Q L <= hd_K L + e`.
3. **Hosts of Thompson's group.** Let `L` be a unital ring with `Q ⊆ Z(L)`, and let `Z[H] -> L` be a unital
   injection, where `H` contains `Z^m`. Then `hd_Q L >= m`, and `hd_K L >= m - e` for every `K` as in 2.
   - `H = F`, Thompson's group, is finitely presented, has solvable word problem, and contains `Z^m` for
     every `m`. So every host `L` of `Z[F]` with `Q ⊆ Z(L)` has `hd_K L = ∞` for every finitely generated
     central subfield `K`.
   - The same holds for `T`, `V`, `nV`, and every group containing `Z^∞` or `Z^m` for all `m`.
4. **Hosts with finite Hochschild dimension.** Let `K ⊇ Q` be a finitely generated field. Each `K`-algebra
   `B` below has `hd_K B < ∞`, and so does every finite tensor product over `K` of such algebras.
   - (a) Every quasi-free `K`-algebra, and every universal localization of one. This covers `L_K(1,n)` and
     free algebras (`universal-localizations-of-quasi-free-algebras-are-quasi-free`).
   - (b) `LC(X, K) ⋊ G`, for every compact metrizable totally disconnected `G`-space `X` and every group
     `G` with `cd_Q G < ∞`. Here `hd_K <= 1 + cd_Q G`.

   For such `B`, no `M_r(B)` and no corner `p M_r(B) p` contains a unital copy of `Z[F]`. So none of these
   rings can be the host `L` of `decidable-group-ring-has-fp-projective-simple-host` for `H = F`.

## What this kills, and where

- *Invariant:* `hd`, over any finitely generated central subfield, or equivalently the commuting rank of
  polynomial subalgebras. Its lower bound is `w.gl.dim(L ⊗_Q Q(y_1..y_m)) >= m`.
- *Where it dies:* at the Koszul top class `Tor_m ≠ 0` for the `m` commuting translations of `Z^m ≤ F`.
  The Eilenberg--Rosenberg--Zelinsky bound caps that degree at `hd`.
- The kill is uniform in `H` in this sense: any host construction `H ↦ L(H)` must produce, already for the
  single decidable f.p. group `F`, a host of infinite Hochschild dimension.
  - The char-0 engine `Z[H] *_Z D` (`finitely-presented-divisible-ring-engine`) is consistent with this. It
    contains `Q[F]` for `H = F`.
- Together with the non-IBN kill (Attempts item 7 of the hole), a surviving characteristic-zero host for
  `H = F` must satisfy both:
  - either be stably finite, or be purely infinite with `[1]` of infinite order in `K_0`;
  - have infinite Hochschild dimension over every finitely generated central subfield.
  In particular, no Cantor crossed product `LC(X,K) ⋊ G` with `cd_Q G < ∞` survives, whether stably finite
  or not.

Scope: this does not decide the hole. Crossed products by groups of infinite rational cd, such as Thompson-like
groups, and free products with division rings, stay untouched.
