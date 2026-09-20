---
rg: 2
id: thompson-v-not-mf
kind: claim
title: Thompson's group V is not MF
distinct_from:
  thompson-v-not-hyperlinear: that excludes injective maps into a tracial ultraproduct, i.e. normalized Hilbert--Schmidt models; this excludes injective maps into the operator-norm matrix corona. Neither is known to imply the other for V, since trivial padding makes any operator-norm model Hilbert--Schmidt-null and an HS model need not be norm-multiplicative.
  thompson-v-not-lef: that excludes exact local embeddings into finite groups, which is classical; this excludes approximate operator-norm unitary models, which is open.
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that shows unnormalized operator-norm ratio witnesses for V are exactly as hard as "V is MF"; this is the negative answer itself, as a hole.
  leavitt-mf-quotients-see-thompson-vd-through-parity: that proves V lies in Rad_MF(R^x), a statement about corona representations of the ambient Kazhdan group R^x; this is about corona representations of V itself, which need not extend to R^x, so property (T) of R^x says nothing about it.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that is about exact finite-dimensional representations; this is about asymptotic ones.
---

**OPEN.** Thompson's group `V = G_(2,1)` admits no injective homomorphism into
the unitary group of a norm matrix corona

```text
Q = prod_k M_(d_k)(C) / sum_k M_(d_k)(C),
```

in the unitary-sequence sense of `countable-group-mf-conventions`.

## Equivalent forms

`V` is simple (`thompson-v-finitely-presented-infinite-simple`), so a
homomorphism `V -> U(Q)` is injective or trivial. Hence the claim says: **every
corona representation of `V` is trivial**, i.e. `Rad_MF(V) = V`. It is enough
to kill one nonidentity element. By
`binary-leavitt-mark-is-conjugate-to-thompson-cone-swap` the natural one is a
cone transposition, e.g. the Bleak--Quick generator `a = (00 01)`.

By compactness (a corona representation is a sequence of asymptotic
representations of a finite presentation), the claim is equivalent to a
uniform finite statement. For the Bleak--Quick presentation
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, there is
`eps > 0` such that every unitary triple `(A, B, C)` in any `U(d)` whose nine
relators satisfy `||r(A,B,C) - I||_op <= eps` has `||A - I||_op < 1`.

Proof of the equivalence.
- If no `eps` works, take triples with defect `1/k` and `||A_k - I|| >= 1`.
  Their classes give a homomorphism `V -> U(Q)` with `||[A] - 1|| >= 1`,
  which is a nontrivial corona representation.
- Conversely, lift a corona representation to unitary sequences. Eventually
  the defect is at most `eps`, so `||pi(a) - 1|| <= 1`. But `pi(a)` is a
  symmetry `1 - 2p` in `Q`, so `||pi(a) - 1||` is `0` or `2`. Hence
  `pi(a) = 1`, and simplicity kills `pi`.

## Why this hole is intrinsically Kazhdan-free

`V` has the Haagerup property (`thompson-v-has-haagerup-property`), so every
Kazhdan subgroup of `V` is finite (`thompson-v-has-no-rigid-compression-defect`).
The compression mechanism of `rank-twelve-leavitt-simple-non-mf` needs an
infinite Kazhdan source, so it cannot run inside `V`. A corona representation of
`V` need not extend to any Kazhdan overgroup. So property (T) of `R^x` or of
`E_n(R)` gives no information about this claim.

## What it would settle

By `property-t-free-leavitt-via-thompson-v-not-mf`, this claim implies
`property-t-free-leavitt-full-mf-radical` by a proof tree free of (T). More
generally it gives `Rad_MF(G) = G` for every simple group `G` containing `V`.

## Attempts

**2026-09-19 (swarm-0917 w14, belief breaker): first-pass attacks and where each dies.**
1. **Through (T) of an overgroup.** This dies because a corona representation of `V` need not extend to `R^x` or to
   `E_n(R)`. Inside `V` every Kazhdan subgroup is finite.
2. **Through non-hyperlinearity.** This dies by trivial padding. Put an MF model of `V` beside a large identity block.
   The result is still an operator-norm model, but in normalized Hilbert--Schmidt norm it is close to trivial. So an
   argument that sees only HS data cannot exclude operator-norm models. Every proof must consume operator-norm or corona
   structure.
3. **Through stable finiteness (deferred).** A corona image `C*(pi(V))` is an MF algebra, hence stably finite. So it
   would suffice that every C*-quotient of `C*_max(V)` in which `V` embeds contains an infinite projection. This is the
   spark of `swarm-0917-w14-w14-ptl-last1`. It is not attempted here: it needs a Cuntz-type isometry built from
   group elements alone, and the obvious ones live in `C(X) x| V`, not in `C*(V)`.
4. **Local form (deferred).** An operator-norm analogue of `thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words`
   would read: exact `S4` and `S3` representations, glued on `a` with `a != I`, make `r5`--`r8` small in operator norm.
   It needs an imported verbatim form of Kazhdan's operator-norm stability of epsilon-representations of finite groups.
   Estimating the minimal gluing defect `mu(N)` for small `N` is then a finite computation, not run here.
