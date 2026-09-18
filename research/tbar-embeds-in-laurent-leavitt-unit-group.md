---
rg: 2
id: tbar-embeds-in-laurent-leavitt-unit-group
kind: claim
title: The Ghys--Sergiescu lift T-bar of Thompson's group T, and so (Q,+), embeds in the unit group of the binary Leavitt algebra over a Laurent ring, with the central translation going to the Laurent variable
distinct_from:
  integral-leavitt-unit-group-contains-q: that puts (Q,+) in L_Z(1,2)^x through a transvection of infinite order, which has order p modulo p; this puts T-bar in (L_k(1,2) ⊗ k[t^±1])^x for every commutative ring k, including F_2, with the divisible element the central variable t.
  rationals-embed-in-binary-leavitt-unit-group: that asks for (Q,+) in L_(F_2)(1,2)^x itself; this is the version with a central Laurent variable adjoined, which reaches that claim only through an embedding of L ⊗ F_2[t^±1] into L.
---

**ESTABLISHED** (proof: `tbar-embeds-in-laurent-leavitt-unit-group-proof`). Not independently reviewed; novelty
not searched.

## Statement

Let `k` be a commutative ring, `L = L_k(1,2)` and `L[t^±1] = L ⊗_k k[t, t^(-1)]`. Let `T̄` be the group of
homeomorphisms of `R` that commute with `x -> x+1` and descend to Thompson's `T` on `R/Z` (survey
arXiv:2306.16356v3, Section 4.3). Write each `h̃ in T̄` on a dyadic subdivision `[0,1) = ⊔ I_(β_i)`, with
`I_β = [0.β, 0.β + 2^(-|β|))`, as `h̃(x) = h(x) + n_i` on `I_(β_i)`, where `h(I_(β_i)) = I_(α_i)` affinely and
`n_i in Z`. Then

```text
Ψ(h̃) = Σ_i s_(α_i) t^(n_i) t_(β_i)
```

is a well-defined injective group homomorphism `T̄ -> L[t^±1]^x`. It sends the central translation `x -> x+1` to
`t`, and its image lies in the topological full group of the groupoid `G_2 × Z`.

**Consequence.** Belk--Hyde--Matucci proved that `T̄` contains `(Q,+)` (Bull. AMS 59 (2022) 561--567; survey
arXiv:2306.16356v3: "the first explicit description of a finitely presented group `T̄` that contains the additive
group `Q`"). So `(Q,+) <= L_(F_2)(1,2)[t^±1]^x`. The dyadic part is explicit: the lifts of the rotations by
`2^(-m)` map to `r_m = Σ_(j < 2^m − 1) s_(w_(j+1)) t_(w_j) + s_(w_0) t t_(w_(2^m − 1))`. Here `w_j` is the binary
word of length `m` for `j`. These satisfy `r_(m+1)^2 = r_m` and `r_0 = t`.

## Use

This is the positive half of the sandwich for `rationals-embed-in-binary-leavitt-unit-group`. Any unital embedding
`L_(F_2)(1,2)[t^±1] -> L_(F_2)(1,2)` carries `T̄`, and with it `(Q,+)`, into `U = L_(F_2)(1,2)^x`
(`rationals-in-leavitt-units-via-diagonal-copy`). Such an embedding exists iff some unit of infinite order is
conjugate to its diagonal copy (`infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy`).
