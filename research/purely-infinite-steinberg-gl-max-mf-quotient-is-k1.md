---
rg: 2
id: purely-infinite-steinberg-gl-max-mf-quotient-is-k1
kind: claim
title: For a minimal effective ample groupoid that compresses every compact open set, the maximal MF quotient of GL_n of its Steinberg algebra is algebraic K_1, and its MF radical is the commutator subgroup
distinct_from:
  purely-infinite-canonical-k1-all-ranks: that is the ring theorem for an arbitrary countable purely infinite simple ring; this is its groupoid face, with a dynamical hypothesis that forces pure infiniteness of the Steinberg algebra
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that kills MF quotients of the elementary groups from rank 2n under the weaker hypothesis of no invariant measure; this computes the full MF quotient of GL_n at every rank n >= 1 under local compressibility
artifacts:
  - research/artifacts/un-k1-homology-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route `purely-infinite-steinberg-gl-max-mf-quotient-is-k1-proof`.

**Setting.**
- `𝒢` is a second countable, Hausdorff, ample groupoid with compact infinite unit space `X`, minimal and effective.
- **(PI) local compressibility.** For every nonempty compact open `A ⊆ X` there are compact open bisections
  `U, V ⊆ 𝒢` with `s(U) = s(V) = A`, `r(U) ⊆ A`, `r(V) ⊆ A` and `r(U) ∩ r(V) = ∅`.
- `k` is a countable field and `R = A_k(𝒢)`.

**Claim.** `R` is a countable purely infinite simple ring. For every `n >= 1` the canonical map
`κ_n : GL_n(R) → K_1(R)` is surjective and

`Rad_MF(GL_n(R)) = [GL_n(R), GL_n(R)] = ker κ_n`,

so every homomorphism from `GL_n(R)` to an MF group factors uniquely through `κ_n`, and the maximal MF quotient
of `GL_n(R)` is the countable abelian group `K_1(A_k(𝒢))`. The same holds for `R^×` with `κ : R^× → K_1(R)`.

**Calibrations.**
- `𝒢 = 𝒢_(R_d)`, the Cuntz groupoid of the full shift on `d >= 2` letters, satisfies (PI). Then `R = L_k(1,d)` and
  the quotient is `K_1 = k^×/(k^×)^(d-1)`, as in `non_mf_groups_exist.tex` Cor l.1297.
- The transformation groupoid of a minimal ℤ-subshift fails (PI): a bisection `U` with `s(U) = A` preserves the
  invariant measure, so `μ(r(U)) + μ(r(V)) = 2μ(A) > μ(A)`. There `GL_n` of the ring is LEF
  (`exactly-matricial-rings-have-lef-general-linear-groups`), so its MF radical is trivial: the opposite extreme.

**Where it sits in the dichotomy.** On the paradox side the MF radical of `GL_n` is as large as it can be,
because every MF quotient is abelian; on the matricial side it is trivial. So an MF approximation of `GL_n` sees
only `K_1`, which is pure homological data, or sees everything. See `research/artifacts/un-k1-homology-2026-09-13-part1.md`.
