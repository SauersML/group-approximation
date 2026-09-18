---
rg: 2
id: saturated-l-adic-subrings-are-arithmetic
kind: claim
title: A finitely generated subring R of Z_l with R[1/l] cap Z_l = R lies in a number field; so l-adic affine hosts only reach S-arithmetic linear groups
distinct_from:
  affine-type-a-structure-groups-give-fp-simple-hosts: that is the host criterion, which assumes saturation; this shows saturation forces the coefficient ring to have transcendence degree zero, which bounds the criterion's reach.
  char-zero-linear-groups-embed-in-polynomial-s-integer-groups: that reduces every characteristic-zero linear group to polynomial S-integer rings of positive transcendence degree; this shows that ring class is out of reach of saturated l-adic affine hosts.
---

**ESTABLISHED** (lane proof, not reviewed; standard commutative algebra, no priority claimed).

**Statement.** Let `ℓ` be a prime and `R ⊆ Z_ℓ` a finitely generated subring.
1. If `R[1/ℓ] ∩ Z_ℓ = R` (ℓ-saturation), then `Frac(R)` is a number field and `R` has Krull
   dimension 1.
2. For every finitely generated `R ⊆ Z_ℓ`, if the saturation `R' = R[1/ℓ] ∩ Z_ℓ` is finitely
   generated, then `R ⊆ R'` lies in a number field. For example, `Z[α]` with `α ∈ Z_ℓ`
   transcendental has non-finitely-generated saturation: it contains `(α − a_k)/ℓ^k` for the
   truncations `a_k ∈ Z` of `α`.

**Proof.**
1. **The residue ring is `F_ℓ`.** Saturation gives `R ∩ ℓZ_ℓ = ℓR`. Indeed, if `r ∈ R ∩ ℓZ_ℓ`
   then `r/ℓ ∈ R[1/ℓ] ∩ Z_ℓ = R`. Hence `R/ℓR ↪ Z_ℓ/ℓZ_ℓ = F_ℓ`, and `R/ℓR = F_ℓ`. So
   `𝔪 = ℓR` is a maximal ideal, and it is principal.
2. **Height one.** `R ⊆ Z_ℓ` is a domain and `ℓ ≠ 0`, so by Krull's principal ideal theorem
   `ht 𝔪 = 1`.
3. **Dimension formula.** `R` is a domain of finite type over `Z`, which is universally catenary.
   So `ht 𝔪 = trdeg_Q Frac(R) + 1 − trdeg_{F_ℓ}(R/𝔪)`, recalled and not re-read, where the `+1`
   is because `R ⊇ Z` is not a `Q`-algebra: `ℓ ∈ 𝔪`. As `R/𝔪 = F_ℓ`, this gives
   `trdeg_Q Frac(R) = 0`.
4. **Item 2.** `R'` is ℓ-saturated. If it is finitely generated, apply item 1. For the example,
   `(α − a_k)/ℓ^k ∈ Z_ℓ ∩ Z[1/ℓ][α] = R'`. If `R'` were finitely generated it would lie in a
   number field by item 1, but `α ∈ R'` is transcendental. ∎

## Lesson for general BH

Any host whose local maps are affine over a ring `A ⊆ Q_ℓ` on `ℓ`-adic coordinates has, as its
germ structure group, the linear group over the saturation `A[1/ℓ] ∩ Z_ℓ`. Finite presentation
needs that ring finitely generated, and then it is arithmetic. So "`ℓ`-adic affine" is exactly the
arithmetic local model. Positive transcendence degree needs local models whose finiteness does
not pass through a saturated coefficient ring: self-similar (Zaremsky), Leavitt (positive
characteristic), or germ models. The general BH route should therefore split by local model, and
not try to stretch one affine host.
