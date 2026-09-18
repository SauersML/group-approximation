# Adversarial check: `central-extensions-of-thompson-f-contain-f` (bh-refute, 2026-09-18)

Coordinator-assigned item. It bears on Witzel's question (via FFKLZ l.293) and on FFKLZ Question 2.4.

Verdict: **PASS**. I recomputed the whole homology calculation from Brown's relations as quoted
(arXiv:math/0411347). Those relations are: the ring `H_*(F)` under juxtaposition; `εα = βε = 0`; `αε = α`;
`εβ = β`; `α² = β² = 0`; `Δ(ε) = ε⊗ε`; `α`, `β` primitive.

## Recomputation

- **The flip on `H_1`.** The flip `R` swaps the two slope characters. With `χ_1(α) = χ_0(β) = 0`, this gives
  `R_*α = sβ` and `R_*β = sα`, with `s = ±1`.
- **The flip reverses the product.** `R(f*g)R = (RgR)*(RfR)`, and the swap has sign `(−1)^{|x||y|}` on cross
  products. So `R_*(αβ) = −s²αβ = −αβ` and `R_*(βα) = −βα`. Also `R_*ε = ε`, since `H_0` is fixed.
- **The coproduct,** using the sign `(x⊗y)(x'⊗y') = (−1)^{|y||x'|}xx'⊗yy'`:
  - `Δ(αβ) = αβ⊗ε + α⊗β − β⊗α + ε⊗αβ`. The four products were checked term by term, and the minus sign comes
    from `|α||β| = 1`.
  - `Δ(βα) = βα⊗ε + ε⊗βα`. The cross terms vanish because `βε = 0` and `εα = 0`.
- **The push-forward.** `δ_*(x⊗y ↦ x·R_*y)` sends
  - `αβ` to `(αβ)ε + sα² − sβ² − ε(αβ) = 0`, by associativity with `βε = εα = 0`;
  - `βα` to `β(αε) − (εβ)α = βα − βα = 0`.
- **Splitting.**
  - `δ` is an injective homomorphism, because `μ` is a homomorphism and `f*(RfR) = 1` forces `f = 1`.
  - `H_1(F) ≅ Z²` is free, so universal coefficients give `H^2(F;A) = Hom(H_2F, A)`. Hence `δ^* = 0`.
  - A central extension of `F` therefore splits over `δ(F)`.
  - Restriction gives the same conclusion for every `Q ⊇ F`.

## Attacks tried (all failed)

- **Non-unital ring.** `ε` generates `H_0`, but it is not a unit (`εα = 0`). The computation never uses a unit,
  only the stated relations and associativity.
- **Künneth signs.** Checked.
- **Nontrivial action on `A`.** Excluded by hypothesis (central extensions). The scope is correctly stated.

## Lesson for general BH

A self-embedding `δ = id * flip` that kills `H^2` makes every central extension split on a copy of the group.
So central extensions are harmless whenever the base has a "doubling with orientation reversal". This
suggests a transferable test for the live BH difficulty with central extensions (Deligne, Torelli): a `B_A`
host `Q` has all its central extensions in `B_A` whenever some self-embedding of `Q` is zero on `H^2`. The
Deligne-type inputs are exactly those whose bases (`Sp_2g(Z)`) have no such self-embedding.
