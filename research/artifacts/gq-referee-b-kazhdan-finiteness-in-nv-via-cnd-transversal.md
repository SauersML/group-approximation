# Referee report (citation/hypothesis lens): `kazhdan-finiteness-in-nv-via-cnd-transversal` and `gl-3-z-in-no-nv-via-cnd-transversal`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: both conditional routes, landed at 4bfc08e51 and 93792b520. Their
premise is the OPEN node `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`. gq-referee-a passed the `GL_3(Z)`
route on the proof-gap lens.

## Verdict

**PASS for both, as conditional routes.** Every hypothesis the requester flagged matches. Neither route establishes
anything until its premise is proved, and both say so.

## The four requested checks

1. **Delorme–Guichardet.**
   - Bekka–de la Harpe–Valette, *Kazhdan's Property (T)* (CUP 2008), §2.12, "The Delorme–Guichardet Theorem",
     Theorem 2.12.4. That section and theorem number were confirmed through search listings of the book; the text
     itself was not read.
   - For countable discrete groups, (T) ⇔ (FH). A conditionally negative definite `ψ` with `ψ(e) = 0` has the
     form `‖b(g)‖²` for an affine isometric action. This is Schoenberg's correspondence, BHV §2.10 and Appendix C,
     with numbers not checked.
   - (FH) gives a fixed point, so `b` is bounded and hence `ψ` is bounded.
   - The use on `K = ι(SL_3(Z))` and on `K' = σ^{-1}Kσ` is correct.
   - **A1.** Cite "BHV Theorem 2.12.4 (§2.12)". Mark the Schoenberg correspondence as "BHV §2.10 / App. C,
     number not checked".
2. **Left cosets.**
   - `haagerup-splits-as-coset-plus-subgroup-properness` defines "proper modulo `H`" as sublevel sets "contained
     in a finite union of left cosets `g_1 H ∪ ... ∪ g_r H`".
   - The premise node says "finitely many left cosets of `T_n`".
   - The covering step uses `K ∩ g_iT = k_i(K ∩ T)` for `k_i ∈ K ∩ g_iT`, which is correct for left cosets.
     **It matches.**
3. **Item 3 of `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`.**
   - Verbatim: "For `d >= 3` and any embedding `SL_d(Z) → nV` or `GL_d(Z) → nV`, no nontrivial power of any root
     element `e_ij` maps into `f T_n f^-1`", for arbitrary `f ∈ nV`.
   - Step 4 needs `ι(e_12)^N = ι(e_12^N) ∈ T_m` with `N >= 1`. That is a nontrivial power, since `e_12` has
     infinite order and `ι` is injective, and `f = 1`. **It matches.**
   - The Kazhdan route's step 3 uses conjugates `T_n^σ = σT_nσ^{-1}` with `σ` a coordinate permutation. That
     conjugation is by an automorphism of `nV`, not by an element `f ∈ nV`.
   - Item 3 is not used there, so there is no mismatch. Do not try to deduce item 3 for `T_n^σ` from `f`-conjugates.
4. **Farley.**
   - `thompson-v-has-haagerup-property` cites D. Farley, *Proper isometric actions of Thompson's groups on Hilbert
     space*, IMRN 2003, no. 45, 2409–2414. It covers `F`, `T` and `V`. The citation is standard, but I did not
     re-read it.
   - The derived facts are standard: CCJJV (Progress in Math. 197) for passage to subgroups and finite products,
     and (T) + Haagerup ⇒ finite for discrete groups.
   - The Kazhdan route builds the proper cnd function `Σ ψ_V(h_i)` on `V^n` itself, which is correct.

## Other points checked

- **`⋂_j T_n^{σ_j} = V^n`.** Brin's `nV` does not permute coordinates. An element mapping the fibres of `x ↦ x_j`
  into fibres, for every `j`, is a product map `(h_1, …, h_n)`, with each `h_j` locally a prefix replacement and
  bijective. So `h_j ∈ V`. **Correct.**
- **Finite index.** `[K : K ∩ V^n] < ∞`, and a finite-index subgroup of a (T) group has (T). **Correct.**

## Scope

Both routes reduce everything to the premise `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`, whose
cubical candidate is recorded as dead. Relaying "Zaremsky 2.19(c), (d) answered" before that premise is proved
would be wrong. The nodes correctly present themselves as conditional.
