---
rg: 2
id: recursive-lef-growth-hosts-miss-some-fp-rf-group-proof
kind: route
title: The depth of a finitely presented subgroup is bounded by the LEF growth of the host
target: recursive-lef-growth-hosts-miss-some-fp-rf-group
requires: [kms-fp-rf-groups-with-arbitrarily-large-depth]
artifacts:
  - research/artifacts/sk-wp-host-2026-09-13.md
---

Notation as in the target. All generating sets are finite and symmetric. A *partial model* of `B_U(r)` is a map as in
the definition of `L_U(r)`.

**Step 1 (monotonicity).** `B_U(r) ⊆ B_U(r+1)`, and the restriction of a partial model of `B_U(r+1)` is a partial
model of `B_U(r)`. So `L_U` is non-decreasing.

**Step 2 (subgroups).** Let `ι: Γ = ⟨S⟩ → U` be an injective homomorphism and `C ≥ 1` the largest `T`-length of an
`ι(s)`, `s ∈ S`. Then `ι(B_Γ(r)) ⊆ B_U(Cr)`. If `φ` is a partial model of `B_U(Cr)`, then `φ∘ι` is injective on
`B_Γ(r)`. For `g, h, gh ∈ B_Γ(r)` the elements `ι(g), ι(h), ι(gh)` lie in `B_U(Cr)`, so `φ(ι(gh)) = φ(ι(g))φ(ι(h))`.
Hence `L_Γ(r) ≤ L_U(Cr)`.

**Step 3 (finite presentation).** Let `S` be symmetric and `Γ = ⟨S | R⟩` a quotient of the free group `F(S)` on the
letters of `S`. Here `R` is finite, contains the relators `s·ŝ` pairing each letter with the letter of its inverse,
and every relator has length at most `m`. Let `n ≥ m` and let `φ` be a partial model of `B_Γ(n)` in `Q`.
- From `1·1 = 1` in the ball we get `φ(1) = 1`.
- Let `ψ: F(S) → Q` be the homomorphism with `ψ(s) = φ(s)`. By induction on length, `ψ(v) = φ(v̄)` for every word `v`
  of length at most `n`, where `v̄ ∈ Γ` is its value. The case of the empty word holds, and for `v = v's` the elements
  `v̄'`, `s` and `v̄` lie in `B_Γ(n)`, so `φ(v̄) = φ(v̄')φ(s) = ψ(v')ψ(s) = ψ(v)`.
- Every relator `ρ` has length at most `m ≤ n` and value `1`, so `ψ(ρ) = φ(1) = 1`. So `ψ` induces a homomorphism
  `ψ̄: Γ → Q` that agrees with `φ` on `B_Γ(n)`.
- If `w ≠_Γ w'` have length at most `n`, then `ψ̄(w̄) = φ(w̄) ≠ φ(w̄') = ψ̄(w̄')` by injectivity of `φ`. So `ψ̄`, onto
  its image of order at most `|Q|`, separates `w` and `w'`.

Hence `ρ_Γ(n) ≤ L_Γ(n)` for `n ≥ m`, for the depth function computed on `S`.

**Step 4 (part (a)).** Suppose `U` is LEF and `L_U ≤ h` with `h` recursive.
- Replacing `h` by `n ↦ max_{k≤n} h(k)` keeps it recursive and makes it non-decreasing. Put `f(n) = h(n²)`, which is
  recursive.
- By `kms-fp-rf-groups-with-arbitrarily-large-depth` there is a finitely presented residually finite `Γ = ⟨X⟩` with
  `ρ_Γ(n) > f(n)` for all `n`. The group `Γ` has a finite presentation on `X`, say with relators of length at most `m`.
- Suppose `Γ` embeds in `U`, with the constant `C` of Step 2 for the generating set `X`. For `n ≥ max(m, C)`,
  Steps 3, 2 and 1 give
  `ρ_Γ(n) ≤ L_Γ(n) ≤ L_U(Cn) ≤ h(Cn) ≤ h(n²) = f(n) < ρ_Γ(n)`,
  a contradiction. So `Γ` does not embed in `U`.

**Step 5 (part (b)).** This is the contrapositive of (a).

**Step 6 (part (c)).** Let `U = ⟨T⟩` be LEF with solvable word problem. For given `r`:
- list the words of length at most `r`, and group them into the elements of `B_U(r)` using the word problem;
- for two elements, decide whether their product equals an element of `B_U(r)`, and which one;
- for `N = 1, 2, …`, enumerate the multiplication tables of groups of order `N` and all maps `B_U(r) → Q`, testing
  injectivity and the partial multiplication.

The first success gives `L_U(r)`, and the search stops because `U` is LEF. So `L_U` is recursive, and (a) applies with
`h = L_U`.

**Model tests.**
- Finite `U`: `L_U` is bounded, and (a) says `U` misses an infinite finitely presented residually finite group, which
  is true.
- `U = Z`: `L_U(r) = 2r+1`, and (a) says some finitely presented residually finite group, e.g. a nonabelian free group,
  does not embed; true.
- The universal hosts of `simple-kazhdan-lef-host-for-countably-many-rf-groups` contain every finitely presented
  residually finite group, so (b) forces their LEF growth to outgrow every recursive function. This is consistent,
  since nothing there bounds their finite models.
