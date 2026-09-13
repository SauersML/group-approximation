---
rg: 2
id: plo-i-group-is-ea-iff-its-orbital-germ-kernels-are-proof
kind: route
title: "Proof: slope germs at orbital ends reduce elementary amenability of PL_o(I) subgroups to compactly supported kernels"
target: plo-i-group-is-ea-iff-its-orbital-germ-kernels-are
requires: []
---

Notation as in the target claim.

**(1).** `A` is a component of the open set `supp(H)`, so its endpoints are not in
`supp(H)` (or are `0`, `1`); every `h ∈ H` fixes `a` and `b`. Since `h` has finitely
many breakpoints, on some `[a, a+ε]` it is affine and fixes `a`:
`h(x) = a + λ_h (x − a)` with `λ_h > 0`. For two such maps,
`(h ∘ k)(x) = a + λ_h λ_k (x − a)` near `a`, so `χ_a^H(h) = λ_h` is a homomorphism.
It depends only on `h` near `a` inside `[a,b]`, so it factors through `H_A`. The same
holds at `b`. The kernel of `(χ_a^H, χ_b^H): H_A → ℝ_{>0}²` is `K_A(H)_A`.

**(2).** If `h ∈ K_A(H)` then `λ_h = 1` near `a` and near `b`, so `h` is the identity
on `[a, a+ε] ∪ [b−ε, b]` for small `ε`.

**(3).** Let `S` be a finite generating set. A point is fixed by `H` iff it is fixed
by every `s ∈ S`, so `supp(H) = ⋃_{s ∈ S} supp(s)`. For a PL map with finitely many
breakpoints, `x ↦ s(x) − x` is affine on finitely many pieces, so its zero set is a
finite union of points and closed intervals, and `supp(s)` is a finite union of open
intervals. A finite union of finite unions of open intervals has finitely many
components. An element that is the identity on every orbital fixes `supp(H)` and the
fixed point set, so it is the identity: restriction to `∏_i H_{A_i}` is injective.

**(4).** If `H` is EA, each `H_{A_i}` (a quotient) and `K_{A_i}(H)_{A_i}` (a subgroup
of it) are EA. Conversely, by (1) each `H_{A_i}` is an extension of `K_{A_i}(H)_{A_i}`
by an abelian group, hence EA; a finite product of EA groups is EA (iterated
extensions), and by (3) `H` is a subgroup of `∏_i H_{A_i}`. For the last sentence, `H`
is the directed union of its finitely generated subgroups, and EA is closed under
directed unions and subgroups.

**(5).** By (3) and (4), some `(D_0)_{A_0} = H_{A_0}` is not EA. Suppose `D_i` is
finitely generated with orbital `A_i` and `P = (D_i)_{A_i}` not EA. The germs at the
ends of `A_i` depend only on the restriction to `[a_i, b_i]`, so
`K_{A_i}(P) = K_{A_i}(D_i)_{A_i}`, and `P` is a finitely generated group acting on
`[a_i, b_i]` with orbital `A_i`. By (4) applied to `P`, `K_{A_i}(D_i)_{A_i}` is not
EA, and by the directed-union clause it has a finitely generated subgroup `Q` that is
not EA. Lift a finite generating set of `Q` to `K_{A_i}(D_i)` and let `D_{i+1}` be the
subgroup these lifts generate, so `D_{i+1} ≤ K_{A_i}(D_i) ≤ D_i` and
`(D_{i+1})_{A_i} = Q`.

By (2) each lifted generator has support in `A_i` contained in a compact subinterval
of `A_i`, so by the argument of (3) `supp(D_{i+1}) ∩ A_i` is a finite union of open
intervals `B_1, …, B_k` with closures inside `A_i`. Their endpoints lie in `A_i` and
are fixed by `D_{i+1}`, so each `B_j` is an orbital of `D_{i+1}`, and `Q` embeds in
`∏_j (D_{i+1})_{B_j}`. Since `Q` is not EA, some `(D_{i+1})_{B_j}` is not EA; set
`A_{i+1} = B_j`. Then `D_{i+1}` is finitely generated, `(D_{i+1})_{A_{i+1}}` is not EA,
and the closure of `A_{i+1}` lies in `A_i`. Induction gives the infinite sequence.

**Model tests.** `ℤ ≀ ℤ = ⟨t, g⟩` with `t` one bump on `(0,1)` and `g` a bump on an
interval `J` whose translates `t^n(J)` are pairwise disjoint: `K_{(0,1)}` is the
normal closure of `g`, a direct sum of copies of `ℤ`; every finitely generated
subgroup of it has abelian projections on its orbitals, so the descent stops after
one step, as it must for an EA group. For standard `F = ⟨x_0, x_1⟩`, `K_{(0,1)}(F) =
[F,F]`, which contains compactly supported copies of `F`, and the descent never
stops, as (5) predicts for a non-EA group.
