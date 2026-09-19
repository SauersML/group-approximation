---
rg: 2
id: compiled-bs-stable-letters-are-never-rediagonalized
kind: claim
title: In a compiled BS(1,m) inside (k+1)V no element outside Z[1/m] admits a brick-diagonal power-conjugacy, so the renormalization compiler cannot be stacked into Baumslag-Solitar chains
distinct_from:
  higman-chain-group-pbh-iff-chain-configuration: that reduces the BS chain group G_1 to finding a chain configuration (a, b, c) in some B_A group; this proves the configuration cannot come from compiling a compiled BS(1,m) a second time, and gives the positive form of the remaining route.
  brin-thompson-aperiodic-elements-have-logarithmic-movement: that bounds movement of aperiodic elements of nV; this is an exact drift obstruction for one specific construction step.
---

**ESTABLISHED** through `compiled-bs-stable-letters-never-rediagonalized-proof`. Elementary lane
proof (bh-invent-08), not reviewed.

**Setting.**
- `T ∈ kV` is an odometer of an `m`-ary code `e`, for example SMART_m in `2V`.
- `s = T × id` and `u = g^{-1}` are the compiled pair in `(k+1)V`, with `g(e_i x, y) = (x, c_i y)`.
  They satisfy `u s u^{-1} = s^m`, and `⟨s, u⟩ ≅ BS(1,m) = Z[1/m] ⋊ ⟨u⟩`.

**Theorem.** Let `b ∈ ⟨s,u⟩ \ Z[1/m]` and `l >= 0`. Then there is NO brick code `e'` on
`C^{k+1+l}`, of any arity `m' >= 2`, with `δ_{e'}(b × id) = (b × id)^{m'}`.

In particular, no stable-letter element of any compiled `BS(1,m)` (e.g. those in `3V`) is itself
renormalizable, in any dimension.

**Consequences.**
1. **Chains cannot be compiled twice.** The chain configuration of
   `higman-chain-group-pbh-iff-chain-configuration` asks for `a b a^{-1} = b^{m'}`, `b c b^{-1} = c^m`,
   with `c` of infinite order. Applying the compiler twice, with `c = s` and `b` the first stable
   letter, never yields one.
2. **Positive form: the chain compiler.** Suppose some `kV` contains `b, c` with `b c b^{-1} = c^m`,
   `c` of infinite order, and a brick code `e'` with `δ_{e'}(b) = b^{m'}`. Then one compile step
   (applied to the `δ_{e'}`-closure of `⟨b, c⟩`) gives `a ∈ (k+1)V` with
   `a (b × id) a^{-1} = (b × id)^{m'}`. So `(a, b × id, c × id)` is a chain configuration in `(k+1)V`.
   The chain problem is thus a same-dimension design problem. It needs a DRIFT-FREE element `b` of
   `kV` that already conjugates an infinite-order `c` to `c^m` inside `kV`, without a fresh coordinate,
   and that also has a diagonal power identity. Every such `b` has zero drift for all invariant
   measures (`brick-diagonal-power-conjugacy-forces-zero-drift`).
3. **Scope.** This is an obstruction to one construction, not a non-embedding theorem. Chains built by
   other means, for example a drift-free SMART-type `b` acting inside the old coordinates, are not
   excluded.

**Lesson for general BH.** The renormalization compiler has a direction. Each application spends one
fresh coordinate and creates a conjugator with strictly signed drift there. Conjugators with signed
drift are exactly the elements that can never be renormalized. So hierarchies (BS chains, the Higman
cycle `H4`, Baumslag–Gersten) cannot be built by stacking compiler steps: every rung above the first
must come from zero-drift dynamics inside the existing coordinates.

That is the precise sense in which the remaining one-relator and Higman targets need a new
same-dimension mechanism, not more dimensions. The mechanism has to be reversible machines whose
renormalization map is itself renormalizable.
