---
rg: 2
id: thompson-f-two-transitive-rigid-stabilizers-fix-no-point-proof
kind: route
title: The complement of the rigid-stabilizer locus is an equivariant closed set, and its extreme disagreement point is an antisymmetric invariant
target: thompson-f-two-transitive-rigid-stabilizers-fix-no-point
requires:
  - thompson-f-two-transitive-actions-are-faithful
---

Assume some `F_U^c` fixes a point. By `thompson-f-two-transitive-actions-are-faithful`
the action is faithful and `[F,F]` (the compactly supported elements) acts
transitively.

**Step 0 (invariant relations).** An `F`-invariant relation
`R ⊆ {(ω1,ω2) : ω1 ≠ ω2}` is empty or everything, by 2-transitivity. So an
invariant `R` that is antisymmetric (never `R(ω1,ω2)` and `R(ω2,ω1)` together)
must be empty.

**Step 1 (the locus).** For `ω ∈ Ω` let `O_ω` be the union of all open
intervals `U` with `F_U^c ≤ F_ω`, and `C_ω = (0,1) \ O_ω`. Since
`g F_U^c g^{-1} = F_{gU}^c` and `F_{gω} = g F_ω g^{-1}`, we get
`O_{gω} = g O_ω` and `C_{gω} = g C_ω`. `O_ω` is open, so `C_ω` is closed in
`(0,1)`. By transitivity and the assumption, every `O_ω` is nonempty.

**Step 2 (`C_ω ≠ ∅`).** *Fragmentation:* if `U, V` are overlapping open
intervals then `F_{U∪V}^c = ⟨F_U^c, F_V^c⟩`. Let `f ∈ F_{U∪V}^c`, with
`U = (u1,u2)`, `V = (v1,v2)`, `u1 < v1 < u2 < v2`, and pick a dyadic
`p ∈ (v1,u2)`. Then `f(p)` is dyadic and lies in `U` or in `V`, and so does
`p`. So there is `h ∈ F_U^c ∪ F_V^c` with `hf(p) = p`: F is transitive on
dyadic points of any dyadic subinterval containing both. Then `hf` fixes `p`
and splits as a product of an element supported in `[·,p]` and one supported
in `[p,·]`, both in `F` with compact support in `U` and in `V` respectively.
So `f ∈ ⟨F_U^c, F_V^c⟩`.

Now if `O_ω = (0,1)`, any `f ∈ [F,F]` has support in a compact `[s,t]`,
covered by finitely many intervals from the family `{U : F_U^c ≤ F_ω}`. Merge
overlapping ones by fragmentation (the family is closed under these unions):
`f ∈ F_U^c ≤ F_ω` for a single `U`. So `[F,F] ≤ F_ω`, and since `[F,F]` is
normal it fixes every point. That contradicts faithfulness, so `C_ω ≠ ∅`.

**Step 3 (a gap endpoint).** Fix `ω` and a component `J = (a,b)` of `O_ω`,
with `0 ≤ a < b ≤ 1`. Since `C_ω ≠ ∅`, `J ≠ (0,1)`, so `a ∈ C_ω` or
`b ∈ C_ω`.

*Case `a > 0`.* Choose dyadics `c < a < d < b` and `g ∈ F` supported in
`[c,d]` with `g(t) > t` on `(c,d)`. Put `C = C_ω` and `C' = C_{gω} = gC`.
- `g` is the identity on `[0,c] ∪ [d,1]`, so `C` and `C'` agree there.
- `C ∩ (a,d) = ∅`, so `C' ∩ (g(a),d) = g(C ∩ (a,d)) = ∅` and
  `C ∩ (g(a),d) = ∅`.
- `g(a) ∈ C'`, and `g(a) ∈ (a,d) ⊂ J`, so `g(a) ∉ C`.
Hence `Δ := C Δ C'` is contained in `(c, g(a)]` and contains `g(a)`. So
`sup Δ = g(a) ∈ C' \ C`, and in particular `gω ≠ ω`.

Define `ρ(ω1,ω2)`: `C_{ω1} ≠ C_{ω2}`, `s = sup(C_{ω1} Δ C_{ω2}) < 1`, and
`s ∈ C_{ω2} \ C_{ω1}`. Elements of `F` are increasing homeomorphisms of
`[0,1]` fixing `1`, and `C_{fω} = fC_ω`, so `ρ` is `F`-invariant. It is
antisymmetric by definition. By Step 0, `ρ = ∅`, but `ρ(ω, gω)` holds.
Contradiction.

*Case `a = 0`.* Then `b < 1` and `b ∈ C_ω`. Symmetrically, use `g` supported
in `[c,d]` with `c < b < d`, `c > 0`, `g(t) < t` on `(c,d)`, and the invariant
antisymmetric relation `λ(ω1,ω2)`: `inf(C_{ω1} Δ C_{ω2}) > 0` and lies in
`C_{ω2} \ C_{ω1}`. The same computation gives `inf Δ = g(b) ∈ C_{gω} \ C_ω`.
Contradiction.

So no `F_U^c` fixes a point. ∎

Remark: the argument uses only that `F` acts on `(0,1)` by increasing
homeomorphisms, with fragmentation and the push elements `g`.
