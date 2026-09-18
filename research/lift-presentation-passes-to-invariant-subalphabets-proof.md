---
rg: 2
id: lift-presentation-passes-to-invariant-subalphabets-proof
kind: route
title: The restriction map of free groups commutes with the recursion, so the preimage of the restricted lift ideal is a lift ideal containing R
target: lift-presentation-passes-to-invariant-subalphabets
requires: [rover-nekrashevych-fp-iff-finite-lift-presentation]
---

Notation as in the claim. For `w ∈ F` and `x ∈ X`, write `w|_x` for the word-level section and `perm(w)`
for the root permutation. The recursion `ψ(w) = ((w|_x)_{x ∈ X}, perm(w))` is a homomorphism
`F -> F ≀ Sym(X)`, and likewise `ψ̄` for `F̄`, `W`.

**1. π commutes with the recursion.**
- *The claim.* For every `w ∈ F`: `perm(π(w)) = perm(w)|_W`, and `π(w)|_x = π(w|_x)` for `x ∈ W`.
- *Well defined.* `perm(w)` preserves `W`, since every state does. So
  `w ↦ ((π(w|_x))_{x ∈ W}, perm(w)|_W)` is a homomorphism `F -> F̄ ≀ Sym(W)`. The coordinate
  permutation it uses is the restriction of `perm(w)` to `W`.
- *Agreement on generators.* On a letter `s` it gives `((\overline{s|_x})_x, s|_W) = ψ̄(s̄)`, because
  sections of the restriction are restrictions of sections. If `s̄ = 1`, then every `s|_x` with
  `x ∈ W` also restricts to `1`, so both sides are trivial.
- *Conclusion.* The two homomorphisms `ψ̄ ∘ π` and this map agree on generators, hence everywhere.

**2. The preimage of a lift ideal is a lift ideal.** Let `M'` be a lift ideal of `F̄` and put
`M = π^{-1}(M')`.
- *Normal.* `M` is normal, since `π` is a surjective homomorphism.
- *Lift-closed.* Let `w ∈ F` have `perm(w) = 1` and every `w|_x ∈ M` (`x ∈ X`). Then
  `perm(π(w)) = 1`, and for `x ∈ W`, `π(w)|_x = π(w|_x) ∈ M'`. As `M'` is lift-closed, `π(w) ∈ M'`,
  so `w ∈ M`.

**3. The theorem.**
- *Setup.* Let `M' = ⟨⟨π(R)⟩⟩_lift`. Relator kernels are lift ideals: if `perm(w) = 1` and every
  `w|_x` acts trivially, then `w` acts trivially. As `π(R) ⊆ π(N) ⊆ N̄`, we get `M' ⊆ N̄`.
- *The chain of inclusions.* By step 2, `π^{-1}(M')` is a lift ideal containing `R`, so it contains
  `⟨⟨R⟩⟩_lift = N`. Hence `π(N) ⊆ M'`. With (RL), `N̄ = π(N) ⊆ M' ⊆ N̄`.
- *Translation.* If `V_{|X|}(G)` is finitely presented, the necessity half of Theorem A gives a finite
  `R`. The sufficiency half, applied to `S̄` on `W^*`, makes `V_{|W|}(Ḡ)` finitely presented.
  Theorem A requires `|W| >= 2`, a finite section- and inverse-closed generating set, and a faithful
  action on `W^*`, all of which hold here.

**4. The sufficient condition for (RL).** Let `S' ⊆ S` be section-closed and inverse-closed, mapping
onto `S̄ \ {1}`, with restriction injective on `⟨S'⟩`.
- Choose a set map `κ: S̄ \ {1} -> S'` with `\overline{κ(t)} = t`, closed under inverses (possible
  because `S'` is), and extend it to `κ: F̄ -> F(S') <= F`. Then `π ∘ κ = id`.
- For `w̄ ∈ N̄`, the element `κ(w̄)` of `⟨S'⟩` restricts to the identity of `W^*`. By injectivity it is
  trivial, so `κ(w̄) ∈ N` and `w̄ = π(κ(w̄)) ∈ π(N)`.

**5. The calibration and the application.**
- *Persistent Grigorchuk.* The persistent action is faithful on `{0,1}^*`, since it restricts to the
  standard action. So step 4 applies with `S' = S`. The two finite-presentation facts are cited in the
  claim.
- *Wächter–Weiß.* Step 4 applies with `S'` the check-mark states with continuation `id`. By step 1b of
  `finite-commutator-wachter-weiss-groups-are-not-fp-proof`, they generate `C_id`, which restriction
  maps isomorphically onto `C`. They are section-closed: sections are again such states, or `id`
  after `$` and at `Σ̃`-letters. `∎`
