---
rg: 2
id: wachter-weiss-check-mark-automaton-is-not-lift-presented
kind: claim
title: The full Wächter–Weiß check-mark automaton is not lift-presented, because its germ group at 0^ω is (Z wr Z) x Z; the same holds for the binary encoding whenever L is not 2 mod 3, which kills the own-action candidate of the PSPACE route for those L
distinct_from:
  single-configuration-check-mark-group-is-lift-presented: that is the one-configuration layer (no # letter, so Z|_γ = 1), which is lift-presented; this adds the skip state K at # and shows the lift presentation is lost, because the germ group at 0^ω grows from <Z,N> to <Z,N,K>, which is (Z wr Z) x Z.
  finite-commutator-wachter-weiss-groups-are-not-fp: that shows the groups G_R are not finitely presented; this shows the weaker property the Boone–Higman route actually needs, lift presentation of V_2(C), also fails for L not 2 mod 3.
  nekrashevych-fp-iff-cycle-germ-groups-fp: that is the general germ-necessity principle; this applies it to one explicit automaton and computes the germ group.
  lift-presentation-passes-to-invariant-subalphabets: that reduces the own action of G_R to V_2(C); this settles V_2(C) negatively for L not 2 mod 3.
  fp-simple-group-with-pspace-complete-word-problem: that is the target; this kills only one candidate overgroup (the own action) of one route to it.
artifacts:
  - research/wachter-weiss-check-mark-automaton-is-not-lift-presented-proof.md
  - experiments/check-mark-lift-2026-09-17/cm.py
  - experiments/check-mark-lift-2026-09-17/results.txt
---

**ESTABLISHED** by `wachter-weiss-check-mark-automaton-is-not-lift-presented-proof` (lane proof by hand,
elementary, not independently reviewed; no priority claimed). Part 1 in lift-ideal form is unconditional. The
translations into "V is not finitely presented", and part 2, go through Theorem A of
`rover-nekrashevych-fp-iff-finite-lift-presentation`, which is not yet refereed. Part 2 uses it by way of
`lift-presentability-is-invariant-under-level-regrouping`. The finite checks in `cm.py` are consistency checks
of the hand computations (output in `results.txt`), not inputs to the proof.

## The automaton

The alphabet is `X' = {0, 1, #, $} ∪ Γ`. Write `g = π(g_0, g_1, g_γ, g_#, g_$)`, with the same section
`g_γ` for every `γ ∈ Γ`. Here `σ` swaps `0` and `1` and fixes the other letters.

```text
A  = σ(Z, A', 1, 1, 1)     A' = σ(N, A', 1, 1, 1)
Z  =  (Z, N,  K, 1, 1)     N  =  (N, N,  A, 1, 1)     K = (K, 1, K, A, 1)          (CM)
```

This is the check-mark automaton of Wächter–Weiß (arXiv:1906.03424v3, Figure
`fig:checkmarkingAutomaton`), unencoded, with continuation `id`. `A` is the check-mark state, `A'` its
carry, `Z` "block zero so far", `N` "block nonzero, continue", and `K` the skip state, which acts only
at `#`. `C' = ⟨A, A', Z, N, K⟩`.

The **binary encoding** `C` (paragraph "Encoding over Two Letters") uses `|Γ| = 2^L` and the codes
`0 = 100`, `1 = 101`, `# = 110`, `$ = 111`, `γ_i = 0·bin_L(i)`. Its states are `(p, x)`, where `p` is a
state of (CM) and `x` is a proper prefix of a code. The state `(p, x)` echoes bits until the code is
complete, then outputs the last bit of the image code and moves to `(p|_a, ε)`.

## Statement

1. **Unencoded.** `{0, 1}` is a closed family of stable letters for the state set of (CM). The germ group
   of `C'` at `0^ω` is `H = ⟨Z, N, K⟩ ≅ (Z ≀ Z) × Z`, which is not finitely presented. Hence:
   - the action of `C'` on `X'^*` is not lift-presented, which is unconditional by
     `nekrashevych-fp-iff-cycle-germ-groups-fp`, part 1, in lift-ideal form;
   - `V_{|X'|}(C')` is not finitely presented, by Theorem A.
2. **Encoded, `L ≢ 2 (mod 3)`, `L >= 1`.** At level 3, `{100, 101}` is a closed family of stable letters
   for the state set of `C`. The only loop states at `(100)^ω` and `(101)^ω` are the aligned states
   `(p, ε)` with `p` a loop of (CM). The germ group of `C` at `(100)^ω` is again
   `⟨(Z,ε), (N,ε), (K,ε)⟩ ≅ H`. Hence `V_2(C)` is not finitely presented.
3. **Consequence for the PSPACE route.** For finite `R` and `L ≢ 2 (mod 3)`, `V_{|Σ|}(G_R)` is not
   finitely presented, by the application in `lift-presentation-passes-to-invariant-subalphabets`. So
   in `pspace-fp-simple-via-lift-presented-automaton-overgroups`, the own action of `G_R` is not a
   lift-presented overgroup. Step 2 there needs a genuinely new overgroup `G'`, one that kills the
   lamplighter germ.
4. **Open case `L ≡ 2 (mod 3)`.** Here a misaligned γ-phase persists along `(100)^ω` and `(101)^ω`. So
   extra loop states `(K, x)`, with `x` a proper γ-prefix, enter, and the germ group at `(100)^ω` becomes
   `P' = ⟨H, (K,x) (x misaligned), (A',ε)(K,x')(A',ε)^{-1}⟩`.
   - For `L = 2`: `P' = ⟨Z, N, K, K_1, K_2, A'K_1A'^{-1}⟩`, with `K_1 = (K,00) = (K,01)` ("skip one bit,
     then K") and `K_2 = (K,0)` ("skip two bits, then K").
   - Of the 21 pairwise commutators of these generators, only `[Z,K]` and `[K_00, K_01]` are trivial
     (`results.txt`).
   - Whether `P'` is finitely presented is open. Since `L` can be enlarged by padding `Γ`, a route may
     restrict to `L ≡ 2`, and the own-action candidate survives only there.

## Lesson

- The skip layer, not the check-mark layer, breaks lift presentation. The one-configuration layer is
  lift-presented (`single-configuration-check-mark-group-is-lift-presented`).
- Adding the skip state `K` turns the germ at `0^ω` into a lamplighter, through the relations
  `[K, A^n K A^{-n}] = 1`. These hold because every section of `⟨A,K⟩` past a `#` is a power of `A`, so
  every conjugate of `K` acts by a base element of an abelian wreath base.
- This answers the "ray retraction" question of `research/artifacts/gq-bh-bh-free-02-check-mark-layers.md`.
  The retraction needed there is germ necessity at the closed stable family `{0,1}`, which was already
  available.
