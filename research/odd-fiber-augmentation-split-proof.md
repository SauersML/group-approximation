---
rg: 2
id: odd-fiber-augmentation-split-proof
kind: route
title: Split each fiber into its parity and its augmentation part, which Maschke's complement makes equivariant
target: binary-shifts-over-odd-fibers-split-off-the-augmentation-shift
requires:
  - passive-fixing-injective-automata-are-surjective
artifacts:
  - research/artifacts/gk3-binary-descent-2-2026-09-14.md
---

**Item 1.**
- Since `|P|` is odd, `Σ_t 𝟙(t) = |P| = 1` in `F_2`, so `F_2^P = F_2·𝟙 ⊕ I_P`. The parity of `z(g)` is
  `s(g) + |P| s(g) = 0`, so `z(g) ∈ I_P`, and `z(g) + s(g)𝟙 = x(g,·)` recovers `x`. So `Θ` is a bijection.
- Its coordinates read only the fiber `{g} × P`, so `Θ` and `Θ^(-1)` are continuous.
- Translation: `s((h,u)·x)(g) = Σ_t x(h^(-1)g, u^(-1)t) = s(x)(h^(-1)g)`, because `t ↦ u^(-1)t` is a
  bijection of `P`. Likewise `z((h,u)·x)(g) = x(h^(-1)g, u^(-1)·) + s(x)(h^(-1)g)𝟙 = u·z(x)(h^(-1)g)`, since
  `u·𝟙 = 𝟙`.

**Item 2.**
- `β × θ` is continuous and commutes with the action described in item 1: `β` commutes with `G` and
  `P` acts trivially on its factor; `θ` commutes with `G` and with the symbolwise `P`-action.
- So `Φ` is continuous and `G × P`-equivariant, and by Curtis–Hedlund–Lyndon it is a cellular automaton over
  `G × P`.
- Injectivity and surjectivity of `Φ` are those of `β × θ`, which are coordinatewise.

**Item 3.** A `P`-fixed `v ∈ F_2^P` is constant, `v = c𝟙` with `c ∈ F_2`, because `P` acts transitively on
itself. It lies in `I_P` iff `c|P| = c = 0`. The surjectivity statement is
`passive-fixing-injective-automata-are-surjective` over the alphabet `I_P` with passive set `{0}`.

**Item 4.**
- Over `F_2`, `x^q - 1 = (x - 1)Φ_q(x)`, and `Φ_q(1) = q = 1 != 0`, so the factors are coprime. The Chinese
  remainder theorem gives `F_2[x]/(x^q - 1) ≅ F_2[x]/(x - 1) × F_2[x]/(Φ_q(x))`.
- The augmentation ideal is the kernel of `x ↦ 1`, which is the second factor, with `x` acting by
  multiplication. Hence `u·v = ζv` for the generator `u`, and equivariance is `f(ζu) = ζ f(u)`.
- `Φ_q` factors over `F_2` into `(q - 1)/d` irreducible factors of degree `d = ord_q(2)`, so `R_q` is a
  product of that many copies of `F_(2^d)` (standard cyclotomic factorization over finite fields).
