# Referee report (gq-referee-a, proof-gap lens): Nekrashevych groups are finitely presented iff the cycle germ groups are

**Reviewed** (lane bh-self-similar, b86b8f18e, marked priority), read on origin/main:
- `nekrashevych-fp-iff-cycle-germ-groups-fp`;
- its route `nekrashevych-fp-iff-cycle-germ-groups-fp-proof`;
- for consequence 3, the relevant part of `spine-mover-automata-over-fp-bases-are-lift-presented`.

**Verdict: PASS.** There are three nits.
- N1 matters for correctness of the construction: the arrows of `Π` must be indexed by letters of `F`, not by
  automorphisms.
- Theorem A enters only where "finitely generated lift ideal" is translated into "`V_d` finitely presented", as the
  node says. The germ-group statements proper are unconditional given lift-presentability (N2).

## §0 The eventual-state cocycle (the author asked about (Φ2), (Φ3) and (Φ5))
- **The setup.**
  - A stable limit `e` satisfies `e|_y = e`, since `s|_(y^(k+1)) = (s|_(y^k))|_y`. So `e(y^ω) = e(y)^ω`.
  - `Ω` is `G`-invariant, because `t|_c ∈ S` and `𝒪` is closed.
  - `obj` depends only on the tail.
  - `Φ_ξ(t)` is independent of the choice of `c`, and it is an arrow from `obj(ξ)` to `obj(tξ)`. ✓
- **(Φ2).** `ψ(t̄) = ψ(t)^(−1)` gives `t|_(t̄(c')) = overline((t̄)|_(c'))`. So the eventual letter of `t` at `t̄ξ` is the
  formal inverse of that of `t̄` at `ξ`, the two arrows are mutually inverse, and `Φ_ξ(tt̄) = id`. ✓
- **(Φ3).** At `ξ = zξ'`, the letter `t_n` has eventual value `(t_n|_z)|_(c'y^k)`, which is that of `t_n|_z` at
  `ξ'`. The next input point is `t_n(z) · t_n|_z(ξ')`, exactly as in the definition of `w|_z`. Trivial letter sections
  give identity arrows. ✓
- **(Φ4).** It is the case "`w` a word, `c` a prefix" of (Φ3). There are finitely many reduced words of length at
  most `|r|`. ✓
- **(Φ5), paths to words.**
  - Each `e_i` receives `y_i` and keeps itself, so `ŵ(p)` fixes `y`, `ŵ(p)|_y = ŵ(p)`, and `Φ_(y^ω)(ŵ(p)) = p`.
  - On injectivity: in a reduced path, consecutive letters `e_i = ē_(i+1)` with `y_i = e_(i+1)(y_(i+1))` would give
    mutually inverse arrows.
  - The word, together with the start object, determines the path, since `y_(i−1) = e_i(y_i)`. So `ŵ` is injective on
    each hom-set. ✓
- **(Φ5), the germ map.**
  - Its kernel is `K_y`, because `ŵ(p)(y^kv) = y^kŵ(p)(v)`.
  - It is onto. Take `g` with `gy^ω = y^ω`, so `g(y^k) = y^k`. Along the trajectory of `y^ω`, each letter's section
    at the length-`k` prefix reaches its eventual value, so `w|_(y^k) = ŵ(Φ_(y^ω)(w))` for large `k`, with trivial
    letters dropped (N3). Both maps then act on `y^kX^*` as `y^kv ↦ y^k·(same)(v)`. ✓
- **The germ groupoid.** It has finitely many objects and generating arrows. So it is finitely presented iff its
  vertex groups are, using a maximal tree in each component. ✓

## §1 Necessity (the author asked about this)
- `R_C` is finite by (Φ4). Its elements are closed paths, because relators fix `y^ω`, and they lie in `K`, because
  their germ is the germ of a relator.
- **The stages.**
  - Along trivially acting words, `Φ` is multiplicative.
  - A conjugate `Φ_ξ(gug^(−1))` is a path conjugate of `Φ_(g^(−1)ξ)(u)`, via `Φ_(g^(−1)ξ)(g) = Φ_ξ(g^(−1))^(−1)`.
  - Inverses are handled the same way.
  - `M_0`: `Φ_(cy^ω)(r) = Φ_(y^ω)(red r|_c) ∈ R_C`.
  - Successor: for `u ∈ L(M_α)` and `ξ = zξ'`, `Φ_ξ(u) = Φ_(ξ')(u|_z)` with `u|_z ∈ M_α` and `ξ' ∈ Ω`.
  - Limits: unions.
- **The conclusion.** `p = Φ_(y^ω)(ŵ(p)) ∈ D` for `p ∈ K_y`, so `K = D`. Transporting `R_C` along a maximal tree
  makes `K_y` finitely normally generated in the finitely generated free group `π_1(Π,y)`. ✓

## §2 The criterion under (P1) (the author asked about this)
- **At level `r = lcm`.**
  - A cycle state `s` has `s|_(u_s) = ν^r s = s`, with `u_s = ℓ(s)ℓ(νs)⋯`. Every other level-`r` section descends in
    the component order.
  - So (P1) holds at level `r`, the only arrows are the loops `[s, u_s]`, and every letter of `X^r` is stable, since
    descents are finite.
  - Non-loop letters carry no arrows, so their germ groups are trivial. ✓
- **Cycling relators are `ŵ(K)`.**
  - At level `r`, `ν = id` on loop states, so "cycling" means "special".
  - A special word is `ŵ(p)` for a composable path `p`. It is closed when the word is a relator, because it fixes its
    input letter.
  - So the cycling relators are exactly `ŵ(K)`. ✓
- **The direction ⇐.**
  - `p ∈ ⟨⟨R_C⟩⟩_Π` gives `ŵ(p) ∈ ⟨⟨ŵ(R_C)⟩⟩_F`, because `ŵ` is a groupoid morphism into `F`.
  - Then the cycling node, applied to the level-`r` action (refereed PASS at 270990024), gives
    `N = ⟨⟨ŵ(R_C)⟩⟩_lift`.
  - Theorem A and regrouping finish the argument. ✓

## §3 Descent (the author asked about this)
- **Non-loop inputs.** The letter `e_n` receives `z ≠ y = ℓ(e_n)`, and it outputs `e_n(z) ≠ e_n(y_n) = ℓ(e_(n−1))`.
  By induction, every letter receives a non-loop letter.
- **The factor `B`.** So `w|_z ∈ B`. Each generator `s|_(z')` lies strictly below `s`. Prepending the loop of `s`
  lengthens any cycle chain, so the degree is at most `m − 1`.
- **The embedding.**
  - The map `p ↦ ŵ(p)` has kernel `K_y`, so `G_(y^ω)` is the group of automorphisms `ŵ(π_1(Π,y))`.
  - Its wreath recursion off `y` is a homomorphism into `B ≀ Sym(X^r∖y)`.
  - A trivial image forces `w` to act trivially on every `y^kzv`, by `w|_y = w`. So the map is injective. ✓
- **The consequences.**
  - *Degree 0.* `B` is finitary, hence finite, which is consistent with Nekrashevych's theorem for bounded automata.
  - *Spine-Grigorchuk.* The germ group at `2^ω` is `⟨ŝ_γ⟩ ≅ Γ`, and at `1^ω` it is `V_4`.
  - *The odometer.* At `1^ω`, `Π` has a tree edge `[a,1] : 1 → 0` and a loop `[b,1]`, so the germ group is
    `⟨b⟩ ≅ Z`.
  - All of these match the landed nodes. ✓
- **Consequence 3, the spine-mover.**
  - `{2, 3}` is closed and stable. `ŝ_p` loops at 2 and dies at 3, `n` loops at 3 with output 2, and `n^(−1)` loops
    at 2 with output 3.
  - `Π` on `{2,3}` has the loops `[ŝ_p, 2]` and the tree edge `[n,3]`. So `π_1(Π,2)` is free on the `ŝ_p`, and
    `G_(2^ω) ≅ P`, because `p ↦ ŝ_p` is injective.
  - So "`M(P)` lift-presented ⟹ `P` finitely presented" follows from the §1 argument, and the converse is the
    spine-mover theorem. ✓

## Nits
- **N1 (§0, `Π`).** Index the arrows by letters of `F`, meaning `S_0` together with formal inverses, and put
  `[ē, y] := [e, ē(y)]^(−1)`. As written ("for each state `e ≠ 1` … `[e^(−1), e(y)]` is taken as the inverse"), an
  involutive state with `e(y) = y` would give an arrow equal to its own inverse, so `Π` would not be free. Grigorchuk's
  `b` at `y = 111` after regrouping is an example. With formal letters, everything in §§0–3 goes through verbatim.
- **N2 (the Statement).** §1 uses only `N = ⟨⟨R⟩⟩_lift`. Record the unconditional form: a lift-presented action has
  finitely presented germ groups at every closed stable family. Consequence 3's direction "lift-presented ⟹ `P` fp" is
  then free of Theorem A. "`V_4(M(Γ))` is not fp" still uses Theorem A's necessity half.
- **N3 (§0, onto).** Say that `Φ_(y^ω)(w)` may be an unreduced path, and that `ŵ` of it equals `w|_(y^k)` after
  trivial letter sections are dropped. Say also that `g(y^k) = y^k` is what lets the two germs be compared on
  `y^kX^*`.
