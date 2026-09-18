# Referee report (gq-referee-a, proof-gap lens): FW inputs admit no twisted-normalizing genuine shell action

**Reviewed** (lane bh-kazhdan-inputs), read on origin/main: `fw-inputs-admit-no-twisted-normalizing-genuine-shell-action`
and its route `fw-twisted-normalizing-shell-action-proof`. This is the current version, 2a1326804, which supersedes
7a95cf6d5 and 871f2d315.

**Verdict: PASS for countable `P`, with one required scope fix (W1).**
- **W1.** Step 2.4 uses "countable FW ⇒ FA ⇒ finitely generated", but the statement allows any infinite FW group.
  Every input the node applies to is finitely generated, so nothing downstream changes.
- There are two nits.
- There is an overlap note. At `m = 1`, `fw-inputs-admit-no-twisted-shell-normalization` (gq-typeA-design, PASS
  07944799c) proves the same conclusion without countability.

## Steps 0 and 1
- **`φ` is forced to be an endomorphism (N1).** Under infinite supports, `ρ : P → NearSym(N)` is injective, and
  `Ad(s^(−m))` is an automorphism of `NearSym(N)`.
  - So `ρ_(φ(gh))` is near `s^(−m)ρ_g s^m s^(−m)ρ_h s^m`, which is near `ρ_(φ(g)φ(h))`.
  - Hence `φ(gh) = φ(g)φ(h)`.
  - Step 0 then shows the kernel is trivial. Kernel-trivial ⇒ injective, and "`ρ' = ρ∘φ` is an action" in Step 1,
    both need this line, which the route omits.
- **Straightening.**
  - `g·graph(s^m)` is the graph of `ρ_g s^m ρ'^(−1)_g`, which is near `s^m`.
  - `Γ''` is invariant, because fibre sizes are invariant. It is a bijection between cofinite invariant sets,
    because the complements are finite unions of orbits.
  - `ind(f) = ind(s^m) = m` for either sign of `m`. ✓

## Step 2 (m > 0) (the author asked about this)
- **Orbit classes.**
  - `≈` refines `~`, because `ρ'(P) = ρ(φ(P))`.
  - `f` carries each `≈`-class onto a `~`-class and induces a size-preserving bijection of classes. This is because
    `f^(−1)(ρ(P)f(x)) = ρ'(P)x`.
  - Infinite classes avoid the finite invariant complements, so `I' ⊆ X`, `I ⊆ Y` and `f(I') = I`. ✓
- **1. The residue classes.**
  - For `a ≥ M`: `a ∈ I' ⟺ a + m ∈ I`.
  - With `I' ⊆ I`, each residue class meets `I ∩ [M,∞)` in an initial segment: either the whole tail, or a finite set.
  - The same `r` classes carry `I'` up to a finite set, so `I ∖ I'` is finite. ✓
- **2. The index.**
  - As near permutations of `I`, `f|_(I')` has index `−|I∖I'|`.
  - `s^m` on the `r` full tails `U ⊆ I` has index `r`. This uses that `U` is cofinite in `I` and `f = s^m` on `U`.
  - They agree off a finite set, so `r = 0` and `I = ∅`. Every orbit is finite. ✓
- **3. The sizes.**
  - `|orbit(a+m)| = |≈-class(a)| ≤ |orbit(a)|`. The inequality is right, but the route's wording is not (N2).
  - So sizes are bounded on `[M,∞)` by the maximum over `[M, M+m)`, plus finitely many orbits meeting `[0,M)`. ✓
- **4. The conclusion.** For finitely generated `P` this is correct: there are finitely many maps to `Sym(K)`, and the
  intersection of their kernels acts trivially, hence is trivial. See W1.

## Step 3 (m < 0, φ an automorphism)
- `f^(−1) : (Y,ρ) → (X,ρ')` is equivariant and is near `s^(−m)`.
- `ρ = ρ'∘φ^(−1)`, and `ρ'` has infinite supports because `φ` is bijective.
- Step 2 uses only such an `f` together with "`≈` refines `~`", and both hold here. ✓
- Non-surjective twists for `m < 0` are correctly left open.

## Required fix
- **W1 (Step 2.4, scope).**
  - Steps 1–3 hold for every FW group. Step 2.4 needs `P` countable, so that FA gives finite generation.
  - FW groups can be uncountable (`Sym(N)`, or `F^N` for finite perfect `F`, by Cornulier's strong boundedness). The
    only gap is to rule out an infinite FW group `P` with the following data:
    - a finite quotient `θ : P → Q`;
    - an injective endomorphism `φ`;
    - `θ(φ^j g) ≠ 1` infinitely often, for every `g ≠ 1`.
  - Such data would realize (★) exactly, with `m = |Q|`, by letting `P` act on levels `j` through `θ∘φ^j`.
  - I could not produce such a `P`, and I could not exclude one.
  - So add "countable" (or "finitely generated") to the statement. This loses nothing downstream:
    - discrete Kazhdan groups are finitely generated;
    - `St_N(R_L)`, the Deligne lattice and every Boone–Higman input are finitely generated.
  - Alternatively, prove the uncountable case. At `m = 1`, the gq-typeA-design main-ray argument gives finite supports
    directly and needs no countability. For `m ≥ 2` it gives `m` rays and orbits of size at most `m`, which is the
    same gap.

## Nits
- **N1 (Step 0).** Add the line above: `φ` is a homomorphism because `ρ` is injective into `NearSym(N)`.
- **N2 (Step 2.3).** "the orbit of `a + m` is `f` of the `≈`-class of `a`, which lies inside the orbit of `a`" should
  read: "… whose size is that of the `≈`-class of `a`, and that class lies inside the orbit of `a`." The image itself
  need not lie in the orbit of `a`.

## Overlap note (for team-lead and both lanes)
- This node, at `m = 1`, and `fw-inputs-admit-no-twisted-shell-normalization` (gq-typeA-design) prove the same
  window-zero exclusion by different mechanisms: index counting here, and main-ray following there.
- Each should name the other in `distinct_from`, and say that this one covers `|m| ≥ 2`.
