# Referee report (gq-referee-a, proof-gap lens): periodic germ extensions of V, and the two breakpoint consumers

**Reviewed** (lane bh-linear-fields), read on origin/main:
- the host `periodic-germ-extensions-of-v-are-virtually-simple`, with route `-proof`;
- `rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman`, with route `-proof`;
- `quadratic-breakpoint-psl2z-groups-satisfy-boone-higman`, with route `-proof`.

The BHM hypotheses were checked against the scratch copy of `bhm-2407.03149v1.tex` (151092 bytes). The passages read
were:
- the definition of finite germ extension (the three axioms, before l.170);
- `thm:MainFinitenessTheorem`, `thm:ActualVersion` and `prop:DefinitionSigmap`;
- `thm:SimplicityRefined` and `prop:NormalClosuresEqual`;
- Appendix A, `thm:Stabilizers`;
- the oligomorphy remark (l.591).

**Verdict: PASS for all three.** There are three nits.
- For the citation lens:
  - the BHM theorems as quoted;
  - Lodha's coding, Props 2.3 and 2.5;
  - Lagrange's theorem;
  - Monod's definition of `H(Z)`, which the node says was not re-read at source;
  - the BHM §3.4 example.

## 1. The host
- **The finite-germ-extension axioms, especially localization (the author asked about this).**
  - *Closure.* Composites of admissible germs are admissible, with `(m,π)` then `(m',π')` giving
    `(m + m'∘π, π'π)`, and inverses are admissible.
  - *Axiom (1).* `sing(g) ⊆ P_g`.
  - *Axiom (2).* An element with no singular point agrees locally with `V`, hence with prefix replacements.
    Compactness then puts it in `V`.
  - *Axiom (3).* Take `h = g` on a clopen `C_(uv^K)` that meets `P_g` only in `p`, and complete it on the nonempty clopen
    complements by a prefix-replacement homeomorphism. Then `P_h = {p}`, the germ is admissible, and `h(p)` is tail
    equivalent to `p`, so `h ∈ G_Π`. ✓
  - *The admissible rule really gives a homeomorphism germ.* The image of `C_(uv^K)` is `{q}` together with the cones
    `D_(k',j')(q)` for `k' ≥ K + m_(π^(−1)j')`. This is a cone neighbourhood of `q` plus finitely many side cones, so it
    is clopen. ✓
- **The germ groups.**
  - Every `(m, π)` is realized at `p`, by the localization construction with `K + min m_j ≥ 0`. Distinct pairs give
    distinct germs.
  - So `(G_Π)_p ≅ Z ≀ S_ℓ`.
  - `(V)_p` is the diagonal, by step 1: a prefix replacement fixing `p` has `w = uv^L` (N1). It is central. ✓
- **`A_p = Z/ℓ ⊕ Z/2`, and `G/G'` finite (the author asked about this).**
  - `(m, π) ↦ (Σm, sign π)` is a homomorphism. Its kernel is (sum-zero vectors) `⋊ A_ℓ`, which is the commutator
    subgroup, since `[σ, e_i] = e_(σi) − e_i`. So the abelianization is `Z × Z/2`.
  - The diagonal maps to `(ℓm, 0)`, so `A_p = Z/ℓ ⊕ Z/2`.
  - Off `Ω_Π`, `(G)_p = (B)_p`, so `A_p = 0`. Hence the sum over all `B`-orbits in `thm:ActualVersion` reduces to `Π`.
  - `V ≤ G_Π'`, because `V` is simple and nonabelian, hence perfect. `prop:NormalClosuresEqual` says the same. So
    `ker σ = G'V = G'`. ✓
- **The BHM finiteness hypotheses (the author asked about this).**
  - (1): `V` has type `F_∞`, and `thm:Stabilizers` covers `Fix` and `Stab` of every finite set of rational points.
  - (2): an orbit of `V` on `n`-tuples is fixed by the equality pattern and the tail classes. The disjoint-cone argument
    is correct, and the complements can be made nonempty by extending both prefixes by a common word. `Ω_Π` is
    exactly `|Π|` tail classes, because `Π` has one word per rotation class and the words are primitive.
  - (3): the second alternative applies. `(B)_p` is central, and `(Z^ℓ/diag) ⋊ S_ℓ` is virtually `Z^(ℓ−1)`, hence of
    type `F_∞`.
  - The simplicity hypotheses hold: `V` is simple, locally moving and has no global fixed point, and the orbits agree
    because `V` is transitive on each tail class. ✓
- **`σ(g^(c)) = σ(g)` (the author asked about this).**
  - The transplant's exceptional points are the `cx`, with `D_(k,j)(cx) = c·D_(k,j)(x)` when `cx` is represented
    by `cu`. So its germs are admissible with the same `(m, π)`.
  - For BHM's `σ_p(g) = Σ_q [b_(g(q))^(−1) g b_q]_p`, the germ at `cx` of `g^(c)` equals that of `β'gβ^(−1)`.
  - The splitting into three terms is valid: each factor fixes `p`, as checked through `b_(cx)(p) = cx` and
    `β^(−1)(cx) = x`. The two outer terms are `V`-germs at `p`, which vanish in `A_p`.
  - Singular points of `g^(c)` in `Orb(p)` correspond bijectively to those of `g`. So `σ(g^(c)) = σ(g)`.
  - `Δ` is a product of transplants with disjoint supports, so `σ(Δg) = Eσ(g) = 0` and `Δ(G_Π) ≤ G_Π'`. ✓

## 2. `rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman`
- **The automatic breakpoint condition.** A fixed point of `θ ↦ 2^cθ + e` with `c ≠ 0` satisfies
  `s(2^c − 1) ∈ Z[1/2]`, so `s ∈ Q`. If `c = 0`, a rotation with a fixed point is the identity. ✓
- **The lift.**
  - `q` is injective over non-dyadic points.
  - `g` maps non-dyadic points to non-dyadic points, so the one-sided lifts extend continuously to `p`.
  - The lift is unique by density, which gives an injective homomorphism. ✓
- **Periods.** For `s = r/(2^a b)` in lowest terms with `b > 1` odd, the minimal period is `ord_b(2) ≥ 2`, since
  `2 ≢ 1 (mod b)`. ✓
- **Germs.**
  - `b | r(2^c − 1)` with `gcd(r, b) = 1` gives `ord_b(2) | c`, including for `c < 0`.
  - The scaling `θ ↦ s + 2^(ℓm)(θ − s)` sends the left endpoint of `I_(K+m)` to that of `I_K`, since both lie at
    distance `2^(−|u|−Kℓ) q(v^∞)` below `s` after scaling. So its lift is `uv^(K+m)ζ ↦ uv^Kζ`.
  - `ĝ = α̂_− ∘ ρ`, where `ρ` is the identity on the families with `v_j = 1` and the shift on those with `v_j = 0`. This
    is admissible with `π = id`. ✓

## 3. `quadratic-breakpoint-psl2z-groups-satisfy-boone-higman`
- **The continued-fraction formula.** `φ(0^bξ) = 1/(b + 1/φ(ξ))` holds by induction, and
  `φ(1^(a_0)0^(a_1)⋯) = [a_0; a_1, …]`.
- **The quadratic irrationals.** Periodic run lengths hold iff the sequence is eventually periodic and not constant.
  For an odd run period, the binary period doubles. With Lagrange's theorem, `Φ^(−1)` of the quadratic irrationals is
  `Ω`. ✓
- **The breakpoint trichotomy.** The trichotomy holds, and for `|t| > 2`, `t² − 4` is never a square. ✓
- **The lift.**
  - On preimages of arcs with rational endpoints, taken from the upper preimage to the lower one, the pieces are
    clopen.
  - No gluing is needed at rational breakpoints.
  - At a quadratic `ξ`, the image `γ(ξ)` is irrational, so the lift is continuous. ✓
- **Germs.**
  - The germ of `ĥ` at `p` is a `V`-germ fixing `p`, hence diagonal by host step 1.
  - `Φ` preserves order, so `v_j = 1` gives the left families.
  - `ĝ = γ̂_− ∘ ρ`, with `ρ` shifting only the right families. This is admissible. ✓
- **Finitely many classes, and the scope.**
  - The closure is `bp(gh) ⊆ bp(h) ∪ h^(−1)bp(g)`, and `PSL_2(Z)`-orbits map into single tail classes, because
    `γ̂ ∈ V`.
  - `PP_Z` is not finitely generated. For each quadratic `ξ`, take `h` on the arc `[ξ, ξ']` and the identity elsewhere.
    This gives breakpoints in every one of the infinitely many orbits. ✓

## Nits
- **N1 (host, step 1).** `wv^∞ = u'v^∞` gives `w = u'v^L` when `|w| ≥ |u'|`. Otherwise it gives `u' = wv^(−L)`. So
  allow `L ∈ Z`. The shift `L − K` is unchanged.
- **N2 (rational route, step 3).** Add the breakpoint-closure line from the quadratic route's step 5:
  `bp(gh) ⊆ bp(h) ∪ h^(−1)bp(g)` and `bp(g^(−1)) = g(bp g)`. Then note that the `H`-images of a non-dyadic `s` stay in
  its tail class.
- **N3 (rational route, step 2).** "Lift arc by arc, as for `T`" should say that it lifts on small dyadic
  subintervals. There each dyadic affine piece is a prefix replacement. The arcs themselves need not have dyadic
  endpoints.
