# Referee report (gq-referee-a, proof-gap lens): RCWA groups satisfy Boone–Higman

**Reviewed:** `rcwa-groups-satisfy-boone-higman` (222a364e8) and its route
`rcwa-groups-bh-via-sign-doubling-and-odometer-host-proof`, read on origin/main. The coordinator asked for this review.

**Verdict: PASS.** There are three nits and one dependency note.
- For the citation lens:
  - Li, Example ex:ZS (III) and the assumptions of thm:deg;
  - Matui's Theorem simple2;
  - FKPS homology and Li's AH corollary.
  The quotes are in `research/artifacts/gq-affq-kep-odometer-host.md` §1.

## Step 1: sign doubling
- **The cocycle and the action.**
  - Slope signs multiply, so `ε_(gh)(n) = ε_g(h n) + ε_h(n)`.
  - `g·(n,i) = (g n, i + ε_g(n))` is an action, which I checked by composing. It is faithful.
  - `φ` is a bijection onto evens ⊔ odds.
- **The table.** All four rows check.
  - For odd `u`, `δ(g)(u) = (au + a − 2b − c)/c` on `ε = 0`, with slope `σ`. The case `ε = 1` has slope `−σ`.
  - The classes are `2r (mod 2m)` and `−2r−1 (mod 2m)`, and `ε` is constant on each.
  - Multipliers are unchanged, and the modulus is `2m`. So `δ(RCWA_P) ⊆ RCWA_P`, and the image is class-wise
    increasing. ✓

## Step 2: extension to `Ẑ_P`
- **Images and shifts.** Integrality of `(a(r+tm)+b)/c` for all `t` gives `c | am`. So each image is the class
  `s_i(n_i)` with `n_i = am/c`, which is `P'`-smooth and positive. Then `h(r_i + tm) = s_i + (t + c_i)n_i`. ✓
- **Boxes.** In `Ẑ_P` with `P'`-smooth moduli, `B(s,n)` meets `B(s',n')` iff `s ≡ s' (mod gcd(n,n'))` iff the classes
  meet. So the image boxes are disjoint, and their union is a clopen set containing `Z`, hence everything.
- **The extension.** `ĥ` is a homeomorphism extending `h`. By density, `h ↦ ĥ` is an injective homomorphism. ✓

## Step 3: the self-similar action and the embedding
- **Carry arithmetic.** I checked this against the two-step computation:
  - `r + n + mr' = ((r+n) mod m) + m((r'+q_1) mod m') + mm'q_2`, with `q_1 = ⌊(r+n)/m⌋` and `q_2 = ⌊(r'+q_1)/m'⌋`;
  - the bracketed residue lies in `[0, mm')`.
  So the residue and the carry agree with the direct computation. ✓
- **Pseudo-freeness.** `a^n` fixes `(m,r)` iff `m | n`, with restriction `a^(n/m)`. So it is strongly fixed only
  for `n = 0`. ✓
- **The embedding.** `ι(g)` on `B(r_i,m) × C` is exactly `μy ↦ λ(a^(c_i)·y)`, with `μ = ((m,r_i),∅)`,
  `λ = ((n_i,s_i),∅)` and `a^c` acting as `z ↦ z + c`. ✓

## Step 4: groupoid properties
- **Effective.** Suppose the bisection is the identity on `μνX`.
  - The `z`-coefficients give `M = M'`, and residues in `[0,M)` give `c = 0`.
  - Degrees and unique factorization give `μ = λ`. Pseudo-freeness gives `n = 0`.
  - So `(λ,n,μ)·e_(μν) = e_(μν)`, which is a unit germ (N2). ✓
- **Hausdorff.**
  - With equal degrees, `r_μ + Mz = r_λ + M(z+n)` is independent of `z`, so the fixed set is empty unless
    `(λ,n) = (μ,0)`.
  - With unequal degrees, either the binary equation `μ_*y = λ_*y`, with `|μ_*| ≠ |λ_*|`, has at most one solution,
    or `(m_μ − m_λ)z = const` has at most one solution in each domain `Z_q`.
  - So the unit-germ sets are clopen. ✓
- **The rest.** Essentially principal (Baire), minimal and purely infinite all hold, with the same `U` and `V` as in
  `2V_τ`. ✓

## Steps 5 and 6: `F_∞`, perfect, simple
- **Li's (III).**
  - Colour `p` has `p ≥ 2` edges and the binary colour has 2.
  - The action is degree-preserving.
  - (F) follows from pseudo-free right cancellation.
  - `D^*(w,w) = Z`.
- **The normal form.** `f = h∏σ_(μ_i)^(n_i)` holds with `h ∈ [[G_Λ]]`, and `{λ_iX}` is a partition because `a^(n_i)`
  is bijective on `X`. ✓
- **Perfectness of `[[G_Λ]]`.** `1 − N_* = −1` makes the one-vertex Koszul complex exact, so `H_* = 0`, and AH then
  gives `[[G_Λ]]^(ab) = 0`.
- **The `σ_μ`.**
  - They are all conjugate, via equal-count binary splitting of the complements, and `hσ_μh^(−1) = σ_(μ')`.
  - `σ_μ = σ_(μ(∅,0))σ_(μ(∅,1))`, because `a` fixes binary letters with restriction `a`. So `c = 2c = 0`.
  - `H_P^(ab) = 0`, and Matui's theorem gives simplicity. ✓
- **The calibrations.** Both calibrations check. `ι(t) = σ_((2,0),∅) σ_((2,1),∅)^(−1)`, and the reflection doubles to
  the class transposition `τ_(0(2),1(2))`.

## Dependency note
- The case `P ≠ ∅` uses `ct-p-z-is-a-one-vertex-k-graph-full-group`, which is still marked "not reviewed", for
  Li's thm:deg assumptions on `Λ_P`.
- I checked the elementary `k`-graph facts it supplies:
  - associativity of `(m,r)(m',r') = (mm', r+mr')`;
  - unique factorization by degree, with `r_1 = r mod m_1`;
  - one vertex, and `p` edges of colour `p`.
- I did not re-referee the thm:deg check. The case `P = ∅` rests only on refereed inputs, as the node says.
- Step 2 also re-proves what it borrows from the unreviewed `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`,
  so that node is not needed for correctness here.

## Nits
- **N1 (definitions).** Say in one line that `RCWA_P(Z)` is a subgroup. Moduli of composites and inverses stay
  `P'`-smooth: the preimage classes have modulus dividing `m_h m_g c`, and the inverse pieces have modulus `am/c`.
- **N2 (Step 4, effective).** Phrase the conclusion as `s·e = e` for the idempotent `e` of `μνX`. That is what
  "the germ is a unit" means in `I_l(D) ⋉ X`, since equality of actions alone does not identify germs there.
- **N3 (Step 2).** State `c_i | a_i m` explicitly. It is what makes the image a residue class.
