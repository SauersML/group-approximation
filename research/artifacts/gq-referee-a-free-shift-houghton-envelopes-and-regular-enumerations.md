# Referee report (gq-referee-a, proof-gap lens): free-shift Houghton-like envelopes are not finitely presented, and regular enumerations

**Reviewed** (lane bh-map, 6362d6c31), read on origin/main:
- `free-shift-houghton-like-envelopes-are-not-fp`, with its route `free-shift-houghton-envelopes-local-stability-proof`;
- `regular-enumerations-can-make-near-shift-free-product`, with its route `regular-free-shift-fresh-trajectory-proof`.
  This node carried no status line. It is the subject of W1 in my report on the Houghton-like germ node (01bc75a40).

**Verdict: PASS for both.** There are three nits.
- With this review, `regular-enumerations-can-make-near-shift-free-product` has one proof-gap referee. So item 4 of the
  free-shift node, and item 5 of `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`, no longer rest on a
  node with no status. That discharges my earlier W1, once the node records a status line.
- For the citation lens: Mallery–Zaremsky Observation 5.1 and Proposition 5.10.

## 1. `regular-enumerations-can-make-near-shift-free-product`
- **The extension step.**
  - Evaluate right to left.
  - At a `P`-syllable `g ≠ 1`, the input `u` is not yet a value of `ν`. Choose `h` and `gh` outside the finite assigned
    domain; `h ≠ gh` because `g ≠ 1`. Set `ν(h) = u`, and set `ν(gh) = v` with `v` fresh.
  - Then `λ_g(u) = ν(gν^(−1)u) = v`.
  - Choosing `v` large puts the end `v + c` of the following shift block on a fresh, nonnegative integer. The last
    choice makes the endpoint differ from `n`.
  - Pure shift words, and the one-syllable case, are handled. Every assignment persists under extension. ✓
- **Genericity.**
  - "Some `n > M` is a defined moved point of `w`" depends on finitely many values of `ν` and `ν^(−1)`, so it is
    open.
  - It is dense by the extension step.
  - The space of bijections, with the two-sided topology of finite prescriptions, is Polish.
  - A comeagre `ν` moves infinitely many points for every nonidentity reduced `w`. So `w ≠ 1` in `NearSym(N)` modulo
    finitary permutations, and `P * ⟨s⟩ → R_ν` is injective. ✓
- **Effectivity.** The word problem of `P` decides normal forms of `P * ⟨s⟩` and all the finite exclusions.
  Interleaving the witness requirements with the two totality requirements gives a computable `ν` and `ν^(−1)`. ✓

## 2. `free-shift-houghton-like-envelopes-are-not-fp`
- **The strand shape of the `K`-letters.**
  - `E_2` is the group of permutations with `π(x+2) = π(x)+2` eventually, so off a finite set it maps each parity
    strand to a strand by a translation.
  - `H_n(E_2)` is the same on each ray.
  - The exceptional set `E` depends only on the `K`-letters of `w`, not on `ν` (N2). ✓
- **Item 1, regular trajectories (the author asked about this).**
  - The strand sequence and the formal element `u_j(w) ∈ P * ⟨ŝ⟩` depend only on `j` and `w`.
  - For `ν`: cofinitely many points of strand `j` are regular. `w(ν) = 1` makes the end strand `j`, and the image of
    `u_j(w)` in `R_ν` is trivial. Injectivity then gives `u_j(w) = 1`.
  - The reduction of `u_j(w)` to the empty word uses the identities `λ'_gλ'_h = λ'_(gh)`, `λ'_1 = id`,
    `s^as^b ⊆ s^(a+b)` as partial maps, and `s^0 = id`. These hold for every `ν'`.
  - So every `ν'`-regular trajectory is fixed by `w(ν')`. ✓
- **Item 1, exceptional trajectories (the author asked about this).**
  - A `ν'`-exceptional trajectory passes through a point `(e, i)` with `e ∈ E`. It is computed from there forward and
    backward.
  - Evaluating `λ'^(±1)_g` at a point `y` needs `ν'^(−1)(y)` and `ν'(g^(±1)ν'^(−1)y)`.
  - If `ν'` agrees with `ν` on the finite set `S` of these preimages and their translates, every such computation is
    the same as for `ν`.
  - So the exceptional trajectories for `ν` and `ν'` coincide, and `w(ν) = 1` there gives `w(ν') = 1` there. ✓
- **Item 2.**
  - With a finite presentation on the finite generating set, the relators survive `ν'`. So `y ↦ y(ν')` is a
    homomorphism fixing `K` pointwise.
  - `r = ρ^(1)_g t ρ^(1)_g^(−1) t'^(−1)` is `1` for `ν`, since `ρ` fixes `z` on the odd strand.
  - For `ν'`, `λ'_g(ν(h)) = ν'(gh) ≠ ν(gh)`, because `ν'(h) = ν(h)`. So `φ(r)` is a 3-cycle.
  - Choosing `h`, `gh` and `h'` outside `S` uses that `P` is infinite. ✓
- **Item 3.**
  - `λ'_g = λ_g` on the even strand, for generators and hence for all `g`.
  - Put `θ = ν^(−1)ν'`. Then `θ(gh) = gθ(h)`, so `ν'(h) = ν(hc)`. ✓
- **Item 4.**
  - For `P = Z` and `n = 3`, the germ group is finitely presented, since `R_ν ≅ F_2` and item 3 of the Houghton-like
    node applies. By item 2 the group itself is not.
  - `ν` exists by §1. So `houghton-like-envelopes-lift-finite-presentation-from-germs` is refuted. ✓
- **The checks.**
  - `n = 1` agrees with the two-sided gate.
  - The zigzag near relation `λ ~ s^2` is destroyed by perturbation far out.
  - Houghton groups have no `ρ`-letters.
  All consistent.

## Nits
- **N1 (free-shift route, item 2).** "`Y` the generating set above" lists `K` itself. Say "a finite generating set
  of `K` together with the `ρ^(k)_g`". Item 1 is applied to words in finitely many `K`-letters.
- **N2 (free-shift route, item 1).** State that `E` depends only on the `K`-letters of `w`, so the same `E` defines
  regularity for every `ν'`. State also that `S` contains, for each exceptional trajectory point `y`, both `ν^(−1)(y)`
  and its translates `g^(±1)ν^(−1)(y)`. Agreement at `ν^(−1)(y)` is what makes `ν'^(−1)(y) = ν^(−1)(y)`.
- **N3 (regular enumerations).** Add the status line, and say that the topology is the two-sided one, with
  prescriptions of `ν` and of `ν^(−1)`. The openness argument and the Baire property both use it.
