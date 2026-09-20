# Pre-injective cover pairs: transport, product splitting, collapse on SI domains (2026-09-20)

Worker: swarm-0917-w23-w23-gs-pull, family reframing. Claim: `pre-injective-si-cover-pairs-are-conjugacies`.
Route: `pre-injective-si-cover-pairs-are-conjugacies-proof`, which has the full proof in Steps 1–8.

## 1. How the proof goes

1. *Unique lifts are local.* On an SFT domain, the unique single-site lift is chosen by a finite admissibility
   check (route Step 2). This is where finite type is used.
2. *Near sites first.* Lifts at `h ∉ Φ^-1` never write at `1`. So the value at `1` of any asymptotic lift is
   fixed after lifting the finitely many sites of `Φ^-1`. This is the ordering trick of Theorem P, applied from an
   arbitrary base point `x` instead of a constant. It gives a two-variable automaton `S(x, y)`.
3. *Cocycle.* `S(S(x, y), z) = S(x, z)` holds on asymptotic data by uniqueness, and everywhere by density.
4. *Splitting.* Transporting to the constant image `d^G` gives a retraction `r : X → Z = F^-1(d^G)` and a
   conjugacy `X ≅ Z × A^G` over `A^G`.
5. *Collapse.* `Z` has no asymptotic pairs, by pre-injectivity. If `X` is SI, then `Z` is SI as the retract
   `r(X)`. An SI SFT with no asymptotic pairs has one point, by splicing. So `Z` is a constant and `F` is a
   conjugacy.

## 2. Consistency checks

- *Full shift, `X = A^G`.* The result is the reversibility of pre-injective, post-surjective automata
  (Capobianco–Kari–Taati). That result is not imported and serves only as a check.
- *Theorem P* of `pointed-pre-injective-cover-pairs-admit-sections`. When `X` contains a constant and `F` is
  pre-injective, `S(c^G, ·)` is the section built there.
- *Amenable groups.* No proper SI SFT cover pair exists, by entropy. That agrees with Corollary 2, which says PSD
  is the same as there being no cover.
- *Linear sector* (`linear-proper-domain-duality-is-stable-finiteness`). The counterexample `x ↦ xM²` on
  `(A^G)MN`, which exists when `NM = I ≠ MN`, is not pre-injective. Theorem C constrains only pre-injective
  pairs, so there is no conflict. A pre-injective linear example would have made `G` non-surjunctive.
- *Bijective pairs* `(τ(A^G), τ^-1)` from `injective-automaton-images-are-sft-cover-pairs` are exactly the case
  `Z = {c^G}`. Every such image contains every constant.

## 3. Where SI is used, and a non-SI remark

SI is used only in route Step 7, to make the fibre `Z` a singleton. Without SI, Theorem S still makes a pre-injective
cover pair a product `(Z × A^G, pr_2)`. Here `Z` is an SFT with no asymptotic pairs. When `X ≠ A^G`, it has no
finite orbit over a surjunctive group. An `H`-fixed `z ∈ Z`, with `H` of finite index, makes `S(z, ·)` an
injective `H`-automaton whose image lies in `X ⊊ A^G`, and
inducing it from `H` to `G` gives a non-surjunctive `G`. The fibred map `(z, y) ↦ (z, S(z, y))` is then a strict
fibre automaton over `Z`, of the same kind as the arrow hotels of
`nonamenable-groups-carry-arrow-shift-strict-automata`, with the product embedded in `A^G`. This case lies outside
PSD, which is about SI domains.

## 4. Side data: 3-symbol tree SFTs (not load-bearing)

`experiments/psd-tree-sft-census-2026-09-17/` enumerates nearest-neighbour SFTs on `F_2` with 3 symbols.
- 139 primitive essential relations, and 84 ordered pairs `(E_a, E_b)` with disjoint cones. Those pairs have no
  invariant measure, hence no periodic point.
- 0 of the 84 pass the path-mixing test, which SI requires.
- The obstruction is a persistent non-full cyclic word: always `ab` at `n = 3`, and `ab` or `aB` in an `n = 4`
  random sample.
- This is consistent with w22's census and with Poirier–Salo's suspicion. It proves nothing beyond the finite
  range.
