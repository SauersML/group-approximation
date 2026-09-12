# Three-point decoder transport: the elementary memory bound, and the amplification step

Lane `w4-three-point`, 2026-09-12. Mathematics on paper only. Convention `tau(x)(g) = mu((x(gm))_(m in M))`;
a left inverse `sigma` has memory `N` with `sigma tau = id` and `x(g) = nu((y(gn))_(n in N))`, `y = tau(x)`.

**Corrections (Section 5 lists them).**
- **Second landing** (after w3-vf-positive's note on the first landing, e87f4c60f5).
  - Proposition 1 has a direct subadditivity proof, and the tightness remark is withdrawn.
  - Proposition 2 was landed as a lower bound on every left inverse, but its argument covered only the constructed
    decoder. It is replaced by Lemma 3.1, and `skewed-marginal-amplification-enlarges-decoder-memory` is reset to OPEN.
- **Third landing** (after w4-vf-positive-b, verification §5).
  - When `tau` avoids a symbol the reduction works (3.1).
  - The open claim is restated for strict `tau` whose missing patterns all need at least two sites.

## 0. Question

`three-point-decoder-memory-injective-ca-are-surjective`: if `tau` on `A^G` is injective and has a left inverse of
memory `N = {e, s, t}`, is `tau` surjective? Two-point decoder memory is closed by
`amenable-decoder-memory-forces-surjectivity`, because `<s>` is cyclic, so the content is `<s, t>` nonamenable. The
target node proposes a reduction: dominate the random-order transport
(`injective-ca-random-order-transport-is-dominated`) for the automaton amplified by
`strict-automata-give-injective-ca-with-skewed-site-marginals`. It flags "whether the amplification keeps three
points" as the first step. This note records what the transport identity gives and where that step stands.

## 1. The elementary memory bound

**Proposition 1.** For every group `G`, finite alphabets `A`, `B`, and injective automaton `kappa : A^G -> B^G` with
left-inverse memory `N` containing `e`, under the uniform product measure,

    H( kappa(x)(e) )  >=  (1 / |N|) log |A| .

*Direct proof* (w3-vf-positive). `x(e)` is a function of `y|_N`, so
`log |A| = H(x(e)) <= H(y|_N) <= sum_(n in N) H(y(n)) = |N| · H(y(e))`. The last step uses shift invariance of the
image law. QED

*Second derivation.* Bound each transport term `A_n = E_U I(x(n^-1); y(e) | Z_n, U)` by `H(y(e))`, and sum with
`injective-ca-random-order-transport-identity`.

**Remark 1.1 (what this says about the transport identity).** Bounding each transport term by `H(y(e))` and summing
gives exactly the subadditivity bound, so the identity adds nothing at that level. Domination (Corollary 2 of the
transport artifact) is the constant-`1` statement, and it is equivalent to the goal.
- **Not sharp:** over amenable groups every injective automaton already has `H(y(e)) >= log |A|`.
- **Not the best elementary constant** (w4-vf-positive-b). The counting bound
  `H(y(e)) >= log |A| · sup_F |F| / |F N|` has Proposition 1 as its `F = {e}` case. For `N = {e, s, t}` with `s, t`
  generating a free semigroup, the positive words `F_L` of length at most `L` give `F_L N = F_(L+1)`, so the ratio
  tends to `1/2`. It stays below `1` when `<N>` is nonamenable.

**Remark 1.2 (where a proof has to look).** The sharper per-term bound `A_n <= H(y(e) | Z_n, U)` gives
`sum_n H(y(e) | Z_n, U) >= log |A|`. That is not domination, because the three conditionings differ, so a proof has
to use the `Z_n` jointly. I found no Shannon-type derivation of domination at three points. I have not shown that
none exists; that would need an entropy vector at the seven decoder sites that satisfies every constraint of the
block-code structure and violates domination.

## 2. The amenable mechanism, and where it stops

**2.1.** By `amenable-decoder-memory-forces-surjectivity`, if `Gamma = <s, t>` is amenable then `tau` is surjective.
- `sigma` restricts coset by coset on `G / Gamma` to a surjective automaton `sigma_0` over `Gamma`.
- Garden of Eden makes `sigma_0` pre-injective.
- So `sigma` is pre-injective, hence bijective, and `tau = sigma^(-1)` is onto.

This uses amenability of `Gamma`, not the transport identity. It settles every two-point case, and every three-point
case with `<s, t>` amenable.

**2.2.** When `Gamma` is nonamenable, the step "surjective implies pre-injective" can fail over `Gamma`. By a result
attributed to Bartholdi, every nonamenable group carries a surjective, non-pre-injective automaton; I have not
re-read the source, and nothing here depends on it. So 2.1 does not run, and nothing on main shows that a surjective
`sigma_0` arising as the coset restriction of a global left inverse is pre-injective.

**2.3 Caution on the free case.** The target's Attempts say "`<s, t> = F_2` is sofic, hence already true". Soficity
there is of the decoder memory group, not of the host `G`. Two gaps:
- the amenable mechanism reduces the free case to pre-injectivity of a surjective automaton over `F_2`, where 2.2
  applies;
- the joint law of `y` at the seven decoder sites depends on the encoder windows `gM`, so on relations of `G` outside
  `<s, t>`. The free-decoder inequality is not a statement about `F_2` alone.

So the free-`Gamma` case should be treated as open, not cited as settled. This is a caution, not a refutation.

## 3. The amplification step

The left inverse built in the skewed-marginal construction first undoes the recoding, then applies a left inverse of
`tau` on tracks `1..k`. To undo the recoding at a site it reads the anchor window and the block window,
`X = Omega^(-1)(Omega Omega^(-1) ∪ Omega)`. So the constructed left inverse has memory `N_tau X`
(w4-vf-positive-b, verification §5).

**3.1 When `tau` avoids a symbol, the reduction works** (w4-vf-positive-b). Suppose the image of `tau` avoids one
symbol. Take `Omega = {e}`:
- `Omega Omega^(-1) = {e}`, anchors are the sites where track `0` shows the fixed symbol, and blocks are single sites;
- `X = {e}`, so the constructed left inverse has memory `N_tau`, three points;
- the skewing theorem still applies, because the classes are singletons and the last class is empty.

So for every strict three-point-decoder `tau` whose image avoids a symbol, `kappa` is injective, has a three-point
left inverse, and has a non-uniform site law. Three-point domination (the `h_fin` reading of the target) would
exclude every such `tau`.

**3.2 When every missing pattern needs at least two sites.** If `|Omega| >= 2` and `<s, t>` is nonamenable, the
constructed memory has more than three points (w4-vf-positive-b, coset count).
- `e in X`, so `N_tau X = N_tau` forces `N_tau x = N_tau` for every `x in X`.
- Then `N_tau` is a union of left cosets of `<X>`, which contains `e`.
- So `<X> = N_tau`, a subgroup of order `3` (it is not trivial, because `|Omega| >= 2`).
- Then `s, t` lie in a finite group, which contradicts nonamenability.

This bounds the constructed left inverse only. For every left inverse the proved lower bound is:

**Lemma 3.1.** Every left inverse of `kappa` with memory `N` yields a left inverse of `tau` whose memory is contained
in `N`.

*Proof.* Fix a constant configuration on track `0` whose symbol differs from the anchor pattern at some site, so no
anchor occurs anywhere. Fix constant configurations on tracks `2..k`. On these inputs no block is recoded, so
`kappa(x) = (x_0, tau(x_1), tau(x_2), ..., tau(x_k))`, and every output track except track `1` is constant (`tau`
sends constants to constants). Plug those constant tracks into the track-`1` coordinate of the left inverse. The
result is an automaton with memory contained in `N` that sends `tau(x_1)` to `x_1`. QED
(Verified by w4-vf-positive-b.)

**Consequence.**
- **`tau` avoiding a symbol:** the reduction on the target runs as stated (3.1).
- **Every missing pattern needs at least two sites:** the reduction is not known to work.
  - It needs a left inverse of `kappa` with three-point memory.
  - The constructed one has more points when `<s, t>` is nonamenable (3.2).
  - Lemma 3.1 bounds every left inverse below only by a left-inverse memory of `tau`.

  That class is the open claim `skewed-marginal-amplification-enlarges-decoder-memory`. For it there are two honest
  readings of the target:
  - the `h_fin` statement for three-point-decoder automata, a special case of
    `injective-ca-images-have-full-single-site-entropy`;
  - a surjectivity statement whose transport route runs through the constructed `kappa`, where Proposition 1 gives
    only `H >= log |A^(k+1)| / |memory|`.

## 4. Status

- **Three-point domination** (the `h_fin` reading) is an information inequality among the outputs at the seven sites
  `{e, s, t, s^(-1), s^(-1)t, t^(-1), t^(-1)s}`, averaged over the random order, with the inputs at `e, s^(-1), t^(-1)`.
  The law of `y` there also depends on the encoder windows (2.3).
- **No proof and no counterexample.** A counterexample would be an injective automaton with a three-point left
  inverse, `<s, t>` nonamenable, and `H(site) < log |A|`. None is known.

## 5. Corrections

1. **Proposition 1** (second landing). Adopted w3-vf-positive's direct proof. Withdrew the remark that the per-term
   bound is attained and that no term-by-term argument beats `1/|N|`: attainment holds only for one order realization
   in the `Z` example, and averaged it is `3/2 < 2`. Old Corollary 1.2 ("a proof must use realizability, not only the
   information relations") is now Remark 1.2, stated as what I did not find, not as an impossibility.
2. **Proposition 2** (second landing). Withdrew the lower bound on every left inverse, and replaced it with Lemma 3.1.
   `skewed-marginal-amplification-enlarges-decoder-memory` was reset to OPEN, and its proof route deleted.
3. **Section 2.3** (second landing). Sharpened the free-case caution with the encoder-window dependence, and flagged
   the Bartholdi attribution as not re-read.
4. **Section 3** (third landing, w4-vf-positive-b §5).
   - Added the constructed-memory formula `N_tau X`, the case `Omega = {e}` (3.1), where the reduction works, and the
     coset count (3.2).
   - The second landing said the reduction "is not known to work" for every `tau`. That now holds only for `tau` whose
     missing patterns all need at least two sites.
   - The open claim is restated for that class.
   - Remark 1.1 now notes that the counting bound does better than `1/|N|`.
