# Three-point decoder transport: the elementary memory bound, and the amplification step

Lane `w4-three-point`, 2026-09-12. Mathematics on paper only. Convention `tau(x)(g) = mu((x(gm))_(m in M))`;
a left inverse `sigma` has memory `N` with `sigma tau = id` and `x(g) = nu((y(gn))_(n in N))`, `y = tau(x)`.

**Corrections, first landing e87f4c60f5 (Section 5 lists them).** Proposition 1 has a direct subadditivity proof, and
the tightness remark is withdrawn. Proposition 2 was landed as a lower bound on every left inverse, but its argument
only describes the constructed decoder. It is replaced by Lemma 3.1, and the claim
`skewed-marginal-amplification-enlarges-decoder-memory` is reset to OPEN.

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
gives exactly the subadditivity bound. So the identity adds nothing at that level. The constant `1/|N|` is not claimed
to be sharp: over amenable groups every injective automaton already has `H(y(e)) >= log |A|`. Domination (Corollary 2
of the transport artifact) is the constant-`1` statement, and it is equivalent to the goal.

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

The decoder built in the skewed-marginal construction reads three windows:
- `W_anchor`, the window on track `0` that recognises the self-separating anchor pattern on `Omega Omega^(-1)`;
- `W_block`, the anchored-block window, to invert the greedy recoding;
- `N_tau`, to invert `tau` on tracks `1..k`.

That shows one left inverse reads `N_tau ∪ W_anchor ∪ W_block`. It does not bound every left inverse. The first
landing argued "each step reads sites the others do not", which is a property of that decoding procedure only. The
lower bound actually proved is:

**Lemma 3.1.** Every left inverse of `kappa` with memory `N` yields a left inverse of `tau` whose memory is contained
in `N`.

*Proof.* Fix a constant configuration on track `0` whose symbol differs from the anchor pattern at some site, so no
anchor occurs anywhere. Fix constant configurations on tracks `2..k`. On these inputs no block is recoded, so
`kappa(x) = (x_0, tau(x_1), tau(x_2), ..., tau(x_k))`, and every output track except track `1` is constant (`tau`
sends constants to constants). Plug those constant tracks into the track-`1` coordinate of the left inverse. The
result is an automaton with memory contained in `N` that sends `tau(x_1)` to `x_1`. QED

**Consequence.** The reduction proposed on the target node is not known to work.
- It needs a left inverse of `kappa` with three-point memory.
- The construction supplies one reading `N_tau ∪ W_anchor ∪ W_block`.
- Lemma 3.1 bounds the memory of `kappa` below only by a left-inverse memory of `tau`.

Whether some amplification keeps three points is the open claim `skewed-marginal-amplification-enlarges-decoder-memory`
(stated as the enlargement, which would block the reduction). Until it is decided there are two honest readings of
the target:
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

## 5. Corrections to the first landing (e87f4c60f5)

1. **Proposition 1.** Adopted w3-vf-positive's direct proof. Withdrew the remark that the per-term bound is attained
   and that no term-by-term argument beats `1/|N|`: attainment holds only for one order realization in the `Z`
   example, and averaged it is `3/2 < 2`. Old Corollary 1.2 ("a proof must use realizability, not only the information
   relations") is now Remark 1.2, stated as what I did not find, not as an impossibility.
2. **Proposition 2.** Withdrew the lower bound on every left inverse, and replaced it with Lemma 3.1.
   `skewed-marginal-amplification-enlarges-decoder-memory` is reset to OPEN, and its proof route is deleted.
3. **Section 2.3.** Sharpened the free-case caution with the encoder-window dependence, and flagged the Bartholdi
   attribution as not re-read.
