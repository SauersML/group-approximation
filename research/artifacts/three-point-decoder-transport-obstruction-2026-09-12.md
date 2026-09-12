# Three-point decoder transport: the reciprocal-memory bound, and why amplification does not reduce to it

Lane `w4-three-point`, 2026-09-12. Mathematics on paper only. Convention `tau(x)(g) = mu((x(gm))_(m in M))`;
a left inverse `sigma` has memory `N` with `sigma tau = id` and `x(g) = nu((y(gn))_(n in N))`, `y = tau(x)`.

## 0. Question

`three-point-decoder-memory-injective-ca-are-surjective`: if `tau` on `A^G` is injective and has a left inverse
of memory `N = {e, s, t}`, is `tau` surjective? Two-point decoder memory is closed
(`amenable-decoder-memory-forces-surjectivity`, since `<s>` is cyclic hence amenable), so the content is
`<s, t>` nonamenable. The target node proposes reducing to domination of the random-order transport
(`injective-ca-random-order-transport-is-dominated`) for the automaton amplified by
`strict-automata-give-injective-ca-with-skewed-site-marginals`, and flags "whether the amplification keeps three
points" as the first step. This note settles that step (no) and records exactly what the transport identity gives.

## 1. The transport identity gives only a reciprocal bound

**Proposition 1.** For every group `G`, finite alphabets `A`, `B`, and injective automaton `kappa : A^G -> B^G`
with left-inverse memory `N` containing `e`,

    H( kappa(x)(e) )  >=  (1 / |N|) log |A| ,

under the uniform product measure on `A^G`.

*Proof.* Write `y = kappa(x)`, fix the i.i.d. order labels `U` (independent of `x`). For each `n in N` the
transport term is `A_n = E_U I( x(n^-1) ; y(e) | y(n^-1 N ∩ past(e)), U )`. For every fixed realization of `U`,

    I( x(n^-1) ; y(e) | Z_n )  <=  H( y(e) | Z_n )  <=  H( y(e) ) ,

and `H(y(e))` does not depend on `U` because `U` is independent of `(x, y)`. So `A_n <= H(y(e))` for each of the
`|N|` terms. By the transport identity (`injective-ca-random-order-transport-identity`), `sum_(n in N) A_n = log |A|`.
Hence `log |A| <= |N| · H(y(e))`. QED

**Remark 1.1 (this is the whole of what transport yields).** The per-term bound `A_n <= H(y(e))` is tight: a single
term can equal `H(y(e))` (take the conditioning to recover `x(n^-1)` from `y(e)`, as in the bijective `Z`-example,
artifact `random-order-decoder-transport` 2.5, where one term reaches the full site entropy). So no argument that
bounds the transport sum term by term can do better than Proposition 1. Domination, `sum A_n <= H(y(e))`, asks for
the reciprocal `1`, i.e. `H(y(e)) >= log |A|`; by Corollary 2 of the transport artifact that **is** the goal restated.
Thus the transport identity, together with the only general upper bound on its terms, proves the site-entropy bound
with constant `1/|N|`, and nothing sharper. For `|N| = 1` this is exact (`kappa(x)(e)` determines `x(e)`); for every
`|N| >= 2` there is a gap, and as `|N| -> infinity` the bound degrades to `0`.

**Corollary 1.2.** Any proof of the three-point case must beat `1/3`: it has to supply an upper bound on the transport
sum that is *not* a sum of the per-term entropy bounds. Equivalently, it must use that `y` is a finite block code of
i.i.d. `x` (realizability), not merely the information-theoretic relations among the seven sites
`{e, s, t, s^-1, s^-1 t, t^-1, t^-1 s}`.

## 2. The two available mechanisms, and why both fall short at three points

**2.1 The amenable mechanism (covers `|N| = 2`, and `|N| = 3` with `<s,t>` amenable).** By
`amenable-decoder-memory-forces-surjectivity`, if the decoder memory group `Gamma = <s, t>` is amenable then `tau`
is surjective: `sigma` restricts coset-by-coset on `G / Gamma` to a surjective automaton `sigma_0` over `Gamma`; the
Garden-of-Eden theorem for the amenable `Gamma` makes `sigma_0` pre-injective; so `sigma` is pre-injective over `G`,
hence bijective, and `tau = sigma^{-1}` is onto. This uses amenability of `Gamma` through GOE, not the transport
identity. It already settles every `|N| = 2` case (`<s>` cyclic) and every `|N| = 3` with `<s, t>` amenable
(finite, virtually cyclic, infinite dihedral, `Z^2`, lamplighter, ...). So the claim is non-vacuous exactly when
`<s, t>` is nonamenable.

**2.2 Why the mechanism stops.** When `Gamma = <s, t>` is nonamenable, `sigma_0` is a surjective automaton over a
nonamenable group, and the GOE direction surjective `=>` pre-injective can fail there (Bartholdi: every nonamenable
group carries a surjective non-pre-injective automaton). So 2.1 does not run. The residual open statement is exact:

> a surjective automaton `sigma_0` over `Gamma` that arises as the coset restriction of a *global* left inverse
> `sigma` (right inverse `tau = sigma_0^{-1}` coset-wise is not assumed; only `sigma sigma`-left-inverse structure)
> must be shown pre-injective.

Nothing on main forces this for nonamenable `Gamma`.

**2.3 Caution on "the free case is already true".** The target node's Attempts say "`<s, t> = F_2` is sofic, hence
already true". Soficity here is of the *decoder memory group* `Gamma`, **not** of the host `G`. The coset argument of
2.1 reduces the free case to pre-injectivity of a surjective automaton over `F_2`, and GOE's surjective `=>`
pre-injective direction fails on `F_2`. So this justification does not go through as written; the free-`Gamma` case
needs its own argument and should be treated as open, not cited as settled. (Recorded as a caution, not a refutation:
the conclusion may still hold for another reason.)

## 3. Amplification enlarges the decoder memory

**Proposition 2.** Let `tau` be strict with decoder memory `N_tau` and let `kappa` on `(A^(k+1))^G` be the injective
automaton of `strict-automata-give-injective-ca-with-skewed-site-marginals`. Then every left inverse of `kappa` has
memory containing `N_tau ∪ W_anchor ∪ W_block`, where `W_anchor` is the window needed to locate the self-separating
anchor pattern on `Omega Omega^{-1}` in track `0`, and `W_block` is the anchored-block window of the greedy recoding.
In particular `|memory(kappa)| > 3` whenever the anchor and block windows are not already inside a three-point
`N_tau`, which is the generic case.

*Proof.* To recover `x` from `y = kappa(x)`: (i) read track `0` to decide which sites are anchored — this needs a
window large enough to recognize the self-separating pattern, i.e. `W_anchor` supported on powers along
`Omega Omega^{-1}`; (ii) on each anchored block, invert the fixed greedy injection — this reads the whole block,
`W_block`, bounded by the anchor separation `rho^{-1}`; (iii) invert `tau` on tracks `1..k` — this uses `N_tau`. Each
step is necessary: dropping (i) loses the block boundaries, dropping (ii) loses the skewed coordinate, dropping (iii)
loses tracks `1..k`. Hence the left-inverse memory contains the union. QED

**Corollary 3.1 (the reduction in the target's Attempts is indirect).** `tau` strict `=>` `kappa` has a skewed
single-site law `=>` single-site domination fails *for `kappa`*. So "domination for `tau` surjective" runs through
domination for `kappa`, whose memory is `N_tau ∪ W_anchor ∪ W_block`, not three points. Proving domination for the
class of three-point-decoder automata therefore does **not** establish
`three-point-decoder-memory-injective-ca-are-surjective` by amplification. Two honest readings remain:
- **As an `h_fin` statement.** Read the target as: every injective automaton whose left-inverse memory is three
  points has `H(site) >= log |A|`. This is the clean statement the transport analysis addresses, and it is a special
  case of `injective-ca-images-have-full-single-site-entropy` restricted to three-point decoders. It does not claim
  surjectivity of any ambient strict `tau`.
- **As a surjectivity statement.** Attack single-site domination for the amplified `kappa` of memory
  `N_tau ∪ W_anchor ∪ W_block` directly; the reciprocal bound (Proposition 1) then gives only
  `H(site) >= (log|A^(k+1)|) / |memory(kappa)|`, which is weaker than `log |A|`.

## 4. Where the inequality sits

- The three-point domination (`h_fin` reading) is a finite information inequality among the entropies of `y` at the
  seven sites, averaged over the `2^6` order patterns on those sites, with `Gamma`-relations entering only by making
  sites coincide (artifact `random-order-decoder-transport` 3.3).
- Proposition 1 shows Shannon inequalities plus the transport identity yield only the reciprocal bound `1/3`. The gap
  to `1` is exactly the synergy between the three conditionings, and closing it needs realizability, matching 2.2:
  even the `|N| = 2` case is true only through amenability of the cyclic decoder group, not through any entropy
  inequality.
- **No proof, no counterexample.** A counterexample would be an injective three-point-decoder automaton with
  `H(site) < log |A|`, over a host where `<s, t>` is nonamenable; none is known, and its seven-site information
  pattern would be directly checkable against the Leavitt hosts.
