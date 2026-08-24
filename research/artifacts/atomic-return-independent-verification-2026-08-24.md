# Independent second reading of the Atomic Morita Return note

**2026-08-24.**  A parallel session ingested the external note *Property-(T)-Free
Non-MF: Atomic Leavitt Gaps, Rank Return, and the Correct Structural Dividing
Line* and landed the region
`atomic-leavitt-gap-on-nonzero-matrix-corner`,
`atomic-morita-return-kills-finite-order-mf-mark`,
`binary-leavitt-atomic-morita-return`,
`binary-leavitt-three-row-atomic-compiler`,
`bounded-prototype-rows-imply-atomic-morita-return`,
`binary-leavitt-heisenberg-is-orthogonal-central-self-copy`,
`orthogonal-root-self-copy-and-normal-generation-are-mf-compatible`,
`finite-rational-rank-flows-are-fd-dense`
and the route `property-t-free-leavitt-via-atomic-morita-return`.

This session was handed the same note and re-derived it independently before
discovering the collision.  Nothing was re-authored; this file is the second
reading, kept because an independent check of a new terminal inequality is
worth recording, and because three findings here are not in the landed nodes.

## Re-derivation: the corner gap is correct

For a nonzero projection `p` in a finite-dimensional C-star algebra and
`s_i,t_i in pAp`, `m>=2`:

```text
m-1 <= sum_i ||t_i s_i - p||_op + ||sum_i s_i t_i - p||_op.
```

Checked line by line and independently of the note's own write-up.
`tau_p = Tr/rank(p)` is a tracial state on the nonzero corner, so
`tau_p(p)=1` and `|tau_p(x)| <= ||x||_op`; cyclicity gives
`tau_p(s_i t_i)=tau_p(t_i s_i)`; the single scalar `tau_p(sum_i s_i t_i)` then
lies within `sum_i ||t_i s_i-p||` of `m` and within `||sum_i s_i t_i-p||` of
`1`, and `|m-1|=m-1`.  The ambient dimension `d` never enters and neither does
`rank(p)/d`.  Confirmed, including the `1/3` value at `m=2` and the growth of
`(m-1)/(m+1)` toward `1`.

The `2||q-UpU^*||_op = ||R_q U R_p U^* - 1||_op` identity of the note's §4.4,
with `R_p = 1-2p`, was also checked and is correct: `R_{p'}` is unitary, so
`||R_q R_{p'} - 1|| = ||R_q - R_{p'}|| = 2||q-p'||`.

The Heisenberg clauses were checked independently: `alpha_i` is a homomorphism
because the central cross term becomes `a(t_i s_i)b' = ab'`; the branches
commute because `t_i s_j = 0`; the intersection is central because
`t_1 s_0 = 0` kills the first coordinate; generation follows from
`a = (a s_0)t_0 + (a s_1)t_1` and its left-handed mirror.  Local finiteness
over `F_q` is correct as written: `A x B x C` with `C` containing `AB` is
closed under both the product law and `(a,b,c)^{-1} = (-a,-b,-c+ab)`.

## Three findings not in the landed nodes

### 1.  Two of the note's "breakthroughs" were already established here.

* **Breakthrough C, cyclic rank monodromy.**  The note's Lemma 4.1
  (`||p-q||_op<1` forces equal rank), Theorem 4.2 (`prod alpha_i = prod
  beta_i`) and Corollary 4.3 (`(1/2)^k != (1/4)^k`) are re-derivations of
  `operator-norm-rank-monodromy-zero`, whose `projection_rank_rigid` and
  `rank_zero_of_power_monodromy` are kernel-checked in
  `GroupApproximation/Sofic/InvolutionRankMass.lean`.  Its Lemma 32.1 is
  `rank-deficient-return-row-has-operator-norm-one`.
* **Breakthrough E, the packet-linearity no-go.**  The rational polyhedral
  scaling argument is what already **refuted**
  `leavitt-prefix-packet-pressure-certificate`, through
  `finite-packet-functoriality-has-positive-regular-profile`, and it is the
  "rational dimension alternative" inside
  `finite-packet-multiplicity-certificates-detect-mf-radicals-proof`.

Neither is new mathematics for this graph; both are correct.

### 2.  The note's §15 and §20 are existing recorded firewalls.

"A universal group-word Leavitt identity would hold in the left regular
representation, and a finite von Neumann algebra has no nonzero properly
infinite projection" is already the *selector cannot be a group-algebra
projection* attempt inside `opnorm-leavitt-coarse-fine-return-row`, and §20 is
`bare-self-copy-mf-calibration` verbatim.

### 3.  Literature: one detail is unverified and must not enter a node.

The note's §34 cites Bachner--Dogon--Lubotzky, *On L^1-approximation of
groups*, arXiv:2508.17392 -- which this graph has already source-verified in
`torsion-free-finitely-presented-non-mf` -- but attaches a **journal
placement, volume 702, an issue date and a DOI** that were not checked in this
session and are not checkable from here.  Those bibliographic details appear in
no node and should not be added to one.  The Fournier-Facio--Rangarajan
Math. Ann. 389 (2024) Example 7.3 pointer was likewise not verified here.

The only status statement anything depends on is the graph's own frontier
entry `property-t-free-leavitt-full-mf-radical [OPEN]`, which needs no
external citation.

## Cross-reference

The companion ingestion in this session,
`research/artifacts/finite-coordinate-conditional-reduction-2026-08-24.md`,
covers a different external document -- the conditional-reduction manuscript
built on the coarse-to-fine *support row* rather than the atomic coefficient
return.  The two open hypotheses are deliberately separate nodes:
`opnorm-leavitt-coarse-fine-return-row` asks for two exact packets on one
carrier and a vanishing support row, `binary-leavitt-atomic-morita-return`
asks for four corner operators and three approximate rows.  The second is the
weaker demand, and the landed `distinct_from` pair records that.
