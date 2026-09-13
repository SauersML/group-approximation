# Idea lane nh-approx-lifting: approximate representations of central extensions of Kazhdan groups (2026-09-13)

Target: `non-hyperlinear-group`. Lens: approximate (Hilbert–Schmidt) representation theory of
non-residually-finite central extensions of Kazhdan groups, above all Deligne's covers of `Sp_4(Z)`.

Status: ideas and kill tests only. Nothing here is established, no node was edited, and nothing is
claimed solved. Every citation below was checked at the level stated (repo node, abstract, or search
summary); no theorem number is used that was not seen.

Notation as in `deligne-hs-metric-ladder-2026-09-13.md`: `Gamma = Sp_4(Z)`, `E_infinity` the integral
Deligne (Maslov) extension, `E_q = E_infinity/qZ`, `z` the central mark, `c_theta = exp(2 pi i theta b)`,
`E_CE` the closed subgroup of the Maslov circle from `maslov-ce-parameter-set-is-a-closed-subgroup`.

## 0. Already dead or already on main (not repeated)

- **Determinant / commutator-cycle phases.** They only see `d mod 3`, which gives floors of order `1/d`
  (`deligne-sector-floor-2026-09-13.md` §3, "Where monomial methods stop").
- **Dimension-free Schatten inputs.** Any such input caps the normalized floor at exponent `1/2` (same
  artifact, §2).
- **Character rigidity.** It already forces sector traces to be central-regular
  (`deligne-maslov-sector-traces-are-central-regular`). So "hyperlinear sector approximations exist" is
  exactly "the twisted factor `L_(c_(1/3))(Gamma)` is Connes-embeddable" (`maslov-ce-subgroup-classifies-finite-deligne-covers`).
- **Hyperfinite HS-stability.** It is equivalent to character rigidity for these lattices
  (`character-rigidity-equals-hyperfinite-hs-stability`, importing Dogon–Vigdorovich Theorem 1.6), but the
  sector algebras are non-hyperfinite, so it does not apply to them.

## Approach 1: move CE along the Maslov circle by equivariant weight shifts

**Idea.**
- `E_infinity` is a lattice in the universal cover `G~` of `Sp_4(R)`. Holomorphic discrete series of `G~`
  come in families with continuous weight, and the central character moves with the weight.
- Restricted to the lattice, each member generates (an amplification of) a twisted group factor
  `L_(c_theta)(Gamma)`, by the formal-dimension argument.
- A `Gamma`-equivariant intertwiner between two weights, e.g. multiplication by a modular form of the
  difference weight, would relate `theta = 1/2` to `theta = 1/3`. Then CE would transfer from the
  metaplectic sector (`E_2` is residually finite, so `1/2 in E_CE`) to the Deligne sector.

**What it would prove.** `1/3 in E_CE`, i.e. every `E_q` hyperlinear. That refutes the Sp4 candidate, a
useful negative result.

**Kill test.** Does an equivariant multiplier of fractional weight `1/3` exist on `Gamma` or a
finite-index subgroup?

**Result.**
- No. Freitag–Hauffe-Waschbüsch (arXiv:2009.06455, abstract checked) record Deligne's theorem: weights of
  Siegel modular forms on congruence subgroups of the genus `g > 1` Siegel modular group are integral or
  half-integral.
- Weight shifts therefore move `theta` only inside `(1/2)Z/Z`, consistent with
  `sp4-finite-index-fd-projective-multiplier-is-finite`.
- Continuity in the weight does not help either. In Rădulescu's `PSL_2(Z)` model the commutants
  `pi_t(Gamma)'` vary with `t` and interpolate different factors (search summary only). Strong continuity
  of a family transports no isomorphism class and no CE.

**Verdict: killed** (Deligne's weight restriction).

## Approach 2: mixed metric, operator-small off a small-rank piece

**Idea.**
- A normalized-HS `epsilon`-defect has at most `(epsilon/eta)^2 d` singular values above `eta`. So every
  HS microstate is an operator-`eta` model after removing normalized rank `(epsilon/eta)^2`.
- In this mixed metric, the failed square-root correction of `deligne-sector-floor-2026-09-13-part2.md` §4
  (HS-small but operator-large central unitaries) becomes a small-rank error.
- One could hope for "operator stability modulo small rank" for `E_infinity`, fed by BDL-type operator
  rounding.

**What it would prove.** The one-word implication `(D3)` of `deligne-maslov-hyperlinear-strategies`, hence
non-hyperlinearity of `E_3`.

**Kill test.** Is any *stability* form of this weaker than known-false statements?

**Result.**
- Mixed-small and HS-small are equivalent (`||X||_2 <= eta + 2 sqrt(rank fraction)`), so mixed stability
  implies local HS-stability.
- Fournier-Facio–Gerasimova–Spaas (arXiv:2307.13155, abstract via search) prove infinite hyperlinear
  property (T) groups are never locally HS-stable.
- `E_infinity` is a lattice in `G~`, which has (T). So mixed stability for it can only hold if it is
  already non-hyperlinear, which is circular. What remains is the one-word form, which is `(D3)` itself.

**Verdict: killed** (equivalent to HS; the stability form is excluded by FGS).

## Approach 3: upgrade hyperlinear sector approximations to strongly convergent ones

**Idea.** If sector microstates of `L_(c_(1/3))(Gamma)` could be chosen strongly convergent, the twisted
reduced C*-algebra would be MF. At genus `g >= 3`, BDL Conjecture 1.8 makes every `E_n`, `n >= 3`, not MF
(`deligne-sp2g-covers-not-mf-from-operator-hs-stability`). That would contradict hyperlinearity.

**What it would prove.** Non-hyperlinearity of `E_3^(g)`, `g >= 3`, conditional on BDL 1.8.

**Kill test.** Does CE, or hyperlinearity, give MF, or strong convergence?

**Result.**
- Not available. Strong convergence is an extra property of the microstates. `mf-implies-hyperlinear` is
  an OPEN root, and `hyperlinear-trace-not-mf-trace` separates the trace notions.
- The MF radical route yields non-MF, which is strictly weaker than non-hyperlinear.

**Verdict: killed** (wrong direction; the upgrade is at least as hard as the Kazhdan-MF problem
`infinite-kazhdan-group-with-mf-reduced-cstar`).

## Approach 4: couple the sector to a Heisenberg–Weil packet (Jacobi group)

**Idea.**
- Let `Gamma` act on `H_5(Z)` by symplectic automorphisms and form `J = H_5(Z) ⋊ E_3`.
- In a hyperlinear approximation with the Heisenberg centre near an irrational phase, approximate
  Stone–von Neumann uniqueness splits the space as Schrödinger factor ⊗ multiplicity space.
- `Gamma` must then act on the Schrödinger factor through an approximate Weil representation. That forces
  the metaplectic multiplier there, and hopefully an incompatible class on the multiplicity space.

**What it would prove.** Non-hyperlinearity of `J`, if the forced classes were incompatible.

**Kill test.** Compute the class forced on the multiplicity space.

**Result.**
- The Weil multiplier is 2-torsion, so the multiplicity space carries `c_(1/3) * mu^(-1)`, i.e. sector
  `-1/6`.
- `E_CE` is a closed subgroup of the circle containing `1/2`. So `1/3 in E_CE` iff `1/6 in E_CE`, and the
  coupling only permutes sectors inside `(1/6)Z/Z`. No incompatibility appears.

**Verdict: killed** (2-torsion shift only; hand computation).

## Approach 5: bounded relator-ideal length gives rung I1

**Idea.** Let `rho` be a sector tuple of `E_3` in dimension `d` whose relator defects `D_r` all have
absolute rank `<= k`. Let `A` be the algebra generated by `rho`, and `J` the two-sided ideal generated by the
`D_r`.
- `A/J` is an exact finite-dimensional representation of the sector twisted group algebra, which Deligne
  plus Malcev forbid unless `A/J = 0`. So `1 = sum_(i<=m) a_i D_(r_i) b_i`, and comparing ranks gives
  `m >= d/k`.
- If the sector algebra `C_zeta[E_3]` had **uniformly bounded ideal length** on finite-dimensional
  representations (1 expressible with `<= M` relator terms in every one), then `d <= kM`.
- That is rung I1 of `deligne-sector-floor-2026-09-13.md`: rank-`<= k` defect tuples live in bounded
  dimension.

**What it would prove.** I1, which nothing on main derives from the established Frobenius floor I0.
Combined with a correction theorem for operator-small parts, it would feed the normalized floor.

**Kill tests run now.**
- (a) Amplification `rho ⊗ 1_m` scales `d` and `k` together, so a bounded *absolute* rank is the right
  hypothesis and the argument is dimension-honest.
- (b) Failure of bounded length gives, in an ultraproduct modulo bounded-rank sequences, an exact nonzero
  representation of the sector algebra. That is an infinite-dimensional object, so no contradiction and no
  easy disproof.
- (c) Natural constructions of bounded-rank tuples fail for independent reasons: compressions of the
  twisted regular representation to finite sets have boundary rank `~ d` because `Gamma` is non-amenable.
  Neither direction is settled.

**Verdict: unclear.** It is a new algebraic sub-question with no analysis in it. Next test: look for
uniform ideal-length bounds in the congruence-subgroup-property proofs of Deligne's finite residual
(Deligne, Funar–Pitsch arXiv:2004.04129). Uniform word-level identities there would give `M`.

## Approach 6: the only rounding Dogon–Vigdorovich actually need, at the regular character

**Idea.**
- Dogon–Vigdorovich Theorem 1.3 (arXiv:2506.20843, statement quoted from their HTML) makes a finite
  central extension non-hyperlinear from three inputs: (T;FD), finite abelianization of the `Z`-extension,
  and **HS-stability** of `Gamma`.
- For `Gamma = Sp_4(Z)` the first two hold, but HS-stability is excluded by Fournier-Facio–Gerasimova–Spaas
  (approach 2). So Theorem 1.3 cannot be applied as printed.
- In their proof, stability is used once. It rounds the microstates of the null sequence of twisted
  factors `L_(e(x/p))(Gamma)`, `p -> infinity`, into genuine representations, which then feed Theorem 4.5.
  That theorem needs only a genuine `rho_n` whose corner `q_n rho_n q_n`, with `liminf ||q_n||_2 > 0`, is
  `epsilon`-close to the projective microstate.
- Those microstates have central-regular sector traces, so on `Gamma` they approximate the **regular
  character**. The input actually needed is a single-character statement:

```text
(RCR)  asymptotic representations of Sp_4(Z) whose traces tend to delta_e are
       HS-close to genuine finite-dimensional representations.
```

- By Margulis superrigidity those genuine representations have finite image. With the congruence subgroup
  property they factor through `Sp_4(Z/N)`. So `(RCR)` is a symplectic, higher-rank analogue of printed
  Dogon–Vigdorovich Question 1.4 (odd congruence quotients of `SL_2(Z)`).

**What it would prove.** `(RCR)` plus the Theorem 4.5 argument gives some non-hyperlinear finite Deligne
cover `E_N` of `Sp_4(Z)`, with no LLP input and no normalized sector floor.

**Kill tests run now.**
- (a) The hypotheses of Theorem 4.5 (quoted) involve no global stability, only the rounded `rho_n` and the
  corner condition. So the reduction to `(RCR)` loses nothing at that step.
- (b) The FGS abstract excludes *local* HS-stability for infinite hyperlinear (T) groups. Whether their
  non-stable witnesses have regular character was **not** checked: the paper text was not read.
  - If they do, `(RCR)` is false for any hyperlinear `Sp_4(Z)`-type base and this approach dies.
  - If the witnesses carry finite-dimensional or mixed characters, `(RCR)` survives as a strictly weaker,
    single-character statement.
- (c) Hyperfinite HS-stability (character rigidity) does not give `(RCR)`, because the microstates
  generate non-hyperfinite algebras.

**Verdict: unclear, best survivor.** Next test: read the FGS construction of non-locally-stable sequences
and decide whether their limit trace is `delta_e`.

## Summary

| # | approach | verdict |
| --- | --- | --- |
| 1 | weight shift along the Maslov circle | killed (Deligne: weights integral or half-integral) |
| 2 | operator-small off small rank | killed (equivalent to HS; FGS) |
| 3 | strong-convergence upgrade to reach BDL | killed (MF does not give CE) |
| 4 | Heisenberg–Weil coupling | killed (2-torsion sector shift) |
| 5 | bounded relator-ideal length gives I1 | unclear |
| 6 | regular-character rounding `(RCR)` feeding Dogon–Vigdorovich Theorem 4.5 | unclear, best survivor |

Sources checked in this lane:
- arXiv:2009.06455 (abstract)
- arXiv:2506.20843 (HTML statements of Theorems 1.3, 1.6, 4.5, Proposition 4.9, Question 1.4)
- arXiv:2307.13155 (abstract, via search)
- Rădulescu's `Gamma`-equivariant Berezin quantization (search summary only)
- repo nodes named above
