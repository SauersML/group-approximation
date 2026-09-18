---
rg: 2
id: random-walk-separators-of-boone-higman
kind: claim
title: No hereditary class defined by an entropy bound, a drift bound or the Liouville property on metabelian-or-larger subgroups separates Boone--Higman; the lamplighter Z/2 wr Z^3 in B_A reaches the linear ceiling, which no amenable group reaches for return probabilities
distinct_from:
  folner-separators-of-boone-higman: that kills Følner-growth separators below towers, using the iterated wreath products of Z and Cavaleri's c.e.-class theorem, and leaves the region above towers open; this kills entropy, drift and Liouville separators at every bound U, using one lamplighter, because these invariants have a linear ceiling that an amenable group in B_A reaches.
  hereditary-approximation-disproofs-of-boone-higman: that kills separators contained in soficity or MF-ness at a nonsofic or full-MF-radical finitely presented simple group; this kills random-walk separators at an amenable metabelian subgroup of some finitely presented simple group.
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that is the exactness separator, whose (S2) holds at one fixed residually finite group; this is a scale of random-walk separators, for which (S1) fails below the linear ceiling and (S2) fails at it.
  thompson-f-random-walks-are-not-liouville: that is Kaimanovich's theorem that finitely supported walks on F are not Liouville; F is not known to be amenable, so F does not lie in the tested family "finitely generated amenable subgroups", and this claim uses Z/2 wr Z^3 instead, with an elementary proof.
  fpbs-random-walk-shannon-and-avez-bounds: that imports the Avez entropy bound and Shannon--McMillan--Breiman for nonamenable walks; this gives linear entropy for one explicit walk on an amenable group, by counting lamps on the range of a transient base walk.
  boone-higman-conjecture: that is the embedding conjecture; this closes the random-walk family of hereditary disproof strategies for it.
---

**ESTABLISHED** by `random-walk-separators-of-boone-higman-proof`. The proof is
unreviewed and elementary. Its inputs are three ESTABLISHED nodes, used only to
put the lamplighter `W = Z/2 wr Z^3` into `B_A`.

## Setup

**Separation.** A class `P` of groups, closed under isomorphism and subgroups,
**separates Boone--Higman** if two things hold (the sense of
`hereditary-approximation-disproofs-of-boone-higman`):
- **(S1)** every finitely presented simple group lies in `P`;
- **(S2)** some finitely generated group with solvable word problem does not.

**Admissible walks.** A measure `μ` on a finitely generated group `H` is
**admissible** if it is a probability measure that is symmetric
(`μ(x) = μ(x^-1)`) and finitely supported, and whose support generates `H`.
The random walk is `X_n = Y_1 ... Y_n`, where the `Y_i` are i.i.d. with law
`μ`. Write:
- `H(μ^n)` for the Shannon entropy of the law of `X_n`;
- `L_μ(n) = E|X_n|` for the drift, with `|.|` the word length for a fixed
  finite generating set. Changing that set changes `L_μ` by a bounded factor.

`μ` is **Liouville** if every bounded `μ`-harmonic function on `H` is
constant. Here `h` is `μ`-harmonic if `h(g) = Σ_x μ(x) h(gx)`.

**Comparison.** `f ≼ U` means `f(n) <= C U(Cn)` for some `C >= 1` and all `n`.
The constant may depend on `H` and `μ`.

**Tested family.** Let `𝓗` be any isomorphism-closed family of finitely
generated groups that contains `W = Z/2 wr Z^3`. Examples: all finitely
generated groups, the amenable ones, the elementary amenable ones, the
solvable ones, and the metabelian ones.

**The classes.** For any function `U : N -> (0, ∞)`:

| class | a group `G` is in it iff, for every subgroup `H ≤ G` with `H ∈ 𝓗` ... |
|---|---|
| `Ent_U` | every admissible `μ` on `H` has `H(μ^n) ≼ U` |
| `Drift_U` | every admissible `μ` on `H` has `L_μ ≼ U` |
| `Liou_∀` | every admissible `μ` on `H` is Liouville |
| `Liou_∃` | some admissible `μ` on `H` is Liouville |

Each class is closed under isomorphism and subgroups, because a subgroup of a
subgroup of `G` is a subgroup of `G`.

## Theorem

1. **Witness.** `W = Z/2 wr Z^3` lies in `B_A`, so it embeds in a finitely
   presented simple group `S_W`.
2. **Linear entropy and drift on the witness.** Let `ν` be uniform on
   `{1, δ}`, where `δ` flips the lamp at the origin. Let `σ` be uniform on the
   six base generators `±e_1, ±e_2, ±e_3`. Then `μ_0 = ν * σ * ν` is admissible
   on `W`. Let `γ > 0` be the escape probability of simple random walk on
   `Z^3`. Then for all `n`:

```text
H(μ_0^n)  >=  (log 2) γ (n+1),        L_(μ_0)(n)  >=  γ (n+1) / 2,
```

   where `L` is taken for the generating set `{δ, ±e_1, ±e_2, ±e_3}`.
3. **No admissible walk on the witness is Liouville.** For every admissible
   `μ` on `W`, a bounded `μ`-harmonic function on `W` is non-constant.
4. **The linear ceiling.** For every finitely generated `H` and every
   admissible `μ` on `H`:

```text
H(μ^n)  <=  n log |supp μ|,        L_μ(n)  <=  n max_(x in supp μ) |x| .
```

5. **Class kill.** For every `U` and every tested family `𝓗` containing `W`,
   none of `Ent_U`, `Drift_U`, `Liou_∀` or `Liou_∃` separates Boone--Higman.
   - **If `n ≼ U`**, then `Ent_U` and `Drift_U` contain every group, by item 4.
     So (S2) fails.
   - **If `n ⋠ U`**, then `S_W` is not in `Ent_U` or `Drift_U`, by items 1
     and 2. So (S1) fails.
   - **The Liouville classes** do not contain `S_W`, by items 1 and 3. So (S1)
     fails for both.

**The invariant and the step where every member dies.** The invariant is the
position of `U` relative to the linear ceiling `n` of item 4.
- Below the ceiling, every member dies at (S1), at the one host `S_W`.
- At or above the ceiling, it dies at (S2), because the class is everything.
- The Liouville property sits at the ceiling itself, and its members die at
  (S1) at the same host. For context only (not used in the proof): by the
  Kaimanovich--Vershik criterion, a finite-entropy walk is non-Liouville iff
  its entropy grows linearly.

## What the kill does not reach: return probabilities

Let `p_(2n)(μ) = μ^(2n)(e)`, and define `Ret_φ` like `Ent_U`, with
`-log p_(2n)(μ) ≼ φ` as the condition. The route proves the following, all
elementary.

6. **Transfer from Følner functions.** Let `H` be amenable with Følner function
   `F_H` (the convention of `folner-separators-of-boone-higman`). Let `μ` be
   admissible on `H`, with support in the `L`-ball. Then for every `r >= 2L`:

```text
-log p_(2n)(μ)  <=  log F_H(r) + 4 L n / r .
```

   So `-log p_(2n)(μ) = o(n)` on every amenable group. A Følner bound
   `F_H(r) <= C U(Cr)` therefore gives the explicit return-probability bound
   `-log p_(2n)(μ) <= log C + min_(r >= 2L) ( log U(Cr) + 4Ln/r )`.
7. **Where the dichotomy breaks.** The ceiling for return probabilities is
   still linear: `-log p_(2n) <= n log(1 / Σ_x μ(x)^2)`. By item 6, no amenable
   group reaches it. So the step "some amenable group in `B_A` reaches the
   ceiling" is false for `Ret_φ`. The kill of item 5 does not extend.
   Return-probability separators on amenable subgroups remain in the same
   situation as Følner separators:
   - they are killed wherever some group in `B_A` beats `φ`;
   - they are open in the band between the rates reached inside `B_A` and `o(n)`.

   Item 7 is a precise statement of where the argument stops. It is not a
   claim about that band. The band is recorded under `## Attempts` of
   `boone-higman-conjecture` (Attempt 14).

## Scope

**Not claimed:**
- The "some admissible `μ`" forms of `Ent_U` and `Drift_U`. They follow from
  item 3 together with two further facts:
  - the Kaimanovich--Vershik entropy criterion, that non-Liouville plus finite
    entropy implies positive asymptotic entropy;
  - the elementary bound `H(μ^n) <= log(nM+1) + (log|S|) E|X_n|`, where `M` is
    the largest length on `supp μ` and `S` is the generating set. It passes
    from linear entropy to linear drift.

  The criterion is not imported into the graph, so these forms are recorded as
  conditional.
- Anything about tested families that exclude `W`, for example nilpotent
  subgroups only.
- Whether `W` embeds in Thompson's group `V`. The related
  `cyclic-p-wreath-z2-does-not-embed-in-thompson-v` is OPEN. The witness uses
  the wreath closure of `B_A`, not `V` itself.
