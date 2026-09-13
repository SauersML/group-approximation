---
rg: 2
id: compiler-rope-is-coset-wreath-of-an-a-t-menable-base
kind: claim
title: The compiler's positive branch is soficity of a coset wreath over an a-T-menable base, where no known nonsoficity mechanism applies
distinct_from:
  sofic-safe-finite-presentation-compiler: that is the whole compiler; this reframes only its positive-branch inner rope as a free generalized wreath over a coset action and records that the base is a-T-menable, so the known nonsoficity mechanisms are excluded.
  centralizing-hnn-perturbed-edge-separation: that is the probabilistic Britton separation lemma for one non-quotient model; this is the structural reframing plus the observation that the coset action itself is obstruction-free.
  arithmetic-coset-wreath-is-not-sofic: that conjectures a coset wreath IS nonsofic, for the arithmetic pair whose actor SL_3(Z[1/3]) has property (T); this is about the compiler base, a product of free groups, which is a-T-menable, so that route's (T)-driven mechanism cannot apply.
---

OPEN (strategic reframing of the positive branch of
[[sofic-safe-finite-presentation-compiler]]).

By [[centralizer-hnn-is-free-generalized-wreath]] the compiler's inner rope

```text
Gamma_e = < K_e, v | [v, l] = 1  (l in L_e) >
        ~= Z wr^*_(K_e curvearrowright X) K_e,     X = K_e / L_e,
```

is the **free** generalized (coset) wreath product of `Z`-lamps over the coset
action `K_e curvearrowright K_e/L_e`, with the stable letter `v` the root lamp
`z_(L_e)` and `k v k^(-1) = z_(k L_e)`.  So the positive branch is: **is this
free coset wreath sofic on INF?**

## The base is a-T-menable, so the known nonsoficity mechanisms are excluded

`K_e` is a finite direct product of free groups
([[sofic-safe-finite-presentation-compiler]]).  Direct products of free groups
have the Haagerup property (they act properly on a product of trees, a CAT(0)
cube complex), i.e. `K_e` is a-T-menable.  Every subgroup of an a-T-menable
group that has property (T) is finite
([[a-t-menable-groups-have-no-rigid-compression-defect]]).  Consequently:

- The Kun--Thom compression mechanism ([[kun-thom-nonsofic-wreath]],
  [[coordinate-action-not-sofic]]) that makes a coset action / coset wreath
  nonsofic **cannot be instantiated inside `K_e`**: it needs an infinite
  infranormal non-normal subgroup with property (T) in the actor, and `K_e` has
  no infinite (T) subgroup at all.
- The conjectural arithmetic route ([[arithmetic-coset-wreath-is-not-sofic]])
  is for the actor `SL_3(Z[1/3])`, which has property (T); it too is a
  (T)-driven mechanism with no a-T-menable analogue.

So there is **no known obstruction** to `K_e curvearrowright K_e/L_e` being a
sofic action, and hence none to the rope being sofic.  A nonsofic rope would be
nonsoficity of a coset wreath over an a-T-menable base — a genuinely new
phenomenon (nonsoficity without property (T) driving it), which would itself be
a major result.  The non-separability of `L_e`
([[centralizing-hnn-sofic-via-regular-edge-centralizer]]) defeats finite-
quotient models but supplies no nonsoficity: separability is a
residual-finiteness obstruction, not an approximation one.

## Attempts

- **Reduce to a set-action soficity input.**  If the coset action
  `K_e curvearrowright X` is a sofic action on a set (Gao--Kunnawalkam
  Elayavalli--Patchell, *Soficity for group actions on sets*, Def. 2.1), then
  the abelian-lamp companion `Z wr_X K_e = (bigoplus_X Z) x| K_e` is sofic by
  GKP Theorem A (with `K_e` sofic).  The rope is the **free**-lamp wreath
  `(*_X Z) x| K_e`, and it is sofic under the same hypothesis by GKP Theorem
  3.7 ([[gkp-free-generalized-wreath-soficity]]).  *Corrected 2026-09-13 (lane
  `ex2-free-wreath-amenable-sofic`):* an earlier version said the gap between
  free and abelian lamps "is exactly the correlated Britton estimate", and
  that "a free-wreath analogue of GKP Theorem A ... closes the branch". That
  analogue is Theorem 3.7, already published. So the first rope needs exactly
  a sofic coset action. By [[compiler-rope-edge-is-not-co-amenable]] (R3),
  that action reduces to the two-sided action of the Higman host, pulled back
  to `F(X_e)^2`. The action is free of (T)-obstructions by the paragraph above,
  but it is not amenable ((R2) there), so no amenability tool applies.
- **Why the (T)-free setting matters.**  It separates the two roles of the edge
  `L_e`: its non-separability (a residual-finiteness failure, the reason the
  compiler exists) versus a nonsoficity mechanism (which needs (T), absent
  here).  The natural conjecture this makes is that every coset action of an
  a-T-menable residually finite group is sofic; that would make every centralizing
  HNN over a subgroup of a product of free groups sofic, closing the branch.
- **Where it is still hard.**  Proving soficity of `K_e curvearrowright K_e/L_e`
  in the absence of an obstruction still requires an actual construction of
  finite orbit-approximations that keep `L_e` acting freely while separating
  the closure points `cl(L_e) \ L_e`; this is the same content as the deferred
  live lane in [[centralizing-hnn-perturbed-edge-separation]], now stated for
  the set-action rather than the rope.
