---
rg: 2
id: full-group-surjunctivity-transfer-must-use-faithfulness
kind: claim
title: A surjunctivity transfer to topological full groups that sees only the acting group is equivalent to Gottschalk, and factor-compatible diagonal hosts carry only virtually free groups
distinct_from:
  kun-thom-full-group-balls-embed-in-permanence-closure: that asks whether one specific alternating full group embeds locally into the permanence closure; this kills the general transfer "surjunctive acting group implies surjunctive full group" and limits one family of faithful hosts.
  amenable-orbit-full-group-subgroups-are-sofic: that is a positive transfer that uses amenability of the orbit relation; this shows a transfer using only surjunctivity or soficity of the acting group proves Gottschalk outright.
  permanence-closure-fg-simple-groups-are-sofic: that bounds what group-theoretic permanence operations can build; this bounds what topological-full-group hosts over sofic acting groups can transfer.
artifacts: []
---

**ESTABLISHED** by `full-group-surjunctivity-transfer-must-use-faithfulness-proof`. This is a class-killing obstruction.

**Transfer principle.** For a class `C` of groups, `T(C)` says: for every `G` in `C` and every minimal action of `G` on
a Cantor space `X`, every subgroup of the topological full group `[[G ↷ X]]` is surjunctive.

**Theorem A (the acting group alone decides nothing).** `T({F_2})` is equivalent to the Gottschalk surjunctivity
conjecture (`gottschalk-surjunctivity-conjecture`). So `T(C)` is equivalent to Gottschalk for every class `C` that
contains `F_2`, such as the sofic groups or the groups in `S*`.

*Exact failing step.* `[[G ↷ X]]` depends only on the image of `G` in `Homeo(X)`. The image of `F_2` under a
non-faithful minimal action can be any 2-generated group `Q` acting freely and minimally, and `Q <= [[F_2 ↷ X]]`.

**Theorem B (faithful diagonal hosts).** Take:
- a surjection `p: F_r -> Q`;
- a free action of `Q` on a compact space `X_Q`;
- a free action of `F_r` on a compact space `Y`.

Let `F_r` act faithfully on `X = X_Q × Y` by `g(x, y) = (p(g)x, gy)`. Suppose `ψ: Q -> [[F_r ↷ X]]` is an injective
homomorphism compatible with the factor map `π: X -> X_Q`, meaning `π(ψ_q(z)) = q π(z)`. Then `Q` quasi-isometrically
embeds in the Cayley tree of `F_r`. So `Q` is virtually free, and hence sofic and surjunctive.

*Exact failing step.* Freeness forces every local cocycle value of `ψ_q` to lie in `p^{-1}(q)`. So the orbit cocycle
is a Lipschitz section of `p`, which is a quasi-isometric embedding of `Q` into a tree.

**What this kills.** A proof that full groups over Kun--Thom-type witnesses carry only surjunctive groups (the route
recorded in `kun-thom-full-group-balls-embed-in-permanence-closure`) cannot use only surjunctivity or soficity of the
acting group and minimality. It must use one of these:
- faithfulness together with a property of the action itself, such as marked-site structure or the profinite factor;
- embeddings that are not compatible with a free factor.

The natural "lift the quotient back through a free extension" host is limited to virtually free groups.

**Calibration.**
- `G = Z`. A non-faithful image is cyclic, and a faithful minimal `Z`-action has an amenable full group
  (Juschenko--Monod), so `T` holds for faithful `Z`-actions.
- Theorem B with `F_r` replaced by `Z`. It gives `Q` quasi-isometric to a line, so `Q` is virtually `Z`.

Both agree with the obstructions.

**Open refinement.** Does some faithful minimal action of `F_2`, or of a sofic group, on a Cantor space have a
non-surjunctive-candidate group, for example a finitely generated simple nonsofic group, inside its topological full
group? A positive answer with an explicit host would move the non-faithful construction of Theorem A into the faithful
regime. Theorem B shows that such a host must not be compatible with a free factor on which the candidate acts. There is a
second constraint from the literature, which is not proved here. Suppose `G` is sofic and acts freely preserving a
probability measure `μ`. Every element of `[[G ↷ X]]` preserves `μ`, so `Q` does too. If `Q` acts essentially freely,
its orbit relation is a subrelation of the sofic relation `R_G`, and it is sofic (Elek--Lippner), so `Q` is sofic.
So a faithful host for a nonsofic candidate must have one of these:
- no invariant measure on which the candidate acts essentially freely;
- a non-free candidate action.
