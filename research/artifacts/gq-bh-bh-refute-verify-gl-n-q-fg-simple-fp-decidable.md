# Adversarial check: `gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups` (bh-refute, 2026-09-18)

This item was assigned by the coordinator. Verdict: **PASS**. It is a pure assembly of cited theorems. Each step
was checked against the quotations from BBMZ arXiv:2306.16356v3 on the node.

## The four items

1. **Two-generated host.** `GL_n(Q)` has an enumerated generating set with a solvable word problem (Prop. 3.3
   proof), so the HNN construction gives a two-generated `G*` with solvable word problem. For countable,
   non-finitely-generated inputs this is the correct form: HNN applies to countable groups with a solvable word
   problem for an enumerated generating set.
2. **Finitely presented host.** Clapham applied to `G*`. Clapham's statement is pinned in
   `gq-bh-bh-refute-verify-mo412219.md` §1, via BBMZ l.145 and FFWZ. It also appears verbatim as Prop. 3.3(2).
3. **Simple host.** `G*V_{G*}` is finitely generated and simple with a solvable word problem (Belk–Zaremsky,
   Thm 4.13 and the sentence after it). Thompson's envelope would also serve.
4. **Finitely presented group with a simple subgroup.** Solvable WP implies computably presented, which implies
   embeddability in a finitely presented `P` by Higman. This gives `GL_n(Q) ≤ S ≤ P`.

## Point checked for overclaim

The node correctly says that only the conjunction "finitely presented and simple" is open. It also quotes BBMZ
on why translation actions (`GV_G`) never satisfy the type (A) criterion. Nothing is claimed beyond the
assembly.

## Lesson for general BH

For every input the two adjectives come separately and for free: simple via Thompson or Belk–Zaremsky, finitely
presented via Clapham. The whole content of BH is their conjunction in one group, which is this lane's first
landing (`bh-separators-must-omit-nested-decidable-hosts` §1) seen from the host side. The standard simple
envelopes use the translation action, which never has finitely many orbits on pairs. So any proof must replace
the translation action of the input by an action with finitely many orbits on pairs (type (A)) or a
finiteness-certified analogue. The regular action is exactly the wrong one.
