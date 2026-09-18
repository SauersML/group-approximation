# bh-free-53: search for a finitely presented shell germ algebra with a non-finitely-presented germ group

Lane log, 2026-09-18. Seed: `shell-germ-algebra-fp-forces-fp-germ-group`. Nothing here is claimed
beyond what the nodes below state. No priority claimed.

## Landed

- `shell-germ-steinberg-algebras-are-never-simple`: for every shell envelope and every field,
  `(1 - u_g) s_0 (1 - u_g) t_0` is a nonzero singular element. The algebra is not simple and the
  germ groupoid is not Hausdorff.
- Attempt 2 on `shell-germ-algebra-fp-forces-fp-germ-group`: the claim splits into an `A` version
  and an `A/J` version, where `J` is the singular ideal, and the input-letter truncation of
  Attempt 1 covers only the `A` version.
- Correction under step 3 of `boone-higman-via-germ-steinberg-algebra-presentation`.

## Directions tried (heuristic, not claimed)

1. **Zigzag enumerations.** Before the parity convention of
   `shell-cantor-embeddings-are-finite-germ-extensions` was checked, the same four-term cancellation
   was found for `P = Z` with the regular action spread over all of `N` along the zigzag
   `0, 1, -1, 2, -2, ...`. There `hat(1)` agrees with the shift by `2` on odd shells and with its
   inverse on even shells. The germ group then acts by translations on the two parity classes, so it is virtually abelian and finitely presented, and
   the example is only a warm-up.
2. **Characteristic-2 linear relations.** In a permutation module, a relation `1 + b + c + d = 0`
   among involutions forces `bc = cb`. So linear relators can replace group relators. The model
   case is Bartholdi's tree-enveloping algebra of the Grigorchuk group (arXiv math/0410226, e-print
   read on MSI), where `B + C + D = 0` holds. His presentation (theorem `thm:=2:pres`) still has two
   infinite families `σ^n(CACACAC)` and `σ^n(DACACAD)`, with `σ : A |-> ACA, B |-> D, C |-> B, D |-> C`.
   These mirror the Lysenok families `σ^n((ad)^4)` and `σ^n((adacac)^4)`. So no finitely presented
   instance comes from there.
3. **Lamps from unipotent algebra elements.** The algebra
   `F_2<x^(±1), y | y^2, yx + y>` is finitely presented and its units contain `C_2 ≀ Z`. It was not
   realized by germs: at the germ level the relation `yx = y` needs `x` to fix the support of `y`,
   and inside a near-permutation germ group that did not produce infinitely many independent lamps.
4. **What a counterexample must look like.** By
   `shell-germ-algebra-fp-forces-bounded-germ-presentation`, the germ group must be boundedly but not
   finitely presented, of Bieri--Strebel type. The germ groups contain `P × P`, acting on even and
   odd shells. So lamp-type subgroups are available, but no enumeration was found that makes the
   algebra finitely presented.

## Open questions left by the lane

- Is `A/J` simple for every shell envelope? Does minimality plus effectiveness suffice for the
  essential quotient of a non-Hausdorff ample groupoid? The source for that was not read.
- Is `J` finitely generated as a two-sided ideal, for instance by the elements `f_g`, `g` in a
  generating set of `P`?
- Does finite presentation of `A/J` force a finitely presented germ group? Attempt 1's fibre model
  does not apply, because `f_g` is nonzero there.
