---
rg: 2
id: plo-i-group-is-ea-iff-its-orbital-germ-kernels-are
kind: claim
title: "A finitely generated subgroup of PL_o(I) is elementary amenable iff its germ-trivial kernels on its finitely many orbitals are; a non-EA one has an infinite nested descent of non-EA kernels"
---

**Notation.** `PL_o(I)` is the group of orientation-preserving piecewise linear
homeomorphisms of `I = [0,1]` with finitely many breakpoints. For `H ≤ PL_o(I)`, an
orbital of `H` is a component of the set of points moved by some element of `H`. If
`A = (a,b)` is an orbital of `H`, every `h ∈ H` fixes `a` and `b` and is affine on
`[a, a+ε]` and on `[b−ε, b]` for some `ε = ε(h) > 0`. Put

- `χ_a^H(h) = h'(a⁺)` and `χ_b^H(h) = h'(b⁻)` (one-sided slopes);
- `K_A(H) = ker χ_a^H ∩ ker χ_b^H`, the germ-trivial kernel at `A`;
- `X_A` = the restrictions to `[a,b]` of the elements of a set `X` of such maps.

Elementary amenable (EA) groups: the smallest class containing finite and abelian
groups and closed under subgroups, quotients, extensions and directed unions.

**Statement.**

1. `χ_a^H` and `χ_b^H` are homomorphisms `H → (ℝ_{>0}, ·)`, they factor through
   `H_A`, and `H_A / K_A(H)_A` embeds in `ℝ_{>0}²`.
2. Each `h ∈ K_A(H)` is the identity on `[a, a+ε] ∪ [b−ε, b]` for some `ε > 0`: on
   `A` its support is contained in a compact subinterval of `A`.
3. If `H` is finitely generated, `H` has finitely many orbitals `A_1, …, A_m`, and
   restriction `H → ∏_i H_{A_i}` is injective.
4. If `H` is finitely generated, `H` is EA iff every `K_{A_i}(H)_{A_i}` is EA. An
   arbitrary `H` is EA iff all its finitely generated subgroups are.
5. **Descent.** If `H` is finitely generated and not EA, there is an infinite
   sequence `(D_0, A_0), (D_1, A_1), …` with `D_0 = H`, each `D_i` finitely
   generated, `A_i` an orbital of `D_i`, `(D_i)_{A_i}` not EA,
   `D_{i+1} ≤ K_{A_i}(D_i)`, and the closure of `A_{i+1}` contained in `A_i`.

No hypothesis on copies of `F` is used. If `H` contains no copy of `F`, neither
does any `D_i`, and then `f-free-plo-i-groups-have-equal-end-germ-kernels` applies
to every `(D_i, A_i)`.

**Why it matters for Zaremsky Problem 2.3.** A counterexample to the Brin–Sapir
conjecture (`some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f`) can be taken
finitely generated, and by (5) it carries an infinite compactly nested descent of
non-EA germ-trivial kernels. An affirmative proof
(`every-subgroup-of-thompson-f-is-ea-or-contains-f`) amounts to ruling out such a
descent for `F`-free groups.

Proof route: `plo-i-group-is-ea-iff-its-orbital-germ-kernels-are-proof`.
