# Referee report (citation/hypothesis lens): `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the claim and its `-proof`, as landed at 443aa4795.

## Verdict

**PASS, with three wording amendments (W1–W3).** The lemma and its proof are correct. The amendments concern
which instances the conclusion of (b) actually has content for, and one citation.

## Checks

- **Step 1: `PW_X(L)` is a group, with `F_{fg} = F_f F_g` and `F_{f^{-1}} = F_f^{-1}`. Correct.**
  `S_g ∪ g^{-1}(S_f)` is closed and nowhere dense.
- **Step 2, part (a). Correct.** It uses rigidity of germs under topological freeness.
- **Step 3: Mal'cev over a commutative ring, reproved. Correct.** Each piece checked:
  - `Ann(a) ⊆ m`, so `a/1 ≠ 0` in `A_m`.
  - Krull's intersection theorem gives `a ∉ m^j`.
  - `A/m` is finite: the characteristic-0 case is excluded by integrality over `Z[1/D]`, and the
    characteristic-`p` case follows from Zariski's lemma.
  - `A/m^j` is finite.
  - The textbook inputs are Hilbert, Krull and Zariski, and Atiyah–Macdonald 5.7 for "a domain over which a
    field is integral is a field".
- **Steps 4–5. Correct.**
  - Divisible groups lie in the kernel of every map to a finite group.
  - `ρ(g)|_X` agrees with `ρ(g)` on `X`, so `ρ(G) ≤ H`, which is residually finite.
- **Step 6, topological freeness. Correct for all instances.**
  - Basic opens in `A_f^n` are `∏_{p∈S} W_p × ∏_{p∉S} Z_p^n`, and the action is coordinatewise.
  - The kernel of `GL_m(A_f)` on `∏_p P^{m-1}(Q_p)` is `A_f^×`: scalar in every coordinate, and a unit for
    almost all `p`.
  - `Z_d[1/d] = ∏_{p|d} Q_p`.
  - For the wreath, independent coordinates force a trivial permutation part.
  - The fixed set of a non-scalar projective map is a finite union of proper subspaces.
- **Step 7, linearity. Correct.**
  - The conjugation kernel is the invertible scalars.
  - `PGL_{n+1}(Q) → GL_{n+1}(A_f)/A_f^×` is injective: a rational matrix that is an adelic scalar is a
    rational scalar.
- **Step 8, cone maps. Correct.** `αψ ↦ βψ` is `z ↦ b + d^{|β|−|α|}(z − a)` in `d`-adic coordinates.

## Wording amendments

- **W1 (vacuous instances).** In instances 3 (`X = Ẑ`, `L = Aff_1(Q)`) and 5 (`X = Z_d^n`,
  `L = Aff_n(Z_d[1/d])`), the stabilizer of `X` in `L` has no nontrivial divisible subgroup:
  - in instance 3 it is `Z ⋊ {±1}`;
  - in instance 5 it is `Aff_n(Z_d)`, and no nonzero element of `Z_p` is `p`-divisible.
  - So the hypothesis `ρ(g)(X) = X` of (b) never holds for divisible `G` there. Only (a) and the first sentence of
    (b) have content.
  - The node says this for `nV` but not for instance 3, `V_d`, `Sc(n)` or `V_d(G)`. Say it once for both
    instances, so no lane reads them as excluding a linear `GL_n(Q)` there, where none can act anyway.
- **W2 (citation for `T`).** Survey Remark 5.5 says: "the group of all PIP homeomorphisms of a circle is
  **isomorphic** to Thompson's group $T$" (citing Greenberg; CFP §7).
  - It says nothing about rational breakpoints.
  - Step 8 should read "`T` is isomorphic to the group of PIP homeomorphisms of `RP^1` (survey Remark 5.5)".
  - Drop "with finitely many rational breakpoints", or cite Greenberg/Imbert for it. It is not needed for the
    lemma.
- **W3 (PIP groups of spheres).** Thurston's PIP groups of the spheres `S^{6g−7}` do not live on `RP^{n−1}`. They
  act on the sphere of rays of `R^m`, with pieces in `GL_m(R)/R_{>0} ≅ SL^±_m(R)`, which is linear and
  topologically free there. Instance 4 covers them only after this change of `(Y, L)`. Add it as a sub-bullet, or
  restrict the claim to "PIP groups of `RP^{n−1}`".
