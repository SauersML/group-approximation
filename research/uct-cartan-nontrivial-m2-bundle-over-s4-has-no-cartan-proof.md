---
rg: 2
id: uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan-proof
kind: route
title: A masa with expectation is a continuous field of fibre masas, hence a line subbundle of the adjoint bundle, which forces the bundle over S^4 to be trivial
target: uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan
requires: []
artifacts:
  - research/artifacts/uct-cartan-obstruction-2026-09-12.md
---

Write `X = S^4`, `π_x : A → E_x ≅ M_2` for evaluation, and `I_x = C_0(X ∖ {x})`.
The centre of `A` is `C(X)`, `ker π_x` is the closure of `I_x A`, and
`‖a‖ = sup_x ‖π_x(a)‖`.

**Item 1.**  `A` is a homogeneous (continuous-trace) algebra over a compact
metrizable space, so it is separable, unital and type I, hence nuclear.  Type I
separable algebras lie in the bootstrap class, so `A` satisfies the UCT.

**Item 2.**  Let `B ⊆ A` be a masa and `P : A → B` a conditional expectation (a
norm-one projection, so a `B`-bimodule map by Tomiyama).

*Step 1: `C(X) ⊆ B` and fibre expectations.*  The centre commutes with `B`, and
`B = B' ∩ A`, so `C(X) ⊆ B` and `1 ∈ B`.  Put `B_x = π_x(B)`, a unital abelian
subalgebra of `M_2`.  Since `P` is `C(X)`-linear, `P(I_x A) ⊆ I_x B ⊆ ker π_x`,
so `P_x(π_x(a)) = π_x(P(a))` defines a conditional expectation `P_x : M_2 → B_x`.

*Step 2: the set `U = {x : dim B_x = 2}` is open and dense.*  If `π_x(b)` is not
scalar, neither is `π_y(b)` for `y` near `x`, so `U` is open.  If the interior `V`
of `X ∖ U` were nonempty, pick an open `W ⊆ V` over which `E` is trivial, a bump
function `f ≥ 0` with support in `W`, and `h = f · diag(1, −1)` in that
trivialization.  For every `x`, either `π_x(h) = 0` or `B_x = C1`, so
`π_x(hb − bh) = 0` for all `b ∈ B`, hence `hb = bh`.  Maximality gives `h ∈ B`,
but `π_x(h)` is not scalar at points of `W` where `f > 0`, while `B_x = C1` there.
So `V = ∅` and `U` is dense.

*Step 3: expectations onto masas of `M_2` are unique.*  If `D = span{p, 1 − p}`
with `p` a rank-one projection and `Q : M_2 → D` is a conditional expectation,
then `Q(p m (1 − p)) = p Q(m)(1 − p) = 0`, and `p m p = tr(pm) p` gives
`Q(p m p) = p m p`; likewise for `1 − p`.  So `Q = E_D`, with
`E_D(m) = p m p + (1 − p) m (1 − p)`.

*Step 4: `U = X`.*  Let `x_0 ∈ X` and suppose `B_{x_0} = C1`, so
`P_{x_0} = φ(·) 1` for a state `φ`.  Trivialize `E` near `x_0`.  Choose
`x_n ∈ U` with `x_n → x_0`, and rank-one projections `p_n` generating
`D_n = B_{x_n}`.  Passing to a subsequence, `p_n → p` and `D_n → D = span{p, 1 − p}`.
For every `a ∈ A`, Step 3 gives `π_{x_n}(P(a)) = E_{D_n}(a(x_n)) → E_D(a(x_0))`,
while continuity of `P(a)` gives `π_{x_n}(P(a)) → φ(a(x_0)) 1`.  Taking `a` with
`a(x_0) = p` yields `p = E_D(p) = φ(p) 1`, which is false.  So `dim B_x = 2` for
every `x`.

*Step 5: the masa field is continuous.*  The same limit argument, applied at an
arbitrary `x_0` with `D_n = B_{x_n}` for any `x_n → x_0`, shows that every limit
point `D` of `(D_n)` satisfies `E_D = E_{B_{x_0}}` on `M_2`, since every matrix is
`a(x_0)` for some section `a`.  So `D = B_{x_0}`, and compactness of the space of
masas gives `B_{x_n} → B_{x_0}`.

*Step 6: a line subbundle of the adjoint bundle.*  Let `V ⊆ E` be the real rank-3
bundle of traceless self-adjoint elements, with inner product `tr(ab)/2`.
`PU(2)` acts on the traceless self-adjoint matrices of `M_2` by the standard
representation of `SO(3)`, and this isomorphism `PU(2) ≅ SO(3)` identifies the
principal bundle of `E` with the oriented frame bundle of `V`.  A masa
`span{p, 1 − p}` corresponds to the line through `2p − 1`, and `1 − p` gives the
same line.  By Step 5, `x ↦ R(2p_x − 1)` is a continuous real line subbundle
`L ⊆ V`.

*Step 7: contradiction.*  Over `S^4`, `L` is trivial since
`H^1(S^4; Z/2) = 0`.  So `L^⊥` is an oriented rank-2 bundle, i.e. a complex line
bundle, trivial since `H^2(S^4; Z) = 0`.  Hence `V ≅ S^4 × R^3` as oriented bundles
(a trivialization over the connected base can be made orientation preserving).
Its oriented frame bundle, which is the principal `PU(2)`-bundle of `E`, is then
trivial, so `E` is trivial.  This contradicts the nonzero clutching class.  So no
such `B` exists.  A Cartan subalgebra is in particular a masa carrying a
conditional expectation, so `A` has none.

**Item 3.**  `A ⊗ K` is a stable, separable continuous-trace algebra with spectrum
`S^4` and Dixmier--Douady class in `H^3(S^4; Z) = 0`.  By the Dixmier--Douady
classification it is isomorphic to `C(S^4) ⊗ K`.  There `C(S^4) ⊗ c_0` is a masa,
`id ⊗ (diagonal expectation)` is a faithful conditional expectation onto it, and
the matrix units `1 ⊗ e_ij` normalize it and generate `C(S^4) ⊗ K` together with
`C(S^4) ⊗ c_0`.  So it is a Cartan subalgebra.

**Existence of `E`.**  Principal `PU(2) ≅ SO(3)`-bundles over `S^4` are classified
by clutching maps `S^3 → SO(3)`, i.e. by `π_3(SO(3)) ≅ Z`, so a nontrivial `E`
exists.
