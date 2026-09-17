---
rg: 2
id: compressible-base-controlled-automata-are-strict-proof
kind: route
title: Transport configurations along the compression map and pad the uncovered clopen with zeros
target: compressible-base-controlled-automata-are-strict
requires: []
---

The notation is that of the target claim. Write `s(z) = s_i` for `z` in `U_i`, so
`T(z) = s(z) z`. `T(X) = ⊔ s_i U_i` is clopen, and `W = X \ T(X)` is nonempty
and clopen.

## Part 1: the strict controlled automaton

**The site map.** For `x` in `X`, define `j_x : G -> G` by
`j_x(g) = g s(g^-1 x)^-1`. It has three properties.

1. **Moving the point.** `j_x(g)^-1 x = s(z) z = T(z)`, where `z = g^-1 x`.
2. **Injective.** Suppose `j_x(g) = j_x(g')`. By (1), `T(g^-1 x) = T(g'^-1 x)`.
   So `g^-1 x = g'^-1 x`, the two `s`-values agree, and `g = g'`.
3. **Image.** `g'` lies in the image iff `g'^-1 x` lies in `T(X)`.
   - If `g'^-1 x = s_i z` with `z` in `U_i`, put `g = g' s_i`.
   - Then `g^-1 x = z`, so `j_x(g) = g' s_i s_i^-1 = g'`.
   - The converse is (1).

The site map is also equivariant: `j_(hx)(hg) = h j_x(g)`.

**The automaton.** Define
- `tau_x(y)(g') = y(g' s_i)` if `g'^-1 x` lies in `s_i U_i`;
- `tau_x(y)(g') = 0` if `g'^-1 x` lies in `W`.

It has four properties.

- **Local.** `tau_x(y)(e)` depends on `y|_S` with `S = {s_1, ..., s_n}`, and on
  which cell of the clopen partition `{s_1 U_1, ..., s_n U_n, W}` contains `x`.
  So `Phi` is continuous.
- **Equivariant.** `tau_x(y)(g')` is `tau_(g'^-1 x)(g'^-1 . y)(e)`, so the
  automaton is defined by translating one local rule. From this,
  `tau_(hx)(h.y)(g') = tau_x(y)(h^-1 g') = (h . tau_x(y))(g')`.
- **Injective.** For every `g`, `j_x(g) = g s_i^-1` with `g^-1 x` in `U_i`, and
  `j_x(g)^-1 x` lies in `s_i U_i`. So `tau_x(y)(j_x(g)) = y(j_x(g) s_i) = y(g)`.
  Hence `y` is recovered from `tau_x(y)`, and `Phi` is injective.
- **Not surjective.** For `x` in `W`, every output has `tau_x(y)(e) = 0`, so `Phi`
  is not surjective. If the action is minimal, the orbit of every `x` meets `W`:
  there is `g'` with `g'^-1 x` in `W`, the coordinate `g'` of every output is `0`,
  and so every fibre map `tau_x` is non-surjective. ∎

## Part 2: compressible examples

**Thompson's V on C.** Put `U_0 = [0]`, `U_1 = [1]` and define two prefix
replacements. Each has image cones partitioning `C`, so each lies in `V`.
- `s_0`: `0w -> 00w`, `10w -> 01w`, `11w -> 1w`.
- `s_1`: `1w -> 01w`, `00w -> 1w`, `01w -> 00w`.

Then `T(z) = 0z` on both pieces, `T` is injective, and `W = [1]`. The action is
minimal.

**F_2 = <a, b> on its boundary.** Let `A = a^-1`. Take `U_1 = ∂F_2 \ [A]` with
`s_1 = a`, and `U_2 = [A]` with `s_2 = b`.
- `a w` is reduced for `w` not starting with `A`, so `s_1 U_1 = [a]`.
- `b A w` is reduced, so `s_2 U_2 = [bA]`.

These images are disjoint, and `W` contains `[B]`, where `B = b^-1`. The boundary
action is minimal.

Since `F_2` is sofic, it is surjunctive (Gromov–Weiss). So controlled strictness
does not imply ordinary strictness.

## Part 3: calibration for amenable groups (sketch)

Let `G` be amenable, `X` minimal, and `Phi` an injective `X`-controlled automaton.

1. **Base measure.** Take an invariant probability `mu` on `X`. By minimality,
   `supp mu = X`.
2. **The target measure.** Let `nu_0 = (uniform Bernoulli) x mu`. The pushforward
   `nu = Phi_* nu_0` is invariant, projects to `mu`, is carried by the closed set
   `Y = Phi(A^G x X)`, and has relative entropy `h_nu(. | X) = log|A|`. This holds
   because `Phi` is a measurable isomorphism commuting with the projection to `X`.
3. **Uniqueness.** `F -> H_nu(y|_F | B_X)` is invariant and strongly subadditive,
   where `B_X` is the invariant sigma-algebra pulled back from `X`. By the
   infimum rule for such functions on amenable groups (Downarowicz–Frej–Romagnoli),
   `log|A| = h_nu(. | X) <= H_nu(y|_F | B_X) / |F| <= log|A|` for every finite `F`.
   So, conditionally on `x`, the pattern `y|_F` is uniform for every `F`, and
   `nu = nu_0`.
4. **Conclusion.** `Y` contains `supp nu_0 = A^G x X`, so `Phi` is surjective.

So the construction of Part 1 cannot exist over an amenable minimal base. The
compressibility of `C`, equivalently the absence of a `V`-invariant probability
on `C`, is exactly what Part 1 uses. The method passes the calibration.

## The class it kills

Suppose an argument for "injective automata over `G` are surjective" uses the
automaton only through data that `X`-controlled automata over some compressible
`G`-space `X` also have. Examples of such data:
- the local rules seen at each site, together with the Cantor germ of that site;
- the restrictions of the automaton to the pieces `V_U ~= V` for clopen `U`;
- counts weighted by Radon–Nikodym cocycles of quasi-invariant measures on `C`.

Then the argument proves surjectivity of the map `Phi` built in Part 1, which is
false.

The failing step is the one where site-independence of the rule, which is the
relation `tau_x = tau_(gx)` for `g` moving `x`, is replaced by dependence on germs.
Stabilizer-commutation `tau_x g = g tau_x` for `g` in `Stab(x)` is not enough:
controlled automata have it.
