# Formalizability at finite levels, and rigidity of Z_3-equivariant automorphisms

Lane `gk-fz-counter` (family F), 2026-09-12. It supports:
- the established claims `finite-group-formalizability-equals-equivariant-automorphism`,
  `formalizable-pairs-restrict-to-finite-quotients`, `automorphisms-of-the-affine-plane-are-an-amalgam`
  (citation), `order-three-equivariant-plane-automorphisms-are-linear` and
  `z3-level-preserving-automorphisms-rotate-uniformly`;
- the open test claim `z3-weight-one-rotation-is-not-an-automorphism-shadow`.

Conventions follow `research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md`, Section 1. A pair
`(tau, sigma)` on `(F_2^n)^G` is *formalizable* if equivariant polynomial representatives on finite
memories satisfy `sigma o tau = id` formally. *Stably formalizable* means the same for `tau x id` on
`(F_2^(n+m))^G` with some left inverse, as in `injective-binary-automata-are-stably-formalizable`.
Left translation is `(k.x)(g) = x(k^-1 g)`.

## 1. Finite levels

**Theorem 1.** Let `G` be finite and `(tau, sigma)` a pair on `(F_2^n)^G` with `sigma o tau = id`.
The pair is formalizable iff `tau` is the Boolean shadow of a `G`-equivariant polynomial automorphism
of affine space `A^(n|G|)` over `F_2`. In that case the inverse automorphism has shadow `sigma`, and
`tau` is bijective.

*Proof.*
- **(⇒)** Memories lie in `G`, so the representatives `T`, `S` are polynomial self-maps of `A^(n|G|)`
  with `S o T = id` formally. Over `F̄_2`, `T` is injective, so by Ax–Grothendieck it is bijective and
  `S = T^-1` on `F̄_2`-points. Then `T o S = id` on `F̄_2`-points. `F̄_2` is infinite, so this identity
  is formal, and `T` is an automorphism. It is equivariant because `T(x)_g` is one rule read at `g`.
- **(⇐)** Let `T` be an equivariant automorphism with shadow `tau`. Equivariance gives
  `T(x)_g = T(g^-1.x)_1`, so `T` is the automaton with memory `G` and rule `P = T(.)_1`. Its inverse
  is equivariant too, giving a rule `Q`. On a finite set `sigma o tau = id` makes `tau` bijective, so
  `sigma = tau^-1`, and the shadow of `T^-1` is `sigma`. The identity `T^-1 o T = id` is formal. ∎

The same statement holds for `tau x id` on `n + m` tracks, so on a finite group stable
formalizability is equivariant automorphism extension of `tau x id`.

**Theorem 2.** Let `G` be any group and `K` a normal subgroup of finite index. Take a formalizable
pair on `(F_2^n)^G`. The automata it induces on `K`-invariant configurations, which are configurations
on `G/K`, form a formalizable pair on `(F_2^n)^(G/K)`. The same holds for stably formalizable pairs.

*Proof.*
- **Invariance.** `tau` commutes with translations, so it preserves the `K`-invariant configurations.
  Those are the functions constant on cosets, identified with `(F_2^n)^(G/K)`.
- **Substitution.** `X_(h,i) -> X_(hK,i)` is a ring homomorphism of polynomial rings. It turns each
  rule `P((X_(gm))_m)` into the rule `P((X_(gmK))_m)` of the induced automaton. Applied to the formal
  identity it gives the formal identity of the induced pair.
- **Stable case.** Apply this to `tau x id`. ∎

**Consequence.** A formalizable pair is visible at every finite quotient `G/K`. There its restriction
is an equivariant polynomial automorphism, by Theorem 1. For a host with no proper finite-index
subgroup, only `K = G` is available: the constant level of
`formalizable-pairs-induce-polynomial-automorphisms-on-constants`.

## 2. Rigidity of equivariant plane automorphisms

**Import (van der Kulk 1953, any field).** `Aut(K[x,y]) = Aff *_B Tri`. Here `Aff` is the affine
group, `Tri` the de Jonquières maps `(x,y) -> (ax + b, cy + p(x))`, and `B = Aff ∩ Tri`. This is
recorded as `automorphisms-of-the-affine-plane-are-an-amalgam`. The amalgam acts without inversion on
its Bass–Serre tree (Serre, *Trees*, Chapter I, Section 4).

**Theorem 3.** Let `K` be a field, and `R` in `GL_2(K)` with `R^2 + R + 1 = 0`, where `x^2 + x + 1`
is irreducible over `K`. Every polynomial automorphism `phi` of `A^2_K` commuting with `R` is
`v -> lambda v`, with `lambda` in `K[R]^×`. Over `K = F_2` the only ones are `1, R, R^2`.

*Proof.*
1. **`R` fixes only the vertex of `Aff`.** `R` lies in `Aff`, so it fixes that vertex `v_A`.
   Fixed-point sets of automorphisms without inversion are subtrees. So if `R` fixed another vertex,
   it would fix a neighbour `g.v_T` with `g` in `Aff`, and then `g^-1 R g` would lie in `B`.
   Elements of `B` are `(x,y) -> (ax + b, cy + dx + e)`, whose linear part has `e_2` as an
   eigenvector. That would give `R` an eigenvector over `K`, a root of `x^2 + x + 1` in `K`. This is
   impossible, so `Fix(R) = {v_A}`.
2. **`phi` is affine.** `phi` commutes with `R`, so it preserves `Fix(R)` and fixes `v_A`. Hence
   `phi` lies in `Aff`, say `phi(v) = A v + c`.
3. **`c = 0` and `A` lies in `K[R]`.** From `phi R = R phi`: `AR = RA` and `Rc = c`.
   - `(R - 1)(R + 2) = R^2 + R - 2 = -3`, which is invertible, since irreducibility of
     `x^2 + x + 1` excludes characteristic 3. So `c = 0`.
   - The minimal polynomial of `R` is irreducible of degree 2, so its centralizer is the field
     `K[R]`, and `A` lies in `K[R]^×`. ∎

## 3. Level-preserving automorphisms over Z_3

`Z_3` acts on `A^3` over `F_2` by cyclic shift. Write `x = s(1,1,1) + v` with `s = x_0 + x_1 + x_2`
and `v_0 + v_1 + v_2 = 0`. This is the isotypic decomposition `A^1 ⊕ V`, since `|Z_3|` is odd. On
`V ≅ F_2^2` the shift acts by `R` with `R^2 + R + 1 = 0`, and `End_(Z_3)(V) = F_2[R] ≅ F_4`.
- **Boolean points.** `000` and `111` have `v = 0`. The weight-one orbit `{100, 010, 001}` has
  `s = 1`, `v ≠ 0`. The weight-two orbit has `s = 0`, `v ≠ 0`.
- **Free Boolean points.** At each level `s`, these are the three nonzero `v` in `V(F_2)`, one orbit.

**Theorem 4.** Let `T` be a `Z_3`-equivariant polynomial automorphism of `A^3` over `F_2` with
`T*(s) = s + b`, `b` in `F_2`. Then `T(s,v) = (s + b, lambda v)` with `lambda` in `{1, R, R^2}`.
Its shadow rotates both free orbits by the same power of the shift.

*Proof.*
1. **Setup.** Write `T(s,v) = (s + b, Phi(s,v))`. Then `T^-1*(s) = s - b`, and
   `T^-1(s,v) = (s - b, Psi(s,v))`. The identities `T o T^-1 = id` and `T^-1 o T = id` give
   `Phi(s - b, Psi(s,v)) = v` and `Psi(s + b, Phi(s,v)) = v`.
2. **An automorphism over `F_2(s)`.** Put `K = F_2(s)`. Then `v -> Phi(s,v)` is a polynomial
   automorphism of `A^2_K` commuting with `R`, with inverse `w -> Psi(s + b, w)`. `F_2` is
   algebraically closed in `K`, so `x^2 + x + 1` stays irreducible.
3. **Apply Theorem 3.** `Phi(s,v) = lambda(s) v` with `lambda(s)` in `F_2[s][R]`, reading off
   `Phi(s, e_1)`. The inverse is polynomial in `s` too, so `lambda(s)` is a unit of
   `F_2[s][R] ≅ F_4[s]`, a constant in `F_4^×`. ∎

**The uniform subgroup.** Let `U_f(s,v) = (s + f(v), v)`, with `f` an `R`-invariant polynomial. It is
a formal involution. The maps `(s + f(v), lambda v)` form a group, since `f` is invariant. On free
Boolean points `f` is constant, so every shadow in this group moves levels uniformly and rotates
uniformly.

## 4. The test permutation

Let `rho` on `{0,1}^(Z_3)` send `e_i -> e_(i+1)` on the weight-one orbit and fix the other five
points.
- It commutes with the shift.
- Its rule is `rho(x)_g = x_(g-1)` when `x` has weight one, and `x_g` otherwise.
- It rotates the level-1 free orbit and fixes the level-0 free orbit.

**Open (`z3-weight-one-rotation-is-not-an-automorphism-shadow`).** No `Z_3`-equivariant polynomial
automorphism of `A^3` over `F_2` has shadow `rho`. By Theorem 1 this is the statement that the
bijective pair `(rho, rho^-1)` is not formalizable.

**Why it is worth deciding.** It would be a second witness for
`binary-left-inverse-pairs-need-not-be-formalizable`, on a finite group. Neither the bi-orderable
leading-term theorem nor the constant-level theorem applies there: `rho` is the identity on constants.

**Where it stops.**
- **Theorem 4:** any realization must move levels. `T*(s) - s` must be a nonconstant `Z_3`-invariant
  polynomial vanishing on all eight Boolean points.
- **Obvious generators:** triangular maps `(s + f(v), lambda v)`, `s`-shears, rotations and
  translations by constants all have uniform shadows. So do all their composites.
- **Families on `V` controlled by `s`:** the automorphisms `v -> lambda(s) v` are constant by
  Theorem 4. Candidates like `v -> v + omega^2 s u^4` (in eigencoordinates) are additive in `u`, so they
  are not injective over `F̄_2` for `s ≠ 0`.
- **Invariant functions** such as `Theta = u o T / u` read the rotation at free Boolean points. They
  give no contradiction, since rational functions take arbitrary values at finitely many points.
- **What is missing:** no structure theorem for equivariant automorphisms of `A^3` in characteristic
  2 is known. That is where a proof or a construction has to come from.

## 5. Stabilization removes the rigidity

The rigidity of Theorems 3 and 4 needs `V` with multiplicity one. With two tracks, `V` has
multiplicity two and `End_(Z_3)(V^2) = M_2(F_2[R])`. Then
`T(s, v_1, v_2) = (s, v_1 + s v_2, v_2)`, with `s` the trivial coordinate of track 1, is an
equivariant automorphism (inverse `v_1 -> v_1 + s v_2`). At level `s = 1` its shadow is not
uniform. So finite-level rigidity is a one-track phenomenon.

This agrees with the stable target `injective-binary-automata-are-stably-formalizable`: Theorem 2
restricts a stable pair to every finite quotient, and stabilization makes those levels flexible.
