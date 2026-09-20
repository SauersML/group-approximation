---
rg: 2
id: property-t-envelope-hosts-restrict-to-manzoor-hosts-proof
kind: route
title: Restrict the host relation along the subrelation R_mu × Delta inside the CDI envelope and project; realize the envelope by the section x rho_b b of the Kazhdan group and read off stabilizers coordinatewise
target: property-t-envelope-hosts-restrict-to-manzoor-hosts
requires:
  - non-ce-property-t-equivalence-relation-exists
  - non-ce-relation-is-not-treeable
  - nonce-relation-hosts-force-root-or-q1-failure
---

**Imported source (verbatim).** Chifan--Drimbe--Ioana, *Embedding universality for II_1 factors with property (T)*,
arXiv 2205.07442. This is the property-(T) relation-embedding theorem invoked by
`non-ce-property-t-equivalence-relation-exists` (Manzoor, arXiv 2502.06697: "Finally by [CDI22, Theorem D] we have
L(R) embedds into some L(R′), where R′ is a ergodic countable p.m.p. relation with property (T).").

* (C1) Theorem D: "Let R be a countable p.m.p. equivalence relation on a probability space (X,µ). Let ∆Y = {(y,y) |
  y ∈ Y} be the trivial equivalence relation on a non-atomic probability space (Y,ν). Then R × ∆Y embeds into a
  countable ergodic p.m.p. equivalence relation S on X×Y such that L(S) ∈ T. In particular, S has property (T),
  Out(S) = {e} and F(S) = {1}."
* (C2) Proof of Theorem D: "Let P be a countable ergodic p.m.p. equivalence relation on (X,µ) which contains R. Let T
  be an ergodic hyperﬁnite p.m.p. equivalence relation on a probability space (Z,ν). Since R × ∆Z ⊂ P × T, it
  suﬃces to prove the conclusion of Theorem D for P × T instead of R. By Lemma 5.2, after replacing R by P × T, we
  may assume that there is a homomorphism π: A → [R] such that {uπ(g)}′′g∈A = L(R), where A = F3."
* (C3) "there is a property (T) group G ∈ W(A,B) with no nontrivial characters, for some icc hyperbolic group B with
  Out(B) = {e}. Using Lemma 2.13, we write G = A(B) ⋊α,v B, where (α,v) is a cocycle action of B on A(B) given by
  αb = Ad(ρb)σb and vb,c = ρbσb(ρc)ρ−1bc, for some map ρ: B → AB, where σ: B → Aut(AB) denotes the shift action."
* (C4) Lemma 2.13: "there is ρ: B → AB such that vb,c := ρbσb(ρc)ρ−1bc ∈ A(B), for every b,c ∈ B, and ρe = e, and
  letting αb := Ad(ρb)σb ∈ Aut(A(B)), for every b ∈ B, we have that G ≅ A(B) ⋊α,v B."
* (C5) Definition 2.6: "the set A × B endowed with the unit e = (e,e) and the multiplication operation
  (x,b) · (y,c) = (xαb(y)vb,c, bc) is a group, denoted A ⋊α,v B".
* (C6) "Deﬁne the equivalence relation R(B) on (XB,µB) by ((xb)b∈B, (yb)b∈B) ∈ R(B) if (xb,yb) ∈ R, for every
  b ∈ B, and the set {b ∈ B | xb ≠ yb} is ﬁnite. Also, deﬁne κ: [R]B → Aut(R(B)) by letting
  κ(ϕ)(x) = (ϕb(xb))b∈B ... We denote by B ↷λ (XB,µB) the Bernoulli shift action ... Deﬁne τ: B → Aut(R(B)) ...
  by letting τb = κ(πB(ρb))λb"
* (C7) "Since λbκ(πB(x))λ−1b = κ(πB(σb(x))), for every b ∈ B and x ∈ AB, it follows that (τ,ω) is a cocycle action
  of B on R(B)."
* (C8) "Since B is inﬁnite, we get that µB({x ∈ XB | (τb(x),x) ∈ R(B)}) = 0, for every b ∈ B \ {e}. Let S be the
  smallest equivalence relation on (XB,µB) which contains R(B) and the graph of τb, for every b ∈ B."
* (C9) "Since S contains R(B), it also contains R × ∆XB\{e}, where we identify Xe with X."

In (C6)--(C9) the letter `R` denotes `P × T` on `X × Z`, after the replacement in (C2). Below it is written
`R_1 = P × T`, and `X_1 = X × Z`, `m = mu × nu`.

**Graph inputs.**
* `non-ce-property-t-equivalence-relation-exists`: `R_T` is the envelope `S` of (C1)--(C9), applied to `R = R_mu`.
  `L(R_mu)` is not Connes embeddable. That node's text records the chain: the IRS algebra embeds in `L(R_mu)`, and
  Connes embeddability passes to von Neumann subalgebras.
* `non-ce-relation-is-not-treeable` item 1: a pmp relation whose von Neumann algebra is not Connes embeddable is not
  treeable.
* `nonce-relation-hosts-force-root-or-q1-failure`: the definition of free host (only the definition is used).

**Step 1 (restriction to a subrelation).** Let `(Lambda ↷ (W, zeta), A_W, S', r)` be a free host of a pmp relation
`R` on `(X, mu)`, and let `R_0 ⊆ R` be a Borel subrelation. Put

```text
S'_0 = { (a, a') ∈ S' : (r(a), r(a')) ∈ R_0 }.
```

* `S'_0` is a Borel equivalence relation, since `R_0` is one and `r` is Borel. It is contained in `S'`, hence in
  `R_Lambda(W)|A_W`.
* `[a]_(S'_0) = [a]_(S') ∩ r^(-1)([r(a)]_(R_0))`. On a conull `S'`-invariant set, `r` maps `[a]_(S')` bijectively
  onto `[r(a)]_R ⊇ [r(a)]_(R_0)`. So it maps `[a]_(S'_0)` bijectively onto `[r(a)]_(R_0)`.
* The action, `A_W`, `zeta` and the push-forward `r_* zeta_(A_W) = mu` are unchanged.

So `(Lambda ↷ W, A_W, S'_0, r)` is a free host of `R_0`, finite if and only if the original is.

**Step 2 (projection off a trivial factor).** Let `R = R_1 × Delta_Y` on `(X_1 × Y, mu_1 × nu_Y)`, and let
`p : X_1 × Y -> X_1` be the projection. Then `p_*(mu_1 × nu_Y) = mu_1`, and `p` maps `[(x, y)]_R = [x]_(R_1) × {y}`
bijectively onto `[x]_(R_1)`. So if `r` is class-bijective onto `R`-classes, `p ∘ r` is class-bijective onto
`R_1`-classes and pushes `zeta_(A_W)` to `mu_1`. A free host of `R` becomes a free host of `R_1` with the same action.

**Step 3 (item 2 of the claim).** By (C2), `R_mu × Delta_Z ⊆ P × T = R_1`. By (C9), `S ⊇ R_1 × Delta_(X_1^(B \ {e}))`.
Hence

```text
S ⊇ R_mu × Delta_Z × Delta_(X_1^(B \ {e})) = R_mu × Delta_Y,    Y = Z × X_1^(B \ {e}),
```

with the `X`-factor as the first coordinate of `xi_e`. Given a free host of `S = R_T`, apply Step 1 with
`R_0 = R_mu × Delta_Y`, then Step 2. The result is a free host of `R_mu` with the same action, and so with the same
finiteness. So "some free host of `R_T`" implies "some free host of `R_mu`". The disjunction in
`nonce-relation-admits-free-host` is therefore equivalent to its `R_mu` disjunct, and an actor for `R_T` is an actor
for `R_mu`.

This step uses only (C1), (C2) and (C9). It holds for every property-(T) relation that contains `R_mu × Delta_Y` for
some standard probability space `Y`, so for every envelope Theorem D produces from `R_mu`.

**Step 4 (item 3: the section `x rho_b b`).** Work in the ordinary semidirect product `A^B ⋊_sigma B`, whose
product is `(x b)(y c) = x sigma_b(y) bc`. Define `j(x, b) = x rho_b b` for `(x, b) ∈ A^(B) × B`. For
`(x, b), (y, c)` in `G = A^(B) ⋊_(alpha,v) B`:

```text
j(x,b) j(y,c) = x rho_b sigma_b(y) sigma_b(rho_c) bc
              = x [rho_b sigma_b(y) rho_b^(-1)] [rho_b sigma_b(rho_c) rho_(bc)^(-1)] rho_(bc) bc
              = x alpha_b(y) v_(b,c) rho_(bc) bc
              = j(x alpha_b(y) v_(b,c), bc)
              = j((x,b) · (y,c)).
```

The last two lines use (C4) (`alpha_b(y), v_(b,c) ∈ A^(B)`) and (C5). `j` is injective, since `j(x,b)` determines `b`
and then `x`. So `G ≅ j(G) ≤ A^B ⋊_sigma B`.

`kappa ∘ pi^B : A^B -> Aut(X_1^B, m^B)` acts coordinatewise and is a homomorphism. `lambda` is a homomorphism. By (C7),
`lambda_b kappa(pi^B(x)) lambda_b^(-1) = kappa(pi^B(sigma_b(x)))`. So `Phi(x b) = kappa(pi^B(x)) lambda_b` is a
homomorphism of `A^B ⋊_sigma B`. By Mackey's point-realization for the countable group `j(G)`, `Phi ∘ j` is a pmp
Borel action of `G` on `(X_1^B, m^B)`.

*Orbit relation.* `(x, b) = (x v_(e,b)^(-1), e) · (e, b)` by (C5), with `alpha_e = id` and `rho_e = e` from (C4). So
`G` is generated by `A^(B) × {e}` and the elements `(e, b)`. Now:
* `Phi(j(e, b)) = kappa(pi^B(rho_b)) lambda_b = tau_b`, by (C6).
* `Phi(j(x, e)) = kappa(pi^B(x))` for `x ∈ A^(B)`.

The orbit relation of `pi(A)` on `X_1` is all of `R_1`. Proof: if `R_pi ⊊ R_1` on a set of positive measure, then
`L(R_pi)` is a proper von Neumann subalgebra of `L(R_1)` containing every `u_pi(g)`. This contradicts
`{u_pi(g)}'' = L(R_1)` in (C2). (By Feldman--Moore, `u_phi` for `phi ∈ [R_1]` whose graph misses `R_pi` on a positive
set is not in `L(R_pi)`.)

Hence the orbit relation of `kappa(pi^B(A^(B)))` is `R_1^(B)` of (C6). Two points in the same `R_1^(B)`-class differ
in finitely many coordinates `c`, and each pair `(xi_c, eta_c)` is joined by some `pi(x_c)`.

So the orbit relation of `Phi ∘ j` is the smallest equivalence relation containing `R_1^(B)` and the graphs of the
`tau_b`. By (C8) that is `S`. `G` has property (T) by (C3).

**Step 5 (item 4: stabilizers).**
* *No element outside `A^(B)` fixes a typical point.* Let `b ≠ e`. Then `Phi(j(x, b)) = kappa(pi^B(x)) tau_b`, and
  `kappa(pi^B(x)) ∈ [R_1^(B)]` for `x ∈ A^(B)`. So if `Phi(j(x,b)) xi = xi`, then `(tau_b(xi), xi) ∈ R_1^(B)`. By (C8)
  this happens only on a null set. `B` is countable, so off a null set, `Stab_G(xi) ⊆ A^(B) × {e}`.
* *Inside `A^(B)`.* `x ∈ A^(B)` fixes `xi` iff `pi(x_c) xi_c = xi_c` for every `c`. So
  `Stab_G(xi) = ⊕_(c ∈ B) Stab_pi(xi_c)`.
* *The coordinate stabilizers are nontrivial with positive probability.* Let `E = {w ∈ X_1 : Stab_pi(w) ≠ 1}`.
  - Suppose `m(E) = 0`. Then `A = F_3` acts essentially freely through `pi`, and its orbit relation `R_1` (Step 4) is
    treeable: the Cayley graph of `F_3` transported to the orbits is a treeing.
  - But `L(R_1) ⊇ L(R_mu × Delta_Z) ⊇ L(R_mu) ⊗ 1`, because `R_mu × Delta_Z ⊆ R_1` by (C2). `L(R_mu)` is not
    Connes embeddable, and Connes embeddability passes to subalgebras, so `L(R_1)` is not Connes embeddable.
    By `non-ce-relation-is-not-treeable` item 1, `R_1` is not treeable. This is a contradiction.

  So `p := m(E) > 0`.
* *Infinitely many coordinates.* Under `m^B` the coordinates `xi_c` are i.i.d. with law `m`, and `B` is infinite (it
  is icc, by (C3)). The events `{xi_c ∈ E}` are independent with probability `p > 0`. By the second Borel--Cantelli
  lemma, a.s. infinitely many occur.
* *Conclusion.* Each nontrivial subgroup of `F_3` is torsion-free, so it contains a copy of `Z`. Hence a.s.
  `Stab_G(xi)` contains `Z^(N)`. A direct sum of infinitely many nontrivial groups is not finitely generated.

The action is thus neither essentially free nor finite-stabilizer on any positive-measure set, since stabilizers are
a.s. infinite. The finite-stabilizer corner (item 3 of `nonce-relation-hosts-force-root-or-q1-failure`) needs finite
stabilizers, and it does not apply to `G`. This matches `manzoor-isotropy-has-no-positive-finite-type-corner` for the
native free-group generator of `R_mu`.

**Remark (why the converse transfer fails; not part of the claim).** To turn a free host of `R_mu` with actor
`Lambda_0` into one of `S`, the natural step is:
1. host `R_1^(B)` coordinatewise in `Lambda_0^(B) ↷ W^B`, which needs a finite host;
2. lift each `tau_b`.

Step 2 is where it breaks. The coordinate part `pi^B(rho_b)` has infinite support for some `b`, and by
`cdi-wreath-tail-cocycle-is-intrinsically-nonsplit` no choice of section removes all the tails. If every `rho_b` could
be finitely supported, then `G` would be the restricted wreath product `A wr B`, and CDI records that "wreath
products never have property (T)". So the canonical lifts of the `tau_b` lie in the full group of the unrestricted
product relation, and they are realized piecewise by elements of `Lambda_0^B ⋊ B`, an uncountable group. Nothing forces
the countable group they generate, together with `Lambda_0^(B)`, to act essentially freely. The w19 exclusion for
`R_T` therefore has no known counterpart for `R_mu`.

**Status.** Items 1--4 are complete, given (C1)--(C9) and the three graph inputs.
