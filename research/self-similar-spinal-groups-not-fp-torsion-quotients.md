---
rg: 2
id: self-similar-spinal-groups-not-fp-torsion-quotients
kind: claim
title: No self-similar spinal group is a quotient of a finitely presented torsion group
distinct_from:
  fp-torsion-group-is-no-limit-of-non-torsion-groups: that is the abstract fence for direct limits; this proves that a whole class of torsion branch groups lies in its scope, and it rules out the stronger possibility that such a group is merely a quotient of a finitely presented torsion group
  grigorchuk-group-is-just-infinite-torsion-not-fp: that says the first Grigorchuk group is not finitely presented; this says no finitely presented group mapping onto it (or onto any self-similar spinal group) is torsion
  just-infinite-base-hnn-has-only-finite-torsion-quotients: that concerns torsion quotients of ascending HNN extensions; this concerns finitely presented covers of spinal groups
  fp-covers-of-grigorchuk-groups-are-large: that imports Benli-Grigorchuk-de la Harpe, whose stronger conclusion (large covers) already gives the first Grigorchuk group and the groups G_omega; this gives the weaker conclusion (an element of infinite order) for the whole self-similar spinal class, including the Gupta-Sidki and GGS groups, by a self-contained cocycle argument
---

**ESTABLISHED** (proposed; proof in `self-similar-spinal-groups-not-fp-torsion-quotients-proof`).

**Setting.** Let `X` be a finite set with `|X| = d >= 2` and `x_0 in X`. Let
`A <= Sym(X)` be transitive, acting on the tree `X*` by rooted automorphisms
`a(xw) = a(x)w`. Let `B` be a finite group of automorphisms of `X*` that fix
the first level. For each `b in B` the section at `x_0` is `rho(b)` for an
automorphism `rho` of `B`, and for `y != x_0` the section
`omega_y(b) := b|_y` lies in `A`. Assume
(self-replication) that `U_y omega_y(B)` generates `A`. Call
`J = <A u B> <= Aut(X*)` a *self-similar spinal group*.

The first Grigorchuk group is one: `d = 2`, `A = <a>`, `B = {1,b,c,d}`,
`x_0 = 1`, `rho = (b c d)`, `omega_0 = (a,a,1)`, from `b = (a,c)`,
`c = (a,d)`, `d = (1,b)`. So are the Gupta-Sidki `p`-groups, all GGS groups
with a nonzero defining vector (in particular the torsion ones), the
Fabrykowski-Gupta group, and the Sunic groups whose spine map `rho` is invertible.

**Theorem.** Let `F` be the free group on the letters `(A\1) u (B\1)`, and
`N = ker(F -> J)`. Then there are normal subgroups
`M_0 <= M_1 <= M_2 <= ... <= N` with `U_k M_k = N`, `F/M_0 = A * B`, and
every `F/M_k` containing an element of infinite order. Consequently:

1. `J` is a limit, in the space of marked groups, of groups with elements of
   infinite order (all of them quotients of `A * B` mapping onto `J`).
2. Every finitely presented group that maps onto `J` contains an element of
   infinite order. So **no self-similar spinal group, torsion or not, is a
   quotient of a finitely presented torsion group**. In particular no such
   group lies in the interior of the torsion locus of the space of marked
   groups.
3. Unless `|A| = |B| = 2`, every `F/M_k`, and hence every finitely presented
   group that maps onto `J`, contains a non-abelian free subgroup. For the
   Gupta-Sidki and GGS groups (`A * B = C_p * C_p`, `p` odd) this is the
   free-subgroup conclusion that Benli-Grigorchuk-de la Harpe prove for the
   first Grigorchuk group.

**What it kills for Zaremsky Problem 1.11.** Let `P` be a finitely presented
infinite torsion group. Then `P` has a just-infinite quotient `Q`, and every
just-infinite group is near-simple, virtually a power of a hereditarily
just-infinite group, or branch (Grigorchuk-Wilson). A construction whose
torsion certificate is a surjection onto a known torsion branch group of
spinal type cannot exist, however the finitely presented cover is built.
In a counterexample every branch just-infinite quotient lies outside the
self-similar spinal class. This covers the first Grigorchuk group, the
Gupta-Sidki groups, and the torsion GGS groups, which are the standard
branch torsion groups. The special case `P = J` recovers, for this class,
the known fact that torsion spinal groups are not finitely presented.

**Prior work.** For the first Grigorchuk group the conclusion is already
known in a stronger form: every finitely presented cover is large
(`fp-covers-of-grigorchuk-groups-are-large`, Benli-Grigorchuk-de la Harpe).
What this adds is the class: every self-similar spinal group, including the
Gupta-Sidki and torsion GGS groups, which that import does not cover, by one argument
that uses no presentation of `J` and no commensurability.

**Mechanism (why the proof is short).** On all of `F` the section at a vertex
lifts to a cocycle `Phi_x: F -> F`, `Phi_x(uv) = Phi_{v(x)}(u) Phi_x(v)`.
Every `B`-letter contributes at most one letter, and every `A`-letter
contributes none. So on reduced words of `A * B` a section at most halves
the length. The operator `Theta(M) = { w in F_1 : Phi_x(w) in M for all x }`
is monotone and fixes `N`. Starting from `M_0 = ker(F -> A*B)`, it climbs to
`N` by induction on the reduced length. Infinite order lifts along
`Phi_{x_0}`, which is onto modulo `M_0`, from `F/M_k` to `F/M_{k+1}`.

**Calibration.** The theorem would be false if it applied to a finite group,
because a finite group is a finitely presented torsion quotient of itself.
It does not. The section map at `x_0` sends `St_J(1)` onto `J`, since
`b |-> rho(b)` and `c^-1 b c |-> omega_{c(x_0)}(b)`. If `J` were finite, then
`|J| > |St_J(1)| >= |J|`. The infinite dihedral group
`<a, b = (a, b)>` is spinal and non-torsion, which is consistent with the
theorem. Also, `P = A * B` is a finitely presented cover, and it has elements
of infinite order.

**Next.** The same proof works for any self-similar group with a finite
free-product "base" `G_0 = F/M_0` such that (i) `Theta(M_0) >= M_0`, and
(ii) sections of `G_0`-reduced words in `N` are strictly shorter above a fixed
radius, with no nontrivial short element of `N`. It is open whether every
contracting self-replicating torsion group admits such a base. A positive
answer would remove every contracting branch torsion group from case (B) of
the just-infinite trichotomy.
