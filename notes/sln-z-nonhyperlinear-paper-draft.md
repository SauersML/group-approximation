# An explicit non-hyperlinear group from flexible Hilbert–Schmidt stability of SL_3(Z)

**Draft, 2026-08-21.** A self-contained conditional theorem: if the plain
higher-rank lattice `SL_3(Z)` is flexibly Hilbert–Schmidt stable, then a
displayed finitely presented non-hyperlinear group exists. Every
hypothesis except that stability is a published theorem. This is the exact
Hilbert–Schmidt analogue of Bowen–Burton's permutation result and, unlike the
prior conditional routes of Dogon and Dogon–Vigdorovich, reaches the plain
lattice rather than a central extension or an S-arithmetic group.

## 1. Statement

Throughout, `||x||_2 = (tr(x*x)/d)^{1/2}` is the normalized Hilbert–Schmidt
norm on `M_d(C)`, `U(d)` the unitary group. For a finite presentation
`G = <S | R>` and a tuple `U in U(d)^S`, write `Def_R(U) = max_{r in R}
||r(U) - I||_2`. `G` is **hyperlinear** if for every finite `F subset G` and
`eps > 0` there is a tuple with defect `< eps` on `F`'s relations and marked
elements separated by `~ sqrt 2`; equivalently the canonical trace of `G`
embeds in a tracial matrix ultraproduct. `G` is **flexibly HS-stable** if
every asymptotic representation `phi_n : G -> U(d_n)` (`Def -> 0`) is, after
padding by a corner of vanishing density, uniformly `||.||_2`-close to a
genuine finite-dimensional representation.

> **Theorem.** Let `a,b in SL_3(Z)` be the two displayed matrices in Section
> 4 and set
>
>     G_exp = < SL_3(Z), t | [t,a]=1, [t,b]=1 >.
>
> If `SL_3(Z)` is flexibly HS-stable, then `G_exp` is a finitely presented
> non-hyperlinear group.  An explicit nonidentity marked word is `[t,r]`,
> where the order-three matrix `r` is displayed in Section 4.

## 2. The HNN reduction

The construction is an instance of the following, which isolates the two
properties of the pair `(A, C)` that matter.

**Definition.** `C <= A` (both f.g.) is **co-dense** if `rho(C)' = rho(A)'`
for every finite-dimensional unitary representation `rho` of `A`, and has a
**uniform conjugation gap** if there is `kappa > 0` such that for every such
`rho` on `C^d` and every `X in M_d` with
`max_{c in S_C} ||rho(c) X rho(c)^* - X||_2 <= eps` one has
`||X - E X||_2 <= eps/kappa`, `E` the trace-preserving projection onto
`rho(C)'`. (Property (tau) of `C` on the family of quotients through which
the representations of `A` factor supplies the gap.)

**Proposition (HNN theorem).** Let `C <= A` be co-dense with a uniform
conjugation gap `kappa`, `a_1 in A \ C`, and `A` flexibly HS-stable. Then
`G = <A, t | [t, C] = 1>` is not hyperlinear.

*Proof.* Suppose `G` is hyperlinear; fix a trace-preserving embedding
`L(G) -> M = prod_omega M_{d_n}` and write `pi = U|_A`, `k = U(t)`. Britton's
lemma gives `w := [t, a_1] != 1` in `G`, so `tau_G(w) = 0` (regular trace of a
nontrivial element), hence `||U(w) - I||_2 = sqrt 2 > 0` in `M`.

Realize `M` as an ultraproduct of finite stages. At stage `n`, `U|_A` is an
asymptotic representation of `A` of defect `t_n -> 0`. Flexible stability
supplies exact representations `rho_n` on `q_n M_{d_n} q_n` (`||q_n||_2 -> 1`)
with `||pi_n(a) - q_n rho_n(a) q_n||_2 -> 0` for `a in S_A cup S_C`. Put
`k_n = q_n U(t)_n q_n`.

For `c in S_C`, the relator `[t, c] = 1` gives
`||k_n pi_n(c) - pi_n(c) k_n||_2 -> 0`, hence
`||rho_n(c) k_n rho_n(c)^* - k_n||_2 <= t_n + o(1)`. By the uniform
conjugation gap of `C`, `||k_n - E_n k_n||_2 <= (t_n + o(1))/kappa`, where
`E_n` projects onto `rho_n(C)'`. By co-density, `rho_n(C)' = rho_n(A)'`, so
`E_n k_n` commutes with `rho_n(a_1)`. Therefore

    ||[k_n, U(a_1)_n]||_2 <= 2||k_n - E_n k_n||_2 + 2||[E_n k_n, rho_n(a_1)]||_2
                             + O(|a_1| eta_n) = O((t_n)/kappa + eta_n) -> 0,

with `eta_n` the vertex approximation error. Thus `||U(w) - I||_2 =
lim ||[k_n, U(a_1)_n]||_2 = 0`, contradicting `||U(w) - I||_2 = sqrt 2`. Hence
`G` is not hyperlinear. `QED`

The proof consumes flexible stability once (to replace `pi_n` by `rho_n`);
the co-density and the gap are used only through the two displayed
inequalities. Finite presentability of `G` is standard (HNN of a finitely
presented group over a finitely generated associated subgroup, with the
finitely many commutation relations `[t, s] = 1`, `s in S_C`).

## 3. The representation theory of the vertex

**Lemma 1.** For `n >= 3`, every finite-dimensional unitary representation of
`SL_n(Z)` factors through a congruence quotient `SL_n(Z/m)`.

*Proof.* A unitary representation `rho : SL_n(Z) -> U(d)` has image in the
compact group `U(d)`. By Margulis superrigidity (equivalently, the vanishing
of the relevant cohomology / the normal subgroup theorem for higher-rank
lattices), a homomorphism of `SL_n(Z)` to a compact Lie group has finite
image. So `ker rho` has finite index, and by the Bass–Milnor–Serre congruence
subgroup property every finite-index subgroup contains a congruence subgroup;
hence `rho` factors through some `SL_n(Z/m)`. (See Bekka, *Operator-algebraic
superrigidity for `SL_n(Z)`, `n >= 3`*, Invent. Math. 169 (2007).) `QED`

## 4. The explicit thin co-dense subgroup and its gap

Put `C=<a,b> <= SL_3(Z)`, where

    a = [ -176379047    1936571625   -17817867 ]
        [ -1941616205  21318171799  -196142682 ]
        [         10          -121           1 ]

    b = [ -40193888    -3684209   -44180039 ]
        [ 396162230    36312596   435450841 ]
        [   3829559      351021     4209349 ].

**Lemma 2.** `C` is a free group of rank two, has infinite index in
`SL_3(Z)`, surjects onto `SL_3(Z/m)` for every `m>1`, and has property (tau)
with respect to this congruence family.

*Proof.* Detinko--Flannery--Hulpke, *Experimenting with Zariski dense
subgroups* (arXiv:2303.06236, Section 3.3), construct `a,b` inside Humphries's
free subgroup `G_4 < SL_3(Z)`.  They verify surjectivity modulo `4` and every
prime and apply their profinite-generation criterion to conclude surjectivity
for every modulus.  As a subgroup of `G_4`, `C` is free; its noncyclic finite
images show that its rank is two.  It has infinite index because a
finite-index subgroup of the Kazhdan group `SL_3(Z)` has property (T), while
a nonabelian free group does not.  Profinite density implies Zariski density,
and Bourgain--Varju, *Expansion in `SL_d(Z/qZ)`, `q` arbitrary*, Invent.
Math. 188 (2012), 151--173, gives the asserted uniform gap. `QED`

For the outsider take

    r = [ 0 -1 0 ]
        [ 1 -1 0 ]
        [ 0  0 1 ].

Then `r^3=1` and `r!=1`.  Since `C` is free and hence torsion-free,
`r notin C`.

**Corollary.** Lemmas 1 and 2 give `rho(C)=rho(SL_3(Z))` for every
finite-dimensional unitary `rho`, hence co-density.  Property (tau) gives
the uniform conjugation gap.  The HNN theorem applies with outsider `r`,
proving the Theorem and the nontriviality of the displayed mark `[t,r]` by
Britton's lemma.

There is also an unconditional exact conclusion worth isolating.

**Proposition.** The word `[t,r]` is killed by every finite-dimensional
unitary representation of `G_exp`.  Consequently `G_exp` is neither
maximally almost periodic nor residually finite.

*Proof.* Restrict such a representation to `SL_3(Z)`.  Lemma 1 makes its
image a congruence image, and Lemma 2 says that the image of `<a,b>` is the
entire image of `SL_3(Z)`.  Since `t` centralizes `a,b`, its image centralizes
the entire lattice image and in particular the image of `r`.  Thus `[t,r]`
maps to one.  Britton's lemma says the word is nevertheless nontrivial.
`QED`

The open HS theorem is exactly the robust upgrade of this proposition from
representations to normalized-HS almost representations.

In fact the whole finite-dimensional representation theory is blind to the
HNN kernel.  The natural noninjective quotient

    q:G_exp -> SL_3(Z) x Z

induces a bijection on `d`-dimensional unitary representations for every
`d`: the preceding proof forces the stable letter to commute with the full
lattice image, and factorization through `q` is unique.  The same argument
for finite target groups shows that `q` induces an isomorphism on profinite
completions; universality over compact unitary images gives an isomorphism on
Bohr compactifications.  Thus `[t,r]` is a displayed element of a
Bohr- and profinite-invisible kernel, not merely one accidentally invisible
word.

## 5. Discussion: why the plain lattice, and what is open

**Genuinely new.** Neither prior conditional route reaches `SL_n(Z)`:
- Dogon (arXiv:2211.10492) needs a central extension `1 -> Z -> ~G -> Gamma
  -> 1` with `Z` torsion-free; but `SL_n(Z)` has the congruence subgroup
  property, so `H_2(SL_n(Z), Z) = K_2(Z) = Z/2` is finite and there is no such
  extension.
- Dogon–Vigdorovich (arXiv:2506.20843) needs an archimedean place with
  `pi_1(G(R))` infinite; but `pi_1(SL_n(R)) = Z/2`.

The commutant/HNN mechanism uses neither a central extension nor an
archimedean fundamental group, so `SL_3(Z)` is admissible.  The
Detinko--Flannery--Hulpke pair removes the former explicitness caveat: the
conditional output group, its two HNN relators, and its marked outsider are
all displayed literally.

**The single open hypothesis.** Flexible HS-stability of `SL_3(Z)` is open. It
is not ruled out: `SL_3(Z)` is an infinite hyperlinear Kazhdan group, so it is
not STRICTLY (same-dimension) HS-stable, but flexible stability is a strictly
weaker property whose determination for infinite (T) groups is the entire
subject of Dogon's paper; the Ioana–Spaas–Wiersma cohomological obstructions
do not reach it (the relevant central extensions are finite, and finite
extensions of hyperlinear groups are hyperlinear). No published infinite
property-(T) host currently supplies the flexible HS-stability needed by this
construction; the literature census in Section 6 shows that the known
positive stability theorems provide no shortcut.

**Permutation twin.** The same construction with permutation (sofic)
approximations gives: if `SL_n(Z)` is flexibly permutation-stable, then `G` is
not sofic — the HNN analogue of Bowen–Burton (`PSL_d(Z)`, `d >= 5`), now from
`n = 3`, using Bourgain–Varjú expansion and Britton's lemma in place of
cofinite IRS rigidity.

## 6. The obstruction census

No published group is simultaneously flexibly HS-stable (or weakly
ucp-stable), non-amenable, and equipped with an infinite finitely generated
co-dense subgroup with property (T) or (tau). Two fences prevent assembling
one from known operations. **Fence A:** if `A` has an infinite residually
finite amenable quotient (in particular infinite abelianization), no co-dense
`C` has a uniform gap — co-density forces `C` onto growing finite quotients
whose Folner sets give almost-invariant, far-from-invariant vectors in the
deformations `rho (+) rho.chi_lambda`. **Fence B:** if `A` is LERF, a proper
f.g. subgroup is never co-dense. Every published non-amenable HS-stable group
(free and virtually free; free products; one-relator with center; chordal
graph products/RAAGs; amalgams over finite subgroups; products with amenable
groups) hits A or B, with its (T) subgroups provably finite (Niblo–Reeves
fixed points, property FA, Kurosh). Hence a first usable host requires a new
flexible-stability theorem for a congruence-rigid group; the candidate list is
`SL_2(Z[1/p])`, `SL_2(Z[1/pq])`, `SL_3(Z[1/p])`, `Sp_4(Z)`, and `SL_n(Z)`
(`n >= 3`), all with the identical single open hypothesis. `SL_n(Z)` is the
most central of these.

## 7. Toward the hypothesis

The sharpest published tools for proving flexible stability of a
congruence-rigid group / closing the equivalent Iwahori "far sector":
- de la Salle (arXiv:2204.07084): finite groups are flexibly stable with a
  linear dimension-free modulus in any tracial target, with a
  subgroup-relative correction (Lemma 1.7). This reduces the far sector, with
  explicit constants, to a length-control estimate for the congruence relator
  family against the exponential Dehn function (Taback, arXiv:math/0302191).
- Dogon–Vidick (arXiv:2607.20135): effective approximate-invariant-measure
  machinery, the route to a polynomial stability modulus for the `BS(1,4)`
  parabolic skeleton, which controls the abelian direction.
- Established scaffolding here: `BS(1,4)` has linear HS length control (from
  its stability, Levit–Vigdorovich) yet exponential Dehn function — the first
  strict `F_G << Dehn_G` separation, establishing the skeleton half of the
  length-control target; and `SL_2(Z)` stability (virtually free) handles the
  vertex, leaving only the square-root/edge compatibility. The remaining
  content of every route is this single edge statement.

**Status.** Conditional theorem proved; the hypothesis (flexible stability of
`SL_n(Z)`, or of any listed congruence-rigid lattice) is a genuine open
problem with no current shortcut. A resolution in either direction, by anyone,
resolves the conditional and — in the positive direction — produces the first
non-hyperlinear group.
