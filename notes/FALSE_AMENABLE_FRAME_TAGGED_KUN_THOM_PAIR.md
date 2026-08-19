# An amenable-frame tag for the actual Kun--Thom radical orbit

Date: 2026-08-12

**Status.** The coefficient-frame construction below is correct, but the
finite tag has the short recurrence `(AFT38)`. The preferred construction is
now `FALSE_AMENABLE_MONOMIAL_FRAME_KUN_THOM_PAIR.md`, which puts the frame in
the Laurent exponent lattice. Its orbit monomials are linearly independent,
so it keeps the amenable stabilizer without introducing that recurrence.

## 1. Outcome

The square-zero Kun--Thom pair can be modified so that the **actual marked
Laurent coefficient**, not an auxiliary external orbit, has amenable
stabilizer. The modification is finite-dimensional: tensor the square-zero
coefficient with an ordered two-frame for `SL_3`.

All algebraic features of the paired Baumslag--Solitar construction remain:

1. the vertex and edge groups are residually finite Kazhdan groups;
2. the edge is infranormal and nonnormal;
3. the symmetric double has an explicit nontrivial word in its full sofic
   radical;
4. the explicit ordinary/cyclotomic Baumslag--Solitar Bockstein class marks
   that word and survives every double-coset stabilizer; and
5. the external orbit of its marked tangent label is `L/H_*` with `H_*`
   amenable.

Since `L=SL_3(Z)` is residually finite, Gao--Patchell--Kunnawalkam
Elayavalli's amenable-stabilizer theorem now supplies sofic finite orbit
charts for the marked orbit itself.

This removes a mismatch in the preceding chart argument: the earlier
amenable orbit `L/<t,s>` was an auxiliary orbit, whereas the original
marked monomial had a nonamenable parabolic stabilizer. The frame tag makes
the two orbits coincide at the point that matters.

It is not yet a complete FALSE proof. One must still extend the paired
Fourier block from the marked orbit to a chart-functorial map on each fixed
finite elementary/tangent window, and that extension must remain genuinely
nonliftable for the Kazhdan base action. Section 8 states the remaining
local lemma precisely.

## 2. The tagged square-zero coefficient ring

Fix an odd prime `p`, put

`q=p+1`, `A=Z[1/q]`,                                   `(AFT1)`

and let

`V=A^3`, `Q=SL_3(A)`.                                  `(AFT2)`

Let

`U=M_(3 times 2)(A)`                                  `(AFT3)`

be the module of ordered two-frames, with `SL_3(Z)` acting by left
multiplication. Put

`J=V tensor_A U`                                      `(AFT4)`

and form the commutative square-zero algebra

`C=A directSum J`, `J^2=0`.                            `(AFT5)`

The group `Q` acts on the `V` factor, and

`L=SL_3(Z)`                                           `(AFT6)`

acts on the `U` factor. These actions commute and act by unital ring
automorphisms of `C`.

Let `L` also act by monomial substitutions on three variables and put

`R_+=C[x_1,x_2,x_3]`,

`R=C[x_1^(+-1),x_2^(+-1),x_3^(+-1)].`                 `(AFT7)`

For even `r>=4`, define

`Gamma=E_r(R_+) semidirect Q`,

`G=E_r(R) semidirect (Q times L).`                     `(AFT8)`

The action of `L` on a tagged monomial is

`g.(a tensor u tensor x^z)=a tensor (gu) tensor x^(gz).` `(AFT9)`

## 3. The Kun--Thom pair survives the tag

**Theorem 1.** The groups `Gamma<G` in `(AFT8)` are residually finite and
have property `(T)`. The subgroup `Gamma` is infranormal and nonnormal in
`G`, and its compression semigroup generates `G`.

**Proof.** The rings in `(AFT7)` are finitely generated commutative unital
rings. Universal-lattice property `(T)` applies to their elementary groups.
Both `Q` and `L` have property `(T)`, and property `(T)` is closed under
extensions. Hence both groups in `(AFT8)` are Kazhdan.

Every nonnegative elementary substitution `I+e_ij in L` sends the positive
exponent cone into itself. It also preserves the full finite coefficient
module `U`; unlike a one-dimensional tag line, no tag restriction is placed
in `R_+`. Therefore it compresses `Gamma` into itself. These substitutions
generate `L` as a group. Their conjugates of the positive elementary root
groups generate every Laurent root group: given `z in Z^3`, choose
`g in L` and `z_+ in N^3` with `g z_+=z`; the source coefficient may be
chosen as `g^(-1)u` because all of `U` occurs in `R_+`. Additivity of
elementary roots handles Laurent polynomials. Thus the compression
semigroup generates `G`, which is the infranormality criterion used in the
Kun--Thom construction.

The inclusion is nonnormal because an inverse elementary substitution sends
a positive exponent to one with a negative coordinate; Section 4 gives an
explicit tagged witness.

Residual finiteness is also unchanged. Reduce `A` modulo a prime not
dividing `q`, reduce `V` and `U` over the resulting finite field, and reduce
the exponent lattice modulo `m`. This gives finite equivariant quotients

`C_(ell)=F_ell directSum`
` (F_ell^3 tensor M_(3 times 2)(F_ell))`,              `(AFT10)`

`R->C_(ell)[(Z/mZ)^3]`,                               `(AFT11)`

together with the corresponding finite quotients of `Q` and `L`. Varying
`ell,m` separates every nonidentity matrix and external component. End
proof.

## 4. The tagged strict fold

Use column-vector conventions and put

`t=I+e_12`, `s=I+e_13 in L`.                           `(AFT12)`

Let

`v_0=(e_1,e_2) in U`,

`u_0=t v_0=(e_1,e_1+e_2).`                            `(AFT13)`

Then

`t^(-1)u_0=v_0`, `s v_0=v_0`,

`t^(-1)e_2=e_2-e_1`, `s(e_2-e_1)=e_2-e_1`.           `(AFT14)`

Let `a=e_1 in V` and let

`P=diag(1,-1,1,-1,...,1,-1).`                         `(AFT15)`

Define

`gamma=1+(a tensor u_0)x_2 P in Gamma`,               `(AFT16)`

`h=t^(-1) gamma t`
` =1+(a tensor v_0)x^(e_2-e_1)P in G`.                `(AFT17)`

The square-zero diagonal factorization used in the untagged construction
shows that both matrices lie in the relevant elementary groups. The
negative first exponent in `(AFT17)` shows `h notin Gamma`.

Put

`c_0=diag(q,1,q^(-1)) in Q`, `c=(c_0,s) in Q times L`. `(AFT18)`

The `Q`-component scales `a` by `q`, while `(AFT14)` says that `s` fixes
both the frame and monomial parts of the marked Laurent coefficient.
Therefore

`c h c^(-1)=h^q`.                                     `(AFT19)`

The external projection of `c` is the infinite-order element `s`, and the
square-zero formula gives

`h^m=1+m(a tensor v_0)x^(e_2-e_1)P`.                  `(AFT20)`

Consequently

`B=<h,c>~=BS(1,q).`                                    `(AFT21)`

## 5. The actual marked orbit has amenable stabilizer

Write

`z_* = v_0 tensor x^(e_2-e_1)`                        `(AFT22)`

for the tag-monomial part of the marked tangent coefficient. Let

`H_*=Stab_L(z_*)`.                                     `(AFT23)`

Because Laurent monomials form an `A`-basis, an element fixing `(AFT22)`
must in particular fix the ordered frame `v_0`. But

`Stab_L(v_0)`
` ={I+a e_13+b e_23:a,b in Z}~=Z^2.`                  `(AFT24)`

Indeed, fixing `e_1,e_2` fixes the first two columns, and determinant one
forces the third diagonal entry to be one. Thus

Every matrix in `(AFT24)` also fixes `e_2-e_1`. Consequently

`H_*=Stab_L(v_0)~=Z^2`,                                `(AFT25)`

so `H_*` is amenable. Notice that `s in H_*` by `(AFT14)`.

The orbit of the actual marked coefficient is therefore

`L.z_* ~= L/H_*`.                                      `(AFT26)`

Since `L` is residually finite and hence sofic, the amenable-stabilizer
orbit theorem gives

`L curvearrowright L.z_* is a sofic action.`           `(AFT27)`

This is the key gain over the untagged pair. There the monomial
`x^(e_2-e_1)` has a nonamenable parabolic stabilizer; here its ordered-frame
tag cuts the stabilizer down to an abelian subgroup without changing the
positive Laurent cone.

## 6. The paired class and radical word are unchanged

The normalized bar chain

`Z_p=sum_(j=1)^p [h^j|h]`
`    -[c|h]-[ch|c^(-1)]+[c^(-1)|c]`                  `(AFT28)`

depends only on the Baumslag--Solitar relation `(AFT19)`. Therefore all
calculations from the untagged paired construction apply verbatim:

`partial Z_p=p[h]`, `partial_chi Z_p=(1-zeta_p)[c^(-1)]`, `(AFT29)`

and both ordinary and cyclotomic Bocksteins are injective on

`H_2(B,F_p)=F_p[Z_p].`                                 `(AFT30)`

Let `rho_L:G->L` be the external projection. Every conjugate of `Gamma`
has trivial external projection, while an element of `B` with stable-letter
exponent `m` has projection `s^m`. Hence

`B cap g Gamma g^(-1) <= ker(B->Z)`                    `(AFT31)`

for every `g in G`. The cyclotomic argument from
`FALSE_RADICAL_BS_PAIRED_KUN_THOM_DOUBLE.md` proves that the class
`[Z_p]` survives all double-coset stabilizer images.

Let `N` be the normal closure of `Gamma` in `G`. The compression-semigroup
argument in Theorem 1 gives

`N=E_r(R) semidirect Q=ker(rho_L).`                    `(AFT32)`

Form the symmetric double

`D=G *_Gamma G`                                       `(AFT33)`

and put

`w=i_2(h)i_1(h)^(-1).`                                `(AFT34)`

Since `h in N\Gamma`, the Kun--Thom complete-radical theorem and amalgam
normal form give

`1!=w in Rad_sof(D)`.                                  `(AFT35)`

Thus the amenable tag has not changed the marked group-theoretic endpoint.

## 7. Why the tag is compatible with finite Frobenius models

Modulo `p^n` and a finite exponent quotient, the tangent module is still
finite. The frame factor introduces no nonlinear relations: it is a finite
free additive module on which the external congruence group acts linearly.
The translation/multiplier construction may use the canonical dual pairing

`U_n^* times U_n -> Z/p^n Z`                           `(AFT36)`

rather than an invariant Euclidean self-pairing. External transport acts on
the multiplier coordinate contragrediently, so `(AFT36)` is exactly
invariant. Equivalently, one may use the hyperbolic self-dual module
`U_n directSum U_n^*`.

The tagged marked vector remains primitive modulo `p^n`. Hence the local
Fourier character calculation still gives

`tr(B_0(z_*)^p)=0`,

`||B_0(z_*)^p-1||_2^2=2`                              `(AFT37)`

for every `n>=2`.

## 8. The reduced analytic endpoint and an essential warning

Let `E` be a fixed finite window in the tagged tangent and base elementary
groups, and let `F` be a fixed finite window in `L`. The action `(AFT27)`
provides finite root-dependent charts which are exactly covariant on
`F` over a set of roots of density `1-o(1)`.

The first remaining requirement is to define, on each good root, the paired
Fourier/Frobenius map for `E` so that changing the local representative by
an element of `H_*` conjugates the fiber map by the corresponding stabilizer
operator. The ordered frame makes this the covariance problem for the
**actual** marked orbit. Since `H_*=Z^2`, every fixed transition set is
amenable and the long paired chain can be chosen deeper than all its tested
exponents.

There is a second requirement which the tag does not remove. Since the
positive ring contains the full tag module, the positive subgroup also
contains the label `v_0 tensor x_2`. In a finite Laurent quotient the base
elementary action can propagate this label to
`v_0 tensor x^(e_2-e_1)`. The property-`(T)` cyclic-seed theorem in
`FALSE_KAZHDAN_CYCLIC_SEED_PROPAGATION_NO_GO.md` shows that exact base
representations with exact tangent covariance would then erase the fold,
with no word-length loss. Equivalently, the short tag recurrence

`t^(-1)u_0=(2-t)u_0`                                  `(AFT38)`

shows that the finite-dimensional frame itself is not a new branch-cut
coordinate.

Therefore the required local chart map must also realize the Laurent
collision only approximately, in a way which stays a fixed distance from
every exact Kazhdan-covariant finite model. If both this nonliftable
base/tangent condition and the `H_*` stabilizer covariance are proved, the
orbit-chart induction estimate gives

`vertex and amalgam defects ->0`,

`marked fold distance^2 ->2`.                          `(AFT39)`

The compatible-pair endpoint then produces a hyperlinear nonsofic image of
`D`. Thus the tag removes the nonamenable orbit-stabilizer part of external
coherence, but it does not solve the kernel-carry/finite-Laurent collision.
The remaining statement is a local `Z^2`-equivariant **nonliftable**
Frobenius block, exactly the kind of object isolated by `(RBF20)` in
`FALSE_REGULAR_BUNDLE_FREE_TABLE_AND_KERNEL_GATE.md`.
