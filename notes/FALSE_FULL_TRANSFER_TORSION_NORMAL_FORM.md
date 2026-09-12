# Degree-torsion normal form for full-transfer holonomy

Date: 2026-08-11

## 1. Outcome

On a full-transfer regular cover, radical holonomy has only one genuinely
new arithmetic component.  It is the sum of

1. the fixed ordinary integral filling functional on the base complex; and
2. a character valued in the degree-torsion subgroup of `Z/qZ`.

Moreover, the quotient of the modulus by its common part with the cover
degree divides the fixed Gram content of the base cycle lattice.  Thus that
quotient ranges over a finite set independent of the cover.  Combined with
`FALSE_BASE_HOLONOMY_DUAL_NORM.md`, this identifies the complete amplified
FALSE target on full-transfer charts: an unbounded centered degree-torsion
character on a fixed finite-rank lattice.

## 2. Setup and Gram content

Use the presentation-cover notation of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`.  Let the regular cover `P_X->P`
have degree `n`, let the modulus be `q>1`, and assume

`J(K_1) <= im(A_X mod q)`,                                        `(FTN1)`

where `K_1=ker(A_1^*)` is nonzero.  Equip `K_1` with the integral Euclidean
pairing inherited from the relator coordinates and define its Gram content

`D_1=gcd{<u,v>:u,v in K_1}`.                                     `(FTN2)`

Equivalently, `D_1` is the gcd of the entries of the Gram matrix in any
integral basis of `K_1`.  It is a positive integer independent of the basis.

Put

`g=gcd(n,q)`,  `e=q/g`.                                           `(FTN3)`

**Proposition 1 (full-transfer Gram divisibility).**  Assumption `(FTN1)`
implies

`e divides D_1`.                                                  `(FTN4)`

In particular, `q/gcd(n,q)` belongs to the finite divisor set of `D_1`.

**Proof.**  For every `v in K_1`, modular transfer and Lemma 1 of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` give

`Jv/q in K_X^#`.                                                  `(FTN5)`

For every `u in K_1`, the constant lift `Ju` lies in `K_X`.  Therefore

`<Jv/q,Ju>=n<v,u>/q in Z`,                                       `(FTN6)`

so `q` divides `n<v,u>`.  Write `q=ge` and `n=gn_0`.  Since
`gcd(e,n_0)=1`, equation `(FTN6)` implies `e divides <v,u>` for all
`u,v in K_1`.  Taking the gcd proves `(FTN4)`.  End proof.

This strengthens the single-vector divisibility `q divides n||v||^2` when
the whole base lattice transfers: all Gram pairings are divisible after the
common cover-degree factor is removed.

## 3. Exact degree-torsion decomposition

Fix once and for all an integral base filling of the radical word,

`A_1^* z_0=b_w`,                                                  `(FTN7)`

and define the ordinary integral functional

`phi:K_1->Z`,  `phi(v)=<v,z_0>`.                                  `(FTN8)`

The degree-holonomy congruence `(THC29)` says

`n(Hol(Jv)-phi(v))=0 mod q`.                                     `(FTN9)`

The kernel of multiplication by `n` on `Z/qZ` is exactly

`e(Z/qZ)={e t mod q:t in Z}`,                                    `(FTN10)`

and the map

`Z/gZ -> e(Z/qZ)`,  `t |-> e t mod q`                            `(FTN11)`

is an isomorphism.

**Theorem 2 (degree-torsion normal form).**  Under `(FTN1)`, there is a
unique character

`psi_(w,X,q):K_1->Z/gZ`                                          `(FTN12)`

such that, for every `v in K_1`,

`Hol_(w,X,q)(Jv)=phi(v)+e psi_(w,X,q)(v) mod q`.                  `(FTN13)`

**Proof.**  Equation `(FTN9)` puts `Hol(Jv)-phi(v)` in the subgroup
`(FTN10)`.  The isomorphism `(FTN11)` gives a unique value `psi(v) in Z/gZ`
satisfying `(FTN13)`.  Both `Hol` and `phi mod q` are homomorphisms, and
`(FTN11)` is injective, so uniqueness forces `psi` to be a homomorphism.
End proof.

Changing `z_0` changes `phi` by an ordinary integral functional and changes
`psi` by the corresponding torsion correction.  The sum `(FTN13)`, and
hence the divergence criterion below, is independent of this choice.

## 4. Centered norm comparison

Choose an integral basis `v_1,...,v_k` of `K_1`.  Put

`f_i=phi(v_i) in Z`,                                              `(FTN14)`

and let `t_i in [-g/2,g/2] intersect Z` be a centered representative of
`psi(v_i)`.  Let `c_i in [-q/2,q/2] intersect Z` be a centered
representative of `Hol(Jv_i)`.  Write `f=(f_i)`, `t=(t_i)`, and `c=(c_i)`.

**Proposition 3 (centered torsion comparison).**

`abs(||c||_2-e||t||_2) <= ||f||_2`.                               `(FTN15)`

In particular, along any sequence of full-transfer stages,

`||c_j||_2->infinity iff e_j||t_j||_2->infinity`.                `(FTN16)`

After passing to a subsequence, `e_j` is constant by Proposition 1, so this
is also equivalent to `||t_j||_2->infinity`.

**Proof.**  For each coordinate, `(FTN13)` and the fact that distance to a
fixed closed subset of `R` is `1`-Lipschitz give

`abs(H_q(f_i+e t_i)-H_q(e t_i)) <= |f_i|`.                        `(FTN17)`

Since `t_i` is centered modulo `g` and `q=eg`,

`H_q(e t_i)=e H_g(t_i)=e|t_i|`,                                  `(FTN18)`

while `H_q(f_i+e t_i)=|c_i|`.  Thus

`abs(|c_i|-e|t_i|)<=|f_i|`.                                      `(FTN19)`

Apply the triangle and reverse-triangle inequalities to the nonnegative
coordinate vectors `(|c_i|)` and `(e|t_i|)` to obtain `(FTN15)`.  The vector
`f` is fixed, and Proposition 1 restricts every `e_j` to the finite divisor
set of `D_1`, proving `(FTN16)` and its subsequence refinement.  End proof.

## 5. Complete full-transfer FALSE criterion

Combine Proposition 3 with Corollary 3 of
`FALSE_BASE_HOLONOMY_DUAL_NORM.md`.

**Corollary 4 (unbounded degree torsion proves FALSE).**  Suppose regular
covers `X_j` and moduli `q_j` satisfy full transfer `(FTN1)`.  Let
`psi_j:K_1->Z/g_jZ` be the characters in Theorem 2, and let `t_j` be their
centered coordinate vectors in one fixed integral basis.  If

`||t_j||_2->infinity`,                                            `(FTN20)`

then a hyperlinear nonsofic group exists.

More generally it is enough that the sequence `||t_j||_2` is unbounded,
since one may pass to a subsequence on which it tends to infinity and on
which the divisor `e_j=q_j/g_j` is constant.

**Proof.**  Proposition 3 makes the centered holonomy vectors `c_j`
unbounded.  After passage to a subsequence they tend to infinity.  Corollary
3 of `FALSE_BASE_HOLONOMY_DUAL_NORM.md` then supplies a fixed primitive base
cycle satisfying the amplified transfer-holonomy criterion.  End proof.

## 6. Computational normal form

Let `V=[v_1 ... v_k]` be the fixed basis matrix.  At a candidate stage:

1. solve `A_X[a_1 ... a_k]=JV mod q`;
2. compute and center `h_i=<a_i,b_(w,x)> mod q`;
3. verify the necessary screen `e=q/gcd(n,q) divides D_1`;
4. subtract the fixed values `f_i=<v_i,z_0>`;
5. divide the residues `h_i-f_i` by `e` in the subgroup `e(Z/qZ)` and
   center the resulting values modulo `g`.

The output is exactly the vector `t`.  The live arithmetic signal is now

`||t||_2 unbounded`,                                              `(FTN21)`

not an optimization over base cycles and not a positive-fraction condition
relative to `q`.  If `gcd(n,q)=1`, then `g=1`, `psi=0`, and all centered
holonomies are bounded by the fixed filling vector `f`, recovering the
coprime no-go in Proposition 4 of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`.

## 7. Scope

This note does not show that full-transfer stages with unbounded torsion
characters exist.  It gives their exact arithmetic normal form.  All
unbounded behavior must live in the growing common part `g=gcd(n,q)` of the
cover degree and the modulus; the complementary factor `e=q/g` is confined
to the fixed divisor set of the base Gram content.  Thus the remaining
full-transfer construction problem is a fixed-rank torsion-character
problem in the nonsemisimple norm sector, with no hidden real or
variable-cycle component.
