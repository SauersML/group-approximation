# The coinduced parity algebra is the negative central corner

Date: 2026-08-11

The universal cyclic module in `notes/FALSE_MACKEY_SPLIT_COCYCLE.md` and the
coinduced crossed product in `notes/FALSE_COINDUCED_PARITY_MODEL.md` are not
merely related representations.  They are the two standard descriptions of
the same central character corner.  This note records the exact
identification and its MF/Connes-embedding scope.

## 1. The universal central extension

Retain the notation of Theorems 6--8 in
`notes/FALSE_MACKEY_SPLIT_COCYCLE.md`:

`0 -> <z> ~= C_2 -> A_univ -> A_0 -> 0`,               `(NCC1)`

`A_0=directSum_(Y) C_2`, `Y=G/<s>`,

`E=A_univ semidirect G`, `Q=A_0 semidirect G`.          `(NCC2)`

The element `z` is fixed by `G`, hence is central in `E`.  In the group von
Neumann algebra put

`p_+=(1+u_z)/2`, `p_-=(1-u_z)/2`.                      `(NCC3)`

These are complementary central projections of canonical trace `1/2`.

## 2. Fourier description of the two fibers

Because `A_univ` is discrete abelian,

`L(A_univ)=L_infinity(dual(A_univ))`.                  `(NCC4)`

Restriction of a character to `<z>` splits the dual into two clopen
`G`-invariant fibers

`X_+={eta:eta(z)=1}`, `X_-={eta:eta(z)=-1}`.           `(NCC5)`

Under `(NCC4)`, `p_+` and `p_-` are their characteristic functions.

The positive fiber is canonically `dual(A_0)={-1,1}^Y`, with the ordinary
coordinate-permutation action.  To identify the negative fiber, use the
basis

`{z} union {e_y:y in Y}`                               `(NCC6)`

from `(MSC20ai)`.  A character in `X_-` is uniquely determined by

`x_y=eta(e_y) in {-1,1}`.                              `(NCC7)`

The action formula

`g e_y=e_(gy)+(kappa(g,y) mod 2)z`                     `(NCC8)`

then becomes, up to the harmless choice of left-versus-right action
convention,

`(g dot x)_(gy)=(-1)^(kappa(g,y))x_y`.                 `(NCC9)`

This is exactly the signed coinduced action `(CPM5)`.

## 3. Central-corner theorem

Since

`L(E)=L(A_univ) crossed G`,                            `(NCC10)`

and the projections in `(NCC3)` are `G`-invariant and central, cutting
`(NCC10)` by the two fibers gives

`p_+ L(E) ~= L(Q)`,                                    `(NCC11)`

`p_- L(E) ~= L_infinity({-1,1}^Y) crossed_(signed) G`. `(NCC12)`

The isomorphism in `(NCC12)` carries the normalized corner trace

`tau_-(x)=2 tau_E(x)`, `x in p_-L(E)`,                 `(NCC13)`

to the canonical crossed-product trace `(CPM17)`.  In particular the
corner unitaries `p_-u_g` give the trace-preserving canonical copy of
`L(G)` noted in `(CPM21)`.

The same Fourier calculation at the reduced C-star level gives

`p_+ C_r^*(E) ~= C_r^*(Q)`,                            `(NCC14)`

`p_- C_r^*(E) ~= C({-1,1}^Y) crossed_(r,signed) G`
`                 = A_(G,s)`.                         `(NCC15)`

Here the last equality is the concrete algebra `(CPM19)`, generated in the
canonical finite crossed product.  The full crossed products admit the
analogous full-group-C-star decomposition.

## 4. Exact consequence and exact limitation

Equations `(NCC12)` and `(NCC15)` unify the two current FALSE endpoints:

* Connes embeddability of the coinduced algebra is precisely Connes
  embeddability of the negative central corner of `L(E)`.
* MF of `A_(G,s)` is precisely MF of the negative central corner of
  `C_r^*(E)`.

Either property retains `z` as the scalar `-1` and therefore yields the
hyperlinear nonsofic image already proved in Corollaries 2--3 of the
coinduced note.

This identification is not an MF permanence theorem.  The positive corner
is the untwisted wreath quotient, while the negative corner is exactly the
Schreier multiplier `(MSC20am)`.  MF of an ambient completion of `E`, or MF
of the negative reduced corner itself, remains to be proved.  Conversely,
the canonical inclusion `L(G) subset p_-L(E)` shows again that Connes
embeddability of the negative corner already forces the required
hyperlinear visibility of the acting group.  The calculation removes a
representation-choice ambiguity; it does not remove the analytic gate.
