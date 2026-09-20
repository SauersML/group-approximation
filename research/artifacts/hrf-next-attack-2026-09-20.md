# A split elementary-abelian radical need not enlarge finite twist detection

Date: 2026-09-20. Written proof; no computational or Lean certification.
The existence of a non-residually-finite word-hyperbolic group remains open.
This artifact proves the precise obstruction in
[[hrf-next-affine-radicals-preserve-detector-image]].

## 1. The new boundary

The separate parallel work named `hrf-alt-edge-twist-finite-detector-spectrum`
identifies edge-twist detectors through
`D_f:H^2(Q;F_p)->T`, for finite quotients `f:Lambda->>Q` of a triangle
colimit with perfect vertices and vanishing vertex `H^2(-;F_p)`.
The earlier composition-factor obstruction excludes quotients built from
PSL2 simple factors and cyclic factors different from `C_p`. It leaves
the solvable radical as a real gap.

Here is a narrower theorem addressing that gap. Let `p` be odd,
`k=F_p`, and let

```
f: Lambda ->> Q = V semidirect S,
g: Lambda ->> S
```

be a finite quotient and its projection, with `V` an elementary abelian
normal subgroup viewed as a finite-dimensional `kS`-module. Assume the
vertex groups `A_i` are perfect, have `H^2(A_i;k)=0`, and

```
H^1(S;V*) = 0,
H^1(A_i;V) = 0 for every vertex i,
```

where the vertex action on `V` is through `g|A_i` and `V*` has the
contragredient action. Then

```
image D_f = image D_g.                                      (1)
```

More precisely every `beta in H^2(Q;k)` satisfies

```
D_f(beta) = D_g(res_S beta),                                (2)
```

using the displayed standard complement `S<=Q`.
Thus this radical contributes no new detecting twist, even if `H^2(Q;k)`
has large new dimension from invariant alternating forms on `V`.
If `H^2(S;k)=0`, then `D_f=0`. The present theorem assumes or verifies
that last vanishing separately in any proposed application; no finite
simple-group cohomology table is needed for its proof.

The vertex `H^1` hypotheses can be weakened: only the specific affine
cocycle supplied by `f|A_i` must be a coboundary. No assertion is made
that all finite quotients satisfy any of these hypotheses.

## 1a. Definition and elementary properties of the discrepancy maps

This section makes the proof independent of the separate parallel
detector-spectrum work. All cohomology in degree two here has trivial
coefficients `k`. Put `T=direct-sum_e Hom(E_e,k)` and orient each edge
from its vertex `i` to its vertex `j`. For a homomorphism
`q:Lambda->R` to a finite group, represent `beta in H^2(R;k)` by a
central extension

```
1 -> k --z--> F --pi--> R -> 1.
```

Concretely, a normalized 2-cocycle `c` represents the extension on
`k x R` with product `(t,r)(u,s)=(t+u+c(r,s),rs)`; changing `c` by
a coboundary gives an extension isomorphism identical on kernel and
quotient. Conversely a set-theoretic section of an extension gives
such a cocycle, so this realizes precisely the usual `H^2` classes.

For each vertex map `q_i:A_i->R`, the pullback extension has zero class
because `H^2(A_i;k)=0`. It has a homomorphic section, equivalently a
homomorphism `s_i:A_i->F` with `pi s_i=q_i`. Two lifts differ by a
function into the central kernel; their homomorphism identities make
that function a homomorphism `A_i->k`. Perfectness of `A_i` makes
it zero. Thus the lift exists and is unique, even if `q_i` is not
injective.

On an oriented edge the maps into `R` agree. Suppressing the two
specified edge inclusions, define `d_e:E_e->k` by

```
s_i(x) = z^(d_e(x)) s_j(x).
```

The centrality of `z(k)` and the homomorphism identities for the two
lifts give `d_e(xy)=d_e(x)+d_e(y)`. Hence `d_e` is in `Hom(E_e,k)`.
Set `D_q(beta)=(d_e)_e`. An equivalence of extensions carries the
unique vertex lifts to the unique vertex lifts, so the map depends
only on `beta`.

For two extensions, take their fiber product over `R` and push its
kernel `k x k` out by addition. This is the Baer sum. The paired
vertex lifts descend to the unique lifts into the sum, and their edge
ratios become `z^(d_e+d'_e)`. Thus `D_q` is additive. Pushing a kernel
out along multiplication by any scalar in `k` multiplies the edge
ratios by that scalar (including the split pushout at scalar zero).
Therefore `D_q` is `k`-linear.

For naturality, let `r:R->R'`, and let `beta'` be an extension of
`R'`. Its pullback to `R` consists of pairs `(a,y)` with
`r(a)=pi'(y)`. If `s'_i` is the unique lift of `r q_i`, the unique
lift of `q_i` to this pullback is `(q_i,s'_i)`. Its edge ratio is
exactly the old edge ratio. Consequently

```
D_q(r* beta') = D_(r q)(beta').
```

This includes the inflation identity used in Section 4. The zero
class has zero discrepancy: in the split extension the unique vertex
lifts are `a -> (0,q_i(a))`.

The term "detector" records a direct universal-property consequence.
For the edge-twisted colimit with central kernel `k`, use the convention
that its canonical vertex lifts obey `a_i(x)=z^(c_e(x))a_j(x)`.
If `D_q(beta)=c`, its vertex maps into `F` agree on all the twisted
edge relations and induce a map of the colimit into the finite group
`F` identical on the central kernel. Conversely any finite image
injective on that kernel, divided by that kernel, is a finite quotient
of the untwisted colimit; its vertex lifts have exactly those
discrepancies. The proof of (1)--(2) only needs the discrepancy maps
and their elementary properties just proved; it does not need a
geometric developability or virtual-splitting theorem.

## 2. Perfectness and the two invariants of a central extension

Since `Lambda` is generated by its perfect vertex groups, `Lambda` and
every quotient are perfect. The abelianization of `V semidirect S` is
`V_S direct-sum S_ab`; consequently

```
V_S=0 and S_ab=0.                                          (3)
```

Take an arbitrary central extension `1->k->F->Q->1`, and let `P` be
the preimage of `V`. Its commutators lie in the central kernel. For lifts
`v_tilde,w_tilde in P`, define

```
b(v,w) = [v_tilde,w_tilde] in k,
h(v) = v_tilde^p in k.
```

Both are independent of lifts. The commutator map `b` is alternating
and bilinear. The power map `h` is additive: the class-two power formula
has a commutator correction with exponent `p(p-1)/2`, divisible by `p`
because `p` is odd. It is therefore `k`-linear. Conjugation by lifts of
`S` makes `b` and `h` invariant. Equation (3) gives
`Hom_S(V,k)=0`, so `h=0`.

For an invariant alternating form `b`, put

```
H_b = V x k,
(v,t)(w,u) = (v+w,t+u+b(v,w)/2).
```

Its commutator form is `b`, its power map is zero, and `S` acts by
`s(v,t)=(sv,t)`. Thus

```
F_b = H_b semidirect S -> V semidirect S
```

is a central extension splitting on `S` and realizing the two invariants
of `P`. Equality of these invariants characterizes the extension over
`V`: in the Baer difference, both invariants vanish, so the extension
group is abelian of exponent `p`. It is a vector-space extension and
has a linear splitting.

## 3. Eliminating the remaining mixed extension

Let `beta=[F]`, let `alpha=res_S beta`, and subtract both the inflation
of `alpha` and the class `[F_b]`. The difference `eta` restricts to zero
on both `S` and `V`. We prove directly that `eta=0` under
`H^1(S;V*)=0`.

Represent `eta` by `E->Q`, choose homomorphic sections `j:V->E` and
`a:S->E`, and write the central kernel additively using `z^t` notation.
Define `ell_s in V*` by

```
a(s) j(v) a(s)^(-1) = j(sv) z^(ell_s(sv)).
```

The section `j` is a homomorphism and the kernel is central, so `ell_s`
is linear. Conjugation successively by `a(t)` and `a(s)` gives

```
ell_(st) = ell_s + s.ell_t,
(s.ell)(w)=ell(s^(-1)w).
```

Hence `ell` is a 1-cocycle. Replacing `j(v)` by `j(v)z^(r(v))` changes
`ell_s` to `ell_s+s.r-r`. Its cohomology class vanishes, so choose `r`
making every new `ell_s` zero. Now the sections satisfy exactly the
semidirect-product relations, and `j(v)a(s)` is a homomorphic section
of `E->Q`. We have proved the decomposition

```
beta = inf_S^Q(alpha) + [F_b].                              (4)
```

This elementary argument is the degree-two extension calculation behind
the Hochschild--Serre filtration. It retains the mixed `H^1(S;V*)` term
as a real hypothesis instead of silently discarding it.

## 4. The Heisenberg contribution has zero edge discrepancy

Write each vertex map as

```
f_i(a) = (u_i(a),g_i(a)).
```

The homomorphism law makes `u_i` a 1-cocycle for the action through
`g_i`. The vertex hypothesis gives a vector `v_i in V` such that

```
u_i(a) = v_i - g_i(a)v_i.
```

Thus `f_i` is the conjugate by `(v_i,1)` of the map into the standard
complement. Its lift to `F_b` is

```
L_i(a) = (v_i,0) (0,0,g_i(a)) (-v_i,0)
       = (v_i-sv_i, -b(v_i,sv_i)/2, s),  s=g_i(a).
```

This is a homomorphism. It is the unique lift since `A_i` is perfect:
two lifts differ by a homomorphism `A_i->k`.

For an edge element shared by vertices `i,j`, the two images in `Q`
are equal. Their `S` coordinates agree, say at `s`, and their vector
coordinates agree, so `d=v_i-v_j` satisfies `sd=d`. The difference
of their central coordinates is minus one half of

```
b(v_i,sv_i)-b(v_j,sv_j)
 = b(d,sv_j)+b(v_j,d)+b(d,d)
 = b(s^(-1)d,v_j)+b(v_j,d)
 = 0.                                                      (5)
```

Therefore the unique vertex lifts agree on every edge. The Heisenberg
extension has `D_f([F_b])=0`. Inflation of `alpha` has precisely the
same unique vertex-lift discrepancies as `alpha` along `g`. Linearity
of `D_f` and (4) prove (2). Conversely every `alpha in H^2(S;k)`
inflates to `Q`, and its restriction back to `S` is `alpha`. This proves
the equality of images in (1).

## 5. What this rules out, and what remains

Adding an elementary-abelian `p`-radical and then taking its Heisenberg
central extension is not automatically a finite detector. Equation (5)
is the obstruction: conjugate complement lifts agree wherever the
complements agree. Nonzero Schur multiplier alone was already known to
be insufficient; here an entire source of new multiplier classes is
proved to have zero discrepancy, with the mixed-extension hypothesis
stated exactly.

For a split affine detector over a base with `H^2(S;k)=0`, one must
therefore encounter either a nonzero `H^1(S;V*)` or a vertex affine
cocycle that is not a coboundary. For a self-dual `V` and vertex maps
identifying each `A_i` with `S`, both vanish when `H^1(S;V)=0`.
This gives a module-cohomology search filter rather than just a
composition-factor search filter. Nonsplit extensions, nonabelian
radicals, and arbitrary subsequent towers are outside the theorem.

There is a separate caution about today's recorded PSL2 seed maps.
If `f_0:Lambda->>S` has kernel `N` with `H^1(N;k)=0`, no nontrivial
elementary-abelian refinement of that *fixed map* exists at all:
a surjection `f:Lambda->>V semidirect S` with projection `f_0` would
restrict to a surjection `N->>V`, a contradiction. More generally it
has no nontrivial finite p-group refinement, since any nontrivial finite
p-group has a `C_p` quotient. This uses only the already recorded
first-homology premise and supplies no evidence about different base
quotient maps. In particular, (1) is not presented as an additional
numerical test passed by those same seed refinements.

## 6. Prior art, status, and checks

The classical background is G. Hochschild and J.-P. Serre,
*Cohomology of group extensions*, Trans. AMS 74 (1953), 110--134,
DOI [10.1090/S0002-9947-1953-0052438-8](https://doi.org/10.1090/S0002-9947-1953-0052438-8).
The authors' paper was accessed through the
[Rochester copy](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hochschild-serre.pdf)
on 2026-09-20. Its extension spectral sequence is standard background;
Sections 2--4 above supply the full specialized proof without an
uncomputed spectral-sequence differential or representation table.
No claim of literature novelty is made.

Repository duplicate searches for affine detectors, conjugate complements,
Heisenberg discrepancies, and split elementary-abelian extensions found
no copy of (1). The Mackey split-cocycle note concerns a locally finite
characteristic-two kernel and a different approximation question, so it
does not duplicate this finite odd-characteristic detector theorem.
The owned node records its distinction from the tracked cellular
moment-test theorem. The parallel `hrf-alt-edge-twist-finite-detector-spectrum`
and `hrf-alt-psl2-detectors-need-new-composition-factors` work motivated
the attack and is acknowledged here; neither is a prerequisite of this
self-contained proof. No existing campaign or `hrf-*` file was changed.

The root status was rechecked against Cui--Wan,
[*Tits Alternative in groups with proper product actions on proper
Gromov-hyperbolic spaces*](https://arxiv.org/html/2604.04007), Section 1.2,
on 2026-09-20: their 5 April 2026 primary preprint explicitly retains
universal hyperbolic residual finiteness as open. This artifact supplies
no resolution. No Liu or Thom approximation theorem is used; those
inputs belong to the separate existing stability campaign.

Only reading, literature search, and Markdown edits were performed.
Graph build/duplicate-similarity checks and independent review are left
to the integrating coordinator; no local computation or MSI job ran.
