# The finite-presentation `INF/FIN` route: an engine/compiler interface firewall

**Date:** 2026-08-26  
**Scope:** MF only; finite-presentation compilation  
**Method:** Cairn audit and elementary free-group normal forms  
**Not used:** Lean execution, MSI, Silico, literature, tensor-rope completion,
or `Transport.CompletionLemma`

## Verdict

The repository has a valid branch-sensitive recursive front end, but it does
not currently have a zero-input proof of the finite-presentation back end.
The natural proposed back end

```text
exact event-cut switch
  -> bidirectional two-generator HNN bridge
  -> MF Boone engine
  -> Aanderaa tau/d/sigma rope
  -> finite presentation
```

contains two distinct gaps.

1. The Rotman--Turing Boone engine has the word-by-word detector that the
   Aanderaa rope consumes, but its MF claim and all three MF rope-permanence
   claims are open in the repository.
2. The formally developed modular-machine Boone engine has a rigorous
   configuration detector, but that detector cannot be substituted for the
   word-by-word detector.  It encodes a whole input word as one element of a
   free basis.  The Aanderaa transport is induced letter by letter by a group
   homomorphism.  A whole-word-to-one-basis-letter encoding cannot be a
   homomorphism, even on the positive word monoid.

The second point is an elementary, unconditional interface firewall.  It
rules out the most immediate proposed repair: replacing the open
Rotman--Turing engine in `mf-safe-compiler-via-aanderaa-boone-tower` by the
formal modular-machine engine.

There is also a zero-literature dependency failure.  The repository's claimed
MF proof for the modular-machine engine uses `regular-mf-central-hnn-closure`,
whose proof explicitly invokes Shulman's central-HNN theorem, as well as an
amenable-amalgam theorem.  Those are literature inputs, so they cannot be used
under the present specification.

Thus no unconditional proof of

\[
 e\in\mathrm{INF}\Longrightarrow R(E,e)\text{ is MF},\qquad
 e\in\mathrm{FIN}\Longrightarrow E\hookrightarrow R(E,e)
\]

is presently available from this candidate route.

## 1. What is already sound: the branch-sensitive front end

`ExactLiteralEFinInfSwitch` builds a recursively presented ray of copies of a
fixed finitely presented seed `E`.

At stage `j`, an event kills the `j`-th copy.  A non-event identifies the
`j`-th and `(j+1)`-st copies generator by generator.  The file proves directly:

\[
 \text{unbounded events}\Longrightarrow S_e=1,
\]

and

\[
 \text{finite events with last cut }J\Longrightarrow S_e\cong E.
\]

The negative isomorphism uses `stageHom E J` and the collapse map associated
to `J`.  It therefore depends on the finite-branch witness `J`; no one
computable seed map is present on both branches.  This is precisely how the
construction avoids the uniform-seed-map firewall.

The bidirectional bridge keeps this feature.  For a countable group `C` with
a generating sequence `(c_i)`, it forms

\[
 B_2(C)=\langle C*F(a,b),t\mid
 t a_i t^{-1}=c_i b_i\ (i\in\mathbb Z)\rangle.
\]

The base embeds by Britton normal form, so a last-cut isomorphism `E -> S_e`
on `FIN` yields an existential embedding

\[
 E\hookrightarrow S_e\hookrightarrow B_2(S_e).
\]

On `INF`, `S_e=1` and the repository gives a direct characteristic-filtration
argument that `B_2(1)` is residually finite.  This is enough for the
two-generator **recursive-presentation** result.  It is not a finite
presentation compiler.

No defect occurs in this part of the truth table.

## 2. The exact input expected by the Aanderaa rope

The claimed finite compiler uses the Rotman--Turing detector.  Its essential
interface is a finitely presented group `G_nb(T)` containing:

* a free alphabet subgroup `F(A)=<s_j>`;
* elements `k_0,t_0`; and
* the equivalence

\[
 [k_0,w^{-1}t_0w]=1
 \quad\Longleftrightarrow\quad
 w\in R
 \qquad(w\in F(A)),                                      \tag{2.1}
\]

where `R` is the recursively enumerated relator set.

The three rope layers are then displayed as

```text
G4 = G_nb(T) * Gamma

G5 = <G4, tau_j |
      [tau_j,s_k] = [tau_j,s'_k] = 1,
      tau_j^-1 k0 tau_j = k0 s'_j^-1>

G6 = <G5,d |
      [d,k0] = 1,
      d^-1 (s_j tau_j) d = s_j>

G7 = <G6,sigma |
      [sigma,k0] = [sigma,s_j] = 1,
      sigma^-1 t0 sigma = t0 d>.
```

The load-bearing identities are induced from the values on the letters
`s_j`.  For example, if `w=s_{j_1}^{eps_1}...s_{j_n}^{eps_n}`, then the
relations determine the corresponding transported word by applying the same
substitution to each letter.  This is not optional: evaluation from a free
group is the unique homomorphism extending the generator assignment.

The formal file `Higman/ExplicitFreeEdge.lean` accurately reflects only this
interface.  Its `Data` structure requires proofs that the source and target
evaluation homomorphisms from a free group are injective.  Its `dData` and
`sigmaData` constructors take those injectivity proofs as hypotheses.  It
does not prove the concrete Aanderaa tuples free and does not prove MF
permanence for their HNN extensions.

The repository claim `aanderaa-rope-layers-are-mf-safe` itself says:

* the `tau` layer is the asymmetric amalgam
  `G4 *_U (U semidirect F_J)` and its shear does not extend to `G4`;
* the `d` and `sigma` layers are HNN extensions over displayed free
  subgroups; and
* **no layer has been closed**.

Therefore “all edge groups are free” is not a proof of the positive MF
branch.

## 3. The interface actually supplied by the modular-machine engine

The formal modular-machine development has a different detector.

Its base contains the normal closure `T` of `t`, and proves that

\[
 T\cong F(\{z_{(alpha,beta)}:(alpha,beta)\in\mathbb Z^2\}),
\]

where

\[
 z_{(alpha,beta)}
 =t(alpha,beta)
 =x^{-alpha}y^{-beta}t x^{alpha}y^{beta}.                 \tag{3.1}
\]

The freeness of this family is not decoration.  It is used to prove that a
basis element lies in the subgroup generated by a set of configurations if
and only if its index belongs to that set.

After the modular-machine HNN tower and one final central stable letter `k`,
the proved detector is

\[
 [k,t(alpha,beta)]=1
 \quad\Longleftrightarrow\quad
 (alpha,beta)\text{ halts}.                               \tag{3.2}
\]

To enumerate a word relator set, a computable reduction may assign to each
whole word `w` a configuration `c(w)=(alpha_w,beta_w)` satisfying

\[
 w\in R\quad\Longleftrightarrow\quad c(w)\text{ halts}.    \tag{3.3}
\]

Combining (3.2) and (3.3) tests one word at a time through
`t(c(w))`.  It does **not** provide a homomorphism

\[
 F(A)\longrightarrow T,
 \qquad w\longmapsto t(c(w)).                              \tag{3.4}
\]

The Aanderaa rope needs exactly the homomorphic, letterwise behavior missing
from (3.4).

## 4. Free-basis singleton coding cannot be homomorphic

Here is the precise obstruction.

### Lemma 4.1 -- singleton-basis length obstruction

Let `A` be a nonempty alphabet, let `I` be any set, and let `F(I)` be the free
group on basis `(z_i)_(i in I)`.  There are no maps

\[
 c:A^+\to I,
 \qquad
 rho:F(A)\to F(I)
\]

such that

\[
 rho(w)=z_{c(w)}                                             \tag{4.1}
\]

for every nonempty positive word `w`.

### Proof

Choose `a in A`.  Equation (4.1) gives

\[
 rho(a)=z_{c(a)},\qquad rho(aa)=z_{c(aa)}.
\]

But homomorphicity gives

\[
 rho(aa)=rho(a)^2=z_{c(a)}^2.
\]

The reduced free-group word `z_{c(a)}^2` has length two, whereas the basis
letter `z_{c(aa)}` has length one.  They cannot be equal.  Contradiction.
\(\square\)

The same proof works if the coding is allowed to choose an inverse basis
letter for every word: the square of one signed basis letter still has
reduced length two.

### Corollary 4.2 -- no direct modular-to-Aanderaa substitution

No assignment that represents every input word `w` by the single modular
configuration basis element `t(c(w))` can be the evaluation homomorphism of a
tuple of letter images.  Hence the identities in the `tau`, `d`, and `sigma`
layers cannot be obtained by replacing the Rotman word `w` with
`t(c(w))` while leaving the Aanderaa presentation unchanged.

This conclusion uses only free reduction and the formally asserted
free-basis shape of `T`.

## 5. Why adding decoder relations is not a local patch

One might add finite relations intended to force

\[
 t(c(uv))=t(c(u))t(c(v)).                                   \tag{5.1}
\]

But (5.1), already with `u=v=a`, identifies a free-basis letter with the
square of another basis letter.  It therefore destroys the free-basis model
used in the proof of the modular detector.

After such relations are imposed, none of the following follows from the
existing modular-machine proof:

1. distinct configurations remain distinct;
2. membership of `t(alpha,beta)` in the halting subgroup is equivalent to
   membership of `(alpha,beta)` in the halting set;
3. the final centralizer equality (3.2) retains its reverse implication;
4. the original modular-machine group embeds in the decoder quotient; or
5. the decoder quotient is MF on `INF`.

Thus a decoder is not a harmless syntactic wrapper.  It would be the missing
finite compiler and would require new normal-form and positive-MF proofs.

## 6. The complementary failure of the Rotman--Turing candidate

The Rotman--Turing group has the correct interface (2.1), so Lemma 4.1 does
not attack it.  Instead its analytic side remains open.

The repository claim `boone-group-is-mf` reduces MF of that group to
`boone-base-has-corona-inner-instruction-automorphisms`.  The latter stops at
a concrete unresolved corona conjugacy problem for a nonamenable amalgam of
`BS(1,2)` factors.  In addition, `aanderaa-rope-layers-are-mf-safe` leaves the
`tau`, `d`, and `sigma` layers open.

Consequently the two available engines have complementary capabilities:

| engine | exact detector needed by rope | zero-input positive MF proof |
|---|---:|---:|
| Rotman--Turing Boone | yes | no |
| formal modular-machine Boone | no | no; current route imports literature |

There is no established engine satisfying both columns.

## 7. The literature dependency is explicit, not merely suspected

The route `modular-machine-boone-group-is-mf-proof` declares that its proof
uses:

* an amenable-amalgam theorem;
* `regular-mf-central-hnn-closure`; and
* an inner-envelope reduction.

The file `regular-mf-central-hnn-closure-proof` begins by applying Shulman's
central-HNN MF theorem.  Therefore its empty `requires` metadata cannot be
read as a first-principles proof.  Under the instruction “zero literature
inputs,” this route is unavailable even before the interface obstruction of
Section 4 is considered.

## 8. Sharper candidate-class firewall

The preceding argument rules out every finite-packing proposal having all
three of these features:

1. **singleton configuration packing:** each recursively enumerated input
   word `w` is represented by one element of a free basis, `z_{c(w)}`;
2. **letterwise rope transport:** the finite compiler transports arbitrary
   words by the homomorphism induced from finitely many input-letter images;
3. **unchanged detector normal form:** the proof of the detector continues to
   use freeness of the configuration basis.

Features 1 and 2 contradict Lemma 4.1.  Dropping feature 3 means the existing
detector theorem no longer applies.  Hence this natural candidate class
cannot close the finite-presentation theorem by rewiring existing modules.

This firewall does **not** rule out all branch-sensitive finite compilers.  A
successful construction could instead:

* use a detector intrinsically compatible with concatenation;
* replace the Aanderaa rope by a whole-word packing mechanism that never asks
  for a homomorphic code; or
* give a new, direct MF approximation of the Rotman--Turing engine and all
  three rope layers.

Each option requires a genuinely new theorem.

## 9. Minimal remaining theorem

The exact switch and bidirectional bridge reduce the desired result to the
following missing object.

### Branch-sensitive MF finite packer

For every two-generator recursive presentation `Gamma`, uniformly output a
finite presentation `Pack(Gamma)` such that:

1. if `Gamma` is the positive scaffold `B_2(1)`, then `Pack(Gamma)` is MF by
   a first-principles matrix-corona construction;
2. there exists an embedding `Gamma -> Pack(Gamma)` for the concrete
   recursive presentations arising on `FIN`; and
3. the embedding is obtained from the last-cut witness and is not a
   computable designated homomorphism on all indices.

The current Aanderaa claim would be one realization only after its engine and
three MF layer lemmas are proved.  The modular-machine formalization does not
supply it through a direct substitution.

## 10. Consequence for the headline theorem

The arbitrary-seed statement

\[
 \forall\text{ finitely presented non-MF }E,
 \quad e\mapsto R(E,e)
\]

remains conceptually valid **conditional on** a branch-sensitive MF finite
packer.  The seed is used only on the `FIN` branch after choosing a last cut,
so no special algebraic property of the literal `E` is needed there.

What is not valid is to cite
`mf-safe-compiler-via-aanderaa-boone-tower` as that packer.  Its Turing-engine
MF hypothesis and rope-layer MF hypotheses are open, while the modular-engine
replacement is blocked by Lemma 4.1 and, independently, by forbidden
literature dependencies.

The fully unconditional `Pi^0_2`-completeness proof therefore remains open at
one sharply isolated point: a first-principles branch-sensitive MF finite
packer.
