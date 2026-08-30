# 2026-08-30 — the finite Weinbaum gate and a perfect-radical calibration

This artifact records two source checks and the deductions promoted from them.
The purpose is not to claim a resolution of the one-relator soficity problem.
It replaces the vague instruction "retain some second-order information" by a
finite marked packet, and checks that the main classical perfect-radical family
is positive rather than a candidate counterexample.

## 1. Primary sources checked

### Linton's kernel theorem

Marco Linton, *Residually rationally solvable one-relator groups*,
arXiv:2407.09272v2, Theorem 3.2, was read at
<https://arxiv.org/html/2407.09272v2>.

In the specialization used here, write a free group as `F = A * B`, let `v`
be cyclically reduced of free-product syllable length at least two and not a
proper power, and put

    G = (A * B)/<<v^m>>,     m >= 1.

If a homomorphism `phi : G -> Q` to a locally indicable group keeps every
proper nonempty subword of the fixed cyclic spelling of `v` nontrivial, then
Linton's theorem decomposes `ker(phi)` as a free product of a free group,
subgroups of `A`, subgroups of `B`, and copies of `Z/mZ`.  Since `A` and `B`
are free in our application, every factor in this decomposition is free or
cyclic.

The same paper's Theorem 1.1 gives the canonical quotient

    pi : G -> H = G/R,       R = G_Q^(omega),

where `H` is residually rationally solvable and `R` is rationally perfect.
The paper's Theorem 3.1 recalls Weinbaum's theorem: every proper nonempty
subword of a one-relator word is nontrivial in the presented group.

### Berlai's Baumslag family

Federico Berlai, *A new family of sofic one-relator groups*,
arXiv:2502.05064v1, Theorem A and its proof, was read at
<https://arxiv.org/html/2502.05064v1>.

With `x^y = y^(-1)xy`, Berlai defines

    G_(r,w)(l,k) = <a,b | (r^l)^(r^w) = r^k>

and proves `G_(a,b^n)(l,k)` sofic for all nonzero `n,l,k`.  The proof writes
the kernel of `a -> 0, b -> 1` as

    K_n = <a_i (i in Z) |
             a_(i+n)^(-1) a_i^l a_(i+n) = a_i^k>,

then splits `K_n` by residue classes modulo `|n|` as a free product of
`|n|` copies of `K_1`.  The group `K_1` is a subgroup of the cyclic-edge HNN
extension of `BS(l,k)`, hence is sofic; free products and amenable extensions
finish the proof.

Fournier-Facio--Willett, *The Local Lifting Property, Property FD, and
stability of approximate representations*, arXiv:2603.18456v2, Proposition
4.26 and Remark 4.27, independently re-run the `l=1` chain and explicitly note
that the same permanence proof yields soficity.  See
<https://arxiv.org/html/2603.18456v2#S4.SS3>.

### The June 2026 partially-positive theorem

Lucy Koch-Hyde, Siobhan O'Connor, and Eamonn Olive, *More Residually Solvable
One-Relator Groups*, arXiv:2606.13933v2, Theorem 1.8, was read at
<https://arxiv.org/pdf/2606.13933>.  A word is *partially positive* when some
generator occurs but its inverse does not.  Their theorem says that every
one-relator group with such a relator is residually solvable.  Their proof in
fact obtains a finite derived term that is free (discussion after Theorem 2.1).
Residual solvability implies residual amenability and hence soficity, so this
recent theorem closes another presentation-visible family not represented by
a canonical Cairn claim before this audit.

## 2. The finite amenable-visibility criterion

Let `S(v)` be the finite set of elements represented by proper nonempty
contiguous subwords of the fixed cyclic spelling of `v`.  If there is one
homomorphism from `G` to an amenable locally indicable group that is nontrivial
on all of `S(v)`, Linton's theorem makes its kernel a free product of free and
finite cyclic groups.  That kernel is sofic, the image is amenable, and the
standard sofic-kernel/amenable-quotient theorem makes `G` sofic.

This asks for much less than residual amenability: only one presentation-sized
finite packet has to survive, rather than every finite subset of `G`.

## 3. A short element in every nontrivial Linton radical

Assume now that `G` is torsion-free and use `m=1`.  The quotient `H=G/R` is
residually rationally solvable, hence locally indicable.  Indeed, if `L <= H`
is nontrivial and finitely generated, choose the first rational-derived layer
of `H` in which `L` is not contained; restriction to that layer's torsion-free
abelian quotient gives a nonzero map from `L` to a finitely generated
torsion-free abelian group, and hence an epimorphism `L -> Z`.

If `H` retained every element of `S(v)`, Linton's kernel theorem would make
`R` free.  But `R` is rationally perfect.  A rationally perfect free group is
trivial, since every nontrivial free group has nonzero torsion-free
abelianization.  Consequently, whenever `R != 1`, some `u in S(v)` satisfies

    u != 1 in G,       pi(u) = 1 in H.

The first assertion is Weinbaum's theorem, and the second says precisely that
`u in R`.  Thus the missing information beyond the canonical Linton quotient
can always be represented by a word strictly shorter than the defining
relator.  In the perfect case `R=R'`, the same `u` lies in the derived core
that the mod-`k` Fox--Magnus map loses.

This marker is effective.  Linton's Corollary 1.4 computes the canonical word
`r`, and the one-relator word problem in `H=F/<<r>>` decides which member of
the finite packet dies.

## 4. Why rational-solvable higher lamps cannot recover the marker

There is a general algebraic fence.  Suppose `R` is rationally perfect,
`pi : G -> H=G/R`, and

    Phi : G -> P,       q : P -> H,       q Phi = pi.

If `ker(q)` is residually rationally solvable, then `Phi(R)=1`.  The image
`L=Phi(R)` is rationally perfect and lies in `ker(q)`.  Functoriality of the
rational derived series gives

    L = L_Q^(j) <= ker(q)_Q^(j)

for every `j`; residual rational solvability forces `L=1`.  If `R` is perfect,
the same proof with the ordinary derived series shows that every lift with
residually solvable kernel kills `R`.

So iterating torsion-free solvable Fox lamps over `H` cannot be the requested
"second-order" model.  A successful model must have a kernel outside this
residual class, or it must cease to be an exact group homomorphism and work
directly with approximate actions.

## 5. The Baumslag--Berlai perfect Linton radical

For `n != 0` and `l notin {0,-1}`, set

    B_(n,l) = G_(a,b^n)(l,l+1).

Let `R=ker(B_(n,l)->Z)`, where `a->0` and `b->1`.  In Berlai's presentation
of `R`, every generator satisfies

    a_i = [a_i^l, a_(i+n)].

Therefore `R` is perfect.  It is nontrivial by the Bass--Serre normal form in
the `BS(l,l+1)` vertex group.  Since `B_(n,l)/R = Z` is residually rationally
solvable and `R` is perfect,

    R = B_(n,l)_Q^(omega).

Thus `R` is exactly the Linton radical, not merely an arbitrary perfect normal
subgroup.  Berlai's residue-class free-product decomposition proves `R` sofic,
and the quotient by `R` is amenable, so `B_(n,l)` is sofic.  Meanwhile every
derived term of `B_(n,l)` contains the nontrivial subgroup `R`, so these groups
are not residually solvable.

This is the essential calibration for the open root: an infinitely generated,
nontrivial perfect Linton radical can be sofic, and its free-shell coupling can
also be sofic, even when ordinary finite and solvable quotient tests lose the
marked generator.  Perfectness itself is therefore not a negative mechanism.

## 6. Remaining exact gate

The finite packet statement suggested by the two theorems is:

> Does every torsion-free one-relator presentation admit one amenable locally
> indicable quotient in which all proper nonempty subwords of the primitive
> relator remain nontrivial?

A positive answer implies every one-relator group is sofic by Section 2.  It
is strictly presentation-local and therefore sharper than asking for residual
amenability of the whole group.  The Baumslag--Berlai theorem shows that a
positive soficity proof need not answer this exact-quotient question: its
finite approximations come instead from amenable-edge HNN chains.
