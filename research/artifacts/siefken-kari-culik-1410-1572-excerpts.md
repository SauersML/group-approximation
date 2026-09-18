# Siefken, "A Minimal Subsystem of the Kari-Culik Tilings", arXiv:1410.1572 (ETDS 2016)

Source: arXiv PDF of 1410.1572 (version dated October 11, 2018 on its first page),
fetched 2026-09-18, text extracted with pypdf. The excerpts below are verbatim
from that extraction. The extraction garbles some typography: subscripts are run
inline, `KC Qc` stands for `KC_{Q^c}`, and ligatures such as "ﬁ" are kept. No
wording has been changed.

## Abstract

> The Kari-Culik tilings are formed from a set of 13 Wang tiles that tile the plane
> only aperiodically.

## Section 1, main theorems

> Let KC be the subset of the Kari-Culik tilings whose rows form (generalized)
> Sturmian sequences.
> Theorem A. The Z2 action by translation on KC is conjugate to a skew product acting
> on the space [1/3, 2]× lim←−R/(6nZ).
> Theorem B. The Z2 action by translation on KC is minimal.

## Section 2, definitions

> Deﬁnition (Rotation Sequence) . A rotation sequence corresponding to the parameters
> α,t∈ R is the sequence x = R⌊·⌋(α,t ) or x′ = R⌈·⌉(α,t ) where
> (x)i =⌊iα +t⌋−⌊ (i− 1)α +t⌋

> Deﬁnition (Sturmian Sequence). A sequence x is a Sturmian sequence if x = R⌊·⌋(α,t )
> orx = R⌈·⌉(α,t ) for some α,t∈ R. [...] S denotes
> the set of all Sturmian sequences and ¯S denotes its closure under d. ¯S is called the set of
> generalized Sturmian sequences.

> Deﬁnition. Φ : KZ2 →{ 0, 1, 2}Z2 is projection onto the bottom labels of tiles in K followed
> by mapping the symbol 0′ to 0.
> Deﬁnition. The set KC ={x : x is a Kari-Culik tiling and Φ(x) consists of generalized
> Sturmian rows}. KC Qc ={x∈KC : (Φ(x))i has an irrational angle for all i}.

## Section 3, multiplier property and angles

> Deﬁnition (Multiplier Property). A Kari-Culik tile with bottom, left, top, and right labels
> of a,b,c,d satisﬁes the relationship
> λa +b =c +d (1)

> Notice that for any Kari-Culik tiling, the rows fall into two distinct categories: those where
> every tile has left-right edge labels in{ 0/3, 1/3, 2/3} and those where every tile has left-right edge
> labels in{0,−1}. We will call these rows as well as the tiles in each row type 1/3 and type
> 2 respectively.

> Deﬁnition. Forx∈ [1/3, 2], deﬁne
> λx = 2 if x∈ [1/3, 1), 1/3 if x∈ [1, 2] and f(x) =λxx = 2x if x∈ [1/3, 1), x/3 if x∈ [1, 2] .
> Corollary 5. Fix a Kari-Culik conﬁguration x and let ri = Φ((x)i). Then,
> α(ri+1) =f(α(ri))
> providedα(ri)⁄= 1.

> Proof. Sinceα(ri+1) =λα(ri) for someλ∈{ 1
> 3, 2}, the constraint that bothα(ri+1),α (ri)∈
> [1/3, 2] uniquely determines λ when α(ri)⁄= 1.

> Proposition 7 (Liousse [5]). The mapf is conjugate to an irrational rotation bylog 2/ log 6.

## Section 3, the Basic Construction

> Deﬁnition (BC Property). A pair of vectors (⃗ α,⃗t)∈ [1/3, 2]Z× [0, 1]Z satisﬁes the BC
> property (Basic Construction property) if
> λi = αi/αi+1 ∈{ 1/3, 2}
> and
> 2ti =ti+1 mod 1 if λi = 2
> ti = 3ti+1 mod 1 if λi = 1/3
> for all i.
> Given a pair of vectors (⃗ α,⃗t) satisfying the BC property, we can construct a point y∈KC
> via the following procedure. The tile at position m,n in y has bottom, left, top, and right
> edges given by
> bottom = ⌊nαm +tm⌋−⌊ (n− 1)αm +tm⌋
> [...]
> top = ⌊nαm+1 +tm+1⌋−⌊ (n− 1)αm+1 +tm+1⌋
> [...]
> where λ = αm/αm+1. Further, if either the bottom or the top label is computed to be 0,
> then 0 is replaced with 0 ′ if αm−1∈ [1/3, 1/2] (respectively αm∈ [1/3, 1/2]). We can also
> do the same construction using ⌈·⌉ instead of⌊·⌋. We call a tiling constructed in this way
> a Basic Construction with parameters (⃗ α,⃗t).
> Proposition 8 (Robinson [8]). If (⃗ α,⃗t) satisﬁes the BC property, then the resulting Basic
> Construction using either ⌊·⌋ or⌈·⌉ is an element of KC .

(Reading note. As printed, `λi = αi/αi+1` together with `2ti = ti+1` when
`λi = 2` is internally inconsistent: a row of angle `α` whose next row has angle
`α/2` cannot have next phase `2t`. The only consistent reading, forced by the
bottom and top formulas and by Corollary 5, is `αi+1 = λ αi` with
`λ ∈ {2, 1/3}`: if `αi+1 = 2αi` then `ti+1 = 2ti mod 1`, and if `αi+1 = αi/3`
then `ti = 3ti+1 mod 1`. This is the reading used downstream.)

## Section 3, injectivity of Φ

> Theorem 10. Φ|KCQc is one-to-one and Φ is at most sixteen-to-one.
> Proof. Fix x∈ KC and consider a row r of x. [...]
> Notice that by the multiplier property (Equation (1)), r is uniquely determined by (rt,rb)
> and a single left label of one of the tiles in r.
