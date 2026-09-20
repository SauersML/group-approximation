# The marked canonical K7 cover has no detector of nilpotency class at most three

Date: 2026-09-20. Lane: ghb7_matching, with root presentation verification and independent stability audit.

**Result.** The canonical face-zero class c0 modulo seven does not inflate from K7's abelianization. Its central generator dies in every quotient of nilpotency class at most three: z belongs to gamma_4(B_c0). Sections 1-6 prove the class-two obstruction; Section 7 proves the stronger class-three theorem supplied by the root lane and independently reviewed here. This eliminates all elementary-abelian-base cup-product/Bockstein detectors. No assertion for class four or higher is made.

We also determine K7^ab exactly as C_7^4 and give a presentation that marks c0 unambiguously. This marking is essential: the existence of other finite central extensions would not determine visibility of this particular class.

## 1. A seven-face presentation and its marking

Let G=G_HB2(7), K=ker(chi:G->C7) with chi(a)=chi(b)=chi(c)=1. Define vertex kernels

    H0=K intersect <a,b>, H1=K intersect <b,c>, H2=K intersect <c,a>.

They have orders 7^2,7^3,7^3; H0 is abelian and H1,H2 have class two and exponent seven. Regard them initially as separate factors. For i in F7 put

    u_i=(a^i b^-i) in H0,
    v_i=(b^i c^-i) in H1,
    w_i=(c^i a^-i) in H2,
    r_i=u_i v_i w_i.

Indices are represented by 0,...,6. The vertex groups have exponent seven, so u_0=v_0=w_0=u_7=v_7=w_7=1. Then

    K = (H0 * H1 * H2) / <<r_1,...,r_6>>.                 (1)

To see the geometric labels, take the triangle with vertices <a,b>,<b,c>,<c,a>, and edge groups <b>,<c>,<a>. K has one orbit of each vertex and edge and seven face orbits, represented by a^i. The a-edge of face a^i is the base a-edge. Its b-edge is the translate by a^i b^-i; its c-edge is the translate by a^i c^-i. The transition between their vertex-one transports is b^i c^-i. The three corner labels are therefore exactly u_i,v_i,w_i. Edge and face stabilizers for K are trivial.

Collapsing a maximal tree in the three-edge quotient leaves one edge letter T. Face zero has boundary T; killing that face sets T=1. The other boundaries then have words r_i, giving (1).

The class c0 is defined to be the pullback of the integer cochain equal to one on face zero and zero on the other faces. Introduce a central generator z, leave each vertex group split, and impose the twisted face equations. The zero face gives T=z; all other faces have trivial central exponent. Substituting T=z makes their equations r_i=z^-1, regardless of the position of T in the oriented boundary. Thus a marked presentation is

    B_c0 = < H0,H1,H2,z | z central, r_i=z^-1 (1<=i<=6) >.    (2)

Reversing the orientation of every face replaces z by z^-1; it does not change any conclusion. This construction is the central extension pulled back from the orbit two-cochain: the vertex extensions are trivial and the only central attaching exponent is on the specified face zero. The pullback is zero on each vertex classifying space, and its splitting there is unique because Hom(Hj,Z)=0. Edges are trivial and all vertical higher cells carry zero cochain. Thus the construction introduces no unspecified torsion class. It is not a choice of an arbitrary nonzero integral class. The established primitive-evaluation theorem guarantees that its central kernel is the indicated infinite Z.

## 2. Algebraic cross-check of the untwisted presentation

Let P denote the right side of (1). On the vertex factors define theta as conjugation by a on H0 and H2, and as Ad(u_1) followed by conjugation by b on H1. In the original vertex groups,

    u_(i+1)=theta(u_i) u_1,
    v_(i+1)=beta(v_i) v_1,       beta=conjugation by b on H1,
    theta(w_i)=w_1^-1 w_(i+1).

Consequently theta(r_i)=r_(i+1) modulo r_1=1: the middle extra factor is v_1^-1 u_1^-1 w_1^-1=1. This holds also at i=6, where r_7=1. Iterating theta on H1 conjugates by u_7 and then by b^7, both trivial; on the other factors its seventh power is likewise trivial. Thus theta is a well-defined automorphism of P of order dividing seven.

In P semidirect_theta <a>, define b=u_1^-1 a and c=w_1 a. Since r_1=1, also c=v_1^-1 b. The pairs a,b; b,c; c,a reconstruct the three original split vertex groups, respectively H0 semidirect <a>, H1 semidirect <b>, H2 semidirect <a>. Hence they satisfy the original G presentation. The maps to and from G are inverse on a,b,c and on all vertex-kernel generators. Therefore P semidirect C7 is G, and its P factor is exactly K. This independently checks that the six face relations have neither lost nor introduced relations.

## 3. Exact vertex weights

The CCKW matrix representation is injective on each original vertex. Each generator is I+N with N^2=0, so its logarithm is N. All computations within an original vertex take place in a unitriangular group of class at most three. Truncated log, exp and BCH are valid over F7, since only denominators 2,3,6,12 are used.

For the ordered pairs (x,y)=(a,b),(b,c),(c,a), let X=log x,Y=log y and put

    U=X-Y, V=[X,Y], W=[U,V].

The standard-library [vertex_weights.py](../../experiments/hrf-wave4-class-two-2026-09-20/vertex_weights.py) checks the following identities with exact 4x4 matrices modulo seven; its output is [vertex_weights.json](../../experiments/hrf-wave4-class-two-2026-09-20/vertex_weights.json).

| kernel | Lie basis | sigma | log(x^i y^-i) |
|---|---|---:|---|
| H0 | U,V | 0 | iU-i^2 V/2 |
| H1 | U,V,W | -1 | iU-i^2 V/2-i^3 W/12 |
| H2 | U,V,W | +1 | iU-i^2 V/2+i^3 W/12 |

For H1 and H2, [U,V]=W and W commutes with U,V. Exactly one of [X,[X,Y]] and [Y,[X,Y]] is zero, so the cubic BCH coefficient is the stated signed multiple of W. For H0 both vanish. The displayed spans are the full kernel Lie algebras: they lie in the kernel of the coordinate-sum character, have dimensions two,three,three, and exponentiating gives respectively all 7^2,7^3,7^3 elements of the known kernels.

Crucially, the degree-three coefficient W lies in the derived algebra of the kernel Hj itself, not merely in the centre of the larger original vertex group. A homomorphism into a class-two group therefore sends that coefficient into the global centre. This is what prevents degree-six cross terms later.

The passage through Lie algebras is functorial for groups of class at most two and exponent seven: the class-two BCH law is X*Y=X+Y+[X,Y]/2, recovered directly from group multiplication and commutators using the inverse of two modulo seven. Thus no extension of a homomorphism from Hj to the original larger vertex is being assumed.

## 4. Exact abelianization of K

Each vertex-kernel abelianization has basis U_j,V_j over F7; its W_j is derived. In the abelianization of (1), the face relation at i becomes

    i(U_0+U_1+U_2) - (i^2/2)(V_0+V_1+V_2)=0.

The values i=1,2 already show that the six face relations impose exactly the two independent equations

    U_0+U_1+U_2=0,  V_0+V_1+V_2=0.

There are no others, so K^ab=C7^4. This determines the integral abelianization, since it is generated by the exponent-seven vertex-kernel abelianizations.

As an independent presentation-level calculation, the script rewrites the G relators by Reidemeister--Schreier with transversal 1,a,...,a^6. After the a^7 Schreier generator is eliminated, there are fourteen generators (the seven b and seven c Schreier generators) and seventy rewritten relators. Their exponent-sum matrix has rank ten over F7, confirming dim H_1(K;F7)=4 without using the seven-face presentation.

## 5. Every class-two quotient kills the marked centre

Let f:B_c0->P be any homomorphism with image of nilpotency class at most two. Relation r_1=z^-1 shows that B_c0 is generated by its three vertex subgroups. Their elements have order dividing seven. A class-two group generated by elements of order seven has exponent seven: commutators have seventh power one, and (xy)^7=x^7 y^7 [y,x]^21=1. We may therefore use the class-two Lie algebra L of the image over F7.

Write Z=log f(z). By Section 3, the logarithm of each corner image has the form

    q_j(i)=i A_j+i^2 B_j+i^3 C_j,

where C_j belongs to [L,L] and is globally central. The class-two BCH formula gives

    log f(r_i) = sum_j q_j(i) + (1/2) sum_(j<k)[q_j(i),q_k(i)].

Since brackets involving any C_j vanish, this is an L-valued polynomial F(i) of degree at most four, with F(0)=0. Every power sum sum_(i in F7) i^d vanishes for 0<=d<=5. Hence

    sum_(i in F7) F(i)=0.

But the marked relations (2) give F(i)=-Z for all six nonzero i, and F(0)=0. Their sum is -6Z=Z in characteristic seven. Therefore Z=0 and f(z)=1.

Applying this to the universal class-two quotient proves z in gamma_3(B_c0). The proof uses no size bound on the target and no finite-quotient search.

## 6. Cup products and Bocksteins cannot realize c0 mod seven

Suppose c0 mod7 inflated from a class in H^2(K^ab;F7), where K^ab=C7^4. Its representative central extension of K^ab by C7 would be a finite group of class at most two. Identifying its pullback with B_c0/<z^7> would give a homomorphism B_c0 to that finite group with z of order seven, contradicting Section 5. Thus c0 mod7 is not in the inflation image.

Every degree-one class of K factors through K^ab. Naturality of cup products and the Bockstein then implies that every linear combination of their degree-two cup products and Bocksteins lies in the same inflation image. The canonical class is outside that span. This excludes the proposed elementary-abelian/class-two detector mechanism.

## 7. Stronger result: class-three quotients also kill z

This extension of the argument was supplied by the root lane. Let P be an image of B_c0 of nilpotency class at most three. As above, it is generated by elements of order seven. It again has exponent seven. One direct collection proof starts with gamma_3(P): its basic triple commutators have seventh power one by the identities for [x^7,y,z]. Then [x,y]^7=1 follows from [x^7,y] and the divisibility of binomial(7,2) by seven. Finally the class-three power-collection formula for a product has commutator exponents that are integer combinations of binomial(7,k), 1<=k<=3, all divisible by seven. Induction over a product of the chosen generators proves exponent seven.

The truncated BCH correspondence for class three, whose denominators are prime to seven, therefore supplies a functorial Lie algebra L over F7. Write U_j,V_j for the images of the vertex basis elements and C_j=sigma_j[U_j,V_j]/12. Thus C_j belongs to gamma_2(L), and the three corner logarithms are

    q_j(i)=iU_j-(i^2/2)V_j+i^3 C_j.

Set

    R(i)=BCH(BCH(q_0(i),q_1(i)),q_2(i)).

Class-three BCH has linear, bilinear, and trilinear Lie terms. Pair brackets involving two C's vanish because [gamma_2,gamma_2]<=gamma_4=0. Triple brackets involving even one C also vanish. Consequently R(i) has degree at most six in i, and its degree-six coefficient consists solely of triple brackets among V_0,V_1,V_2.

Let Z=log f(z). The seven values of this polynomial are R(0)=0 and R(i)=-Z for i!=0. Polynomial interpolation in degree at most six over F7 therefore gives the identity

    R(i)=-Z i^6.                                           (3)

In particular its degree-two coefficient vanishes. Expanding that coefficient gives

    -sum_j V_j/2 + sum_(j<k)[U_j,U_k]/2=0,

so sum_j V_j belongs to gamma_2(L). Its degree-four coefficient, modulo gamma_3(L), is exactly

    (1/8) sum_(j<k)[V_j,V_k].

Indeed brackets [U,C] and all BCH triple brackets already lie in gamma_3, and there are no degree-four linear terms. Thus sum_(j<k)[V_j,V_k] belongs to gamma_3(L).

Working modulo gamma_3 and using V_2=-V_0-V_1 modulo gamma_2, this last sum reduces to [V_0,V_1]. Therefore [V_0,V_1] belongs to gamma_3; substituting again shows that every pair bracket [V_j,V_k] belongs to gamma_3. All triple brackets among the V_j consequently vanish. The degree-six coefficient of R is zero. Comparing it with (3) yields Z=0.

Thus z dies in every class-three image of B_c0. Applying this to the universal such quotient proves

    z in gamma_4(B_c0).

The proof does not extend this claim to class four: brackets discarded here may survive there, and a new calculation would be required.

## 8. Review and validation

The stability-audit lane independently replayed the vertex-weight and Schreier certificate and checked Sections 1-6, returning PASS. It then read the completed Section 7 and separately returned PASS for the class-three extension, including exponent-seven collection, the coefficient-four calculation, and the universal quotient step. The root lane supplied and reviewed the algebraic kernel-presentation verification and class-three extension.

Final canonical compilation derives all five claims and five routes in the expanded wave-four visibility lane as ESTABLISHED or COMPLETE, with no finding naming these nodes. Earlier concurrent missing-artifact errors have been resolved; the final snapshot has zero errors and 46 warnings elsewhere. Exact statuses and counts are in [the validation receipt](hyperbolic-rf-wave4-visibility-validation-2026-09-20.json). Unbounded central survival and flexible stability remain OPEN. No full `cairn check` or Lean formalization is claimed.
