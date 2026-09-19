# red2.g: reduce a pq-exported class-CL 2-quotient P (file PQF, pq option 25) to a small quotient Q = P/N
# in which z = a^(ord(a)/2) survives, by linear algebra only; then the monolithic loop of mono.g on Q.
# usage: gap -q -o 2g -c 'PQF:="R3.gap";; S:=66;; NCAND:=3;; NAME:="k2";;' red2.g
#   S = log2 |P_(I-1)|: A = gamma_I(P) is spanned by the pc generators S+1..n (pq orders them by weight).
#   Take 2I > CL, so A is abelian (checked).
# V = A/A^2 = F_2^m / R (exponent vectors mod the span R of the exponent vectors of the squares) is an
# F_2[P]-module.  For a functional f on V with f(z) = 1, W = the P-invariant span of f in V^*, and
# N = {v in A : w(v) = 0 for w in W} is normal in P, contains A^2 and avoids z.  Q = P/N is written as a
# new pc presentation on the S top generators and a basis y_1..y_d of A/N = W^* (d = dim W); its
# relations are read off the pcgs of the genuine quotient P/N, so it is consistent when P is (pq checks P);
# CHECKCONF := true also runs IsConfluent (slow for 480 generators).
Read(PQF);
P := F;; pcgs := Pcgs(P);; n := Length(pcgs);; one := One(GF(2));;
gi := List([1..4], i -> MapImages[i]);;
Fr := FreeGroup("a","b","c","d");;
rels := [ Fr.2^Fr.1/Fr.2^3, Fr.3^Fr.2/Fr.3^3, Fr.4^Fr.3/Fr.4^3, Fr.1^Fr.4/Fr.1^3, Comm(Fr.1,Fr.3)^2 ];;
Print(NAME, " |P| = 2^", n, " ords ", List(gi, Order), " relators ",
  List(rels, r -> IsOne(MappedWord(r, GeneratorsOfGroup(Fr), gi))), "\n");
z := gi[1]^(Order(gi[1])/2);;
Aidx := [S+1..n];; m := Length(Aidx);; top := [1..S];;
ex := g -> ExponentsOfPcElement(pcgs, g);;
Print(NAME, " A abelian: ", ForAll(Aidx, i -> ForAll(Filtered(Aidx, j -> j > i), j -> IsOne(Comm(pcgs[i], pcgs[j])))),
  " z in A: ", IsZero(ex(z){top}), " t ", Runtime(), "\n");
Rrows := ImmutableMatrix(GF(2), List(Aidx, t -> ex(pcgs[t]^2){Aidx} * one));;
vz := ex(z){Aidx} * one;;
Rperp := NullspaceMat(TransposedMat(Rrows));;
Print(NAME, " m = ", m, " dim V = ", Length(Rperp), " t ", Runtime(), "\n");
Ms := [];;   # compressed GF(2) matrices: 476 dense 745x745 FFE lists exceed 2GB
for i in top do Ms[i] := ImmutableMatrix(GF(2), List(Aidx, t -> ex(pcgs[t]^pcgs[i]){Aidx} * one)); od;;
Print(NAME, " action matrices t ", Runtime(), "\n");
span := function(f)
  local B, todo, w, u, j;
  B := MutableBasis(GF(2), [f]); todo := [f];
  while todo <> [] do
    w := Remove(todo);
    for j in [1..4] do
      u := Ms[j] * w;
      if not IsContainedInSpan(B, u) then CloseMutableBasis(B, u); Add(todo, u); fi;
    od;
  od;
  return BasisVectors(ImmutableBasis(B));
end;;
cands := Filtered(Rperp, f -> not IsZero(f * vz));;
cands := cands{[1..Minimum(NCAND, Length(cands))]};;
best := fail;;
for f in cands do
  W := span(f); Print(NAME, " candidate dim W = ", Length(W), " t ", Runtime(), "\n");
  if best = fail or Length(W) < Length(best) then best := W; fi;
od;
Wm := best;; d := Length(Wm);; WmT := TransposedMat(Wm);;
coords := u -> Wm * u;;   # coordinates of u in F_2^m in A/N = F_2^d
dual := List([1..d], s -> SolutionMat(WmT, List([1..d], function(r) if r = s then return one; else return 0*one; fi; end)));;
Print(NAME, " z coords nonzero: ", not IsZero(coords(vz)), "\n");
fg := GeneratorsOfGroup(FreeGroup(S + d));;
wd := function(e)   # e = full exponent vector in P of an element: word in the new generators
  local c, w, i;
  c := coords(e{Aidx} * one); w := One(fg[1]);
  for i in top do if e[i] = 1 then w := w * fg[i]; fi; od;
  for i in [1..d] do if not IsZero(c[i]) then w := w * fg[S+i]; fi; od;
  return w;
end;;
coll := SingleCollector(fg, List([1..S+d], i -> 2));;
Print(NAME, " building collector t ", Runtime(), "\n");
for i in top do
  if i mod 50 = 0 then Print(NAME, " row ", i, " t ", Runtime(), "\n"); fi;
  SetPower(coll, i, wd(ex(pcgs[i]^2)));
  for j in [i+1..S] do SetConjugate(coll, j, i, wd(ex(pcgs[j]^pcgs[i]))); od;
  for s in [1..d] do
    c := coords(dual[s] * Ms[i]);
    SetConjugate(coll, S+s, i, Product(Filtered([1..d], r -> not IsZero(c[r])), r -> fg[S+r], One(fg[1])));
  od;
od;
UpdatePolycyclicCollector(coll);;
Print(NAME, " |Q| = 2^", S+d, " collector built t ", Runtime(), "\n");
if CHECKCONF then Print(NAME, " confluent: ", IsConfluent(coll), " t ", Runtime(), "\n"); fi;
Q := GroupByRwsNC(coll);; gi := Pcgs(Q){[1..4]};;
Print(NAME, " Q ords ", List(gi, Order), " relators ",
  List(rels, r -> IsOne(MappedWord(r, GeneratorsOfGroup(Fr), gi))), " generated ", Size(Group(gi)) = Size(Q), "\n");
PrintTo(Concatenation(NAME, "-big-pc.g"), "# 2-quotient ", NAME, " = P/N of order 2^", S+d, " (before the monolithic loop)\n");
AppendTo(Concatenation(NAME, "-big-pc.g"), GapInputPcGroup(Q, "MQ"), "\n");
AppendTo(Concatenation(NAME, "-big-pc.g"), "MEXP := ", List(gi, g -> ExponentsOfPcElement(Pcgs(Q), g)), ";\n");
Print(NAME, " saved big model t ", Runtime(), "\n");
t0 := Runtime();;
repeat
  z := gi[1]^(Order(gi[1])/2);
  O := Omega(Center(Q), 2, 1); B := Pcgs(O); k := Length(B);
  if k > 1 then
    v := ExponentsOfPcElement(B, z) * one;
    compl := BaseSteinitzVectors(IdentityMat(k, GF(2)), [v]).factorspace;
    K := Subgroup(Q, List(compl, u -> Product([1..k], i -> B[i]^IntFFE(u[i]))));
    nh := NaturalHomomorphismByNormalSubgroup(Q, K);
    Q := Image(nh); gi := List(gi, g -> Image(nh, g));
  fi;
  Print(NAME, " |Q| = 2^", LogInt(Size(Q),2), " soc rank ", k, " ords ", List(gi, Order), " s ",
        Int((Runtime()-t0)/1000), "\n");
until k <= 1;
PrintTo(Concatenation(NAME, "-pc.g"), "# monolithic 2-quotient model ", NAME, " of order 2^", LogInt(Size(Q),2), "\n");
AppendTo(Concatenation(NAME, "-pc.g"), GapInputPcGroup(Q, "MQ"), "\n");
AppendTo(Concatenation(NAME, "-pc.g"), "MEXP := ", List(gi, g -> ExponentsOfPcElement(Pcgs(Q), g)), ";\n");
QUIT;
