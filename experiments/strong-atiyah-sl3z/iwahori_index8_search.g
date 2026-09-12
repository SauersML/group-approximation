# Does the pro-2 Iwahori I <= SL_3(Z_2) have a torsion-free open subgroup of index 8?
# Every index-8 subgroup contains K_4 = ker(SL_3(Z_2) -> SL_3(Z/16)), so we search I/K_4.
# Torsion-free <=> contains no involution; the involutions of SL_3(Z_2) form two classes,
# diag(1,-1,-1) and [[0,1],[1,0]] (+) (-1) (Diederichsen--Reiner), so the forbidden set is the
# intersection of their SL_3(Z/16)-classes with I/K_4.
# Search: chains I > M1 > M2 > W of index-2 steps; at the last step W = ker(chi) for a
# character chi of M2/Phi(M2) with chi(t) = 1 for every forbidden t in M2.

R := Integers mod 16;;
one := One(R);;
ElMat := function(i, j, a) local m; m := IdentityMat(3, R); m[i][j] := a*one; return m; end;;
Dg := function(a, b, c) return DiagonalMat([a*one, b*one, c*one]); end;;
inv3 := Inverse(3*one);;

G16 := Group([ElMat(1,2,1), ElMat(2,1,1), ElMat(2,3,1), ElMat(3,2,1), ElMat(1,3,1), ElMat(3,1,1)]);;
Print("|SL_3(Z/16)| = ", Size(G16), "  expected ", 168*2^24, "\n");

Igens := [ElMat(1,2,1), ElMat(1,3,1), ElMat(2,3,1), ElMat(2,1,2), ElMat(3,1,2), ElMat(3,2,2),
          Dg(-1,-1,1), Dg(1,-1,-1), DiagonalMat([3*one, inv3, one]), DiagonalMat([one, 3*one, inv3])];;
I16 := Group(Igens);;
Print("|I/K_4| = ", Size(I16), "  expected ", 2^27, "\n");

A := Dg(1,-1,-1);;
B := [[0,1,0],[1,0,0],[0,0,-1]]*one;;
clA := Orbit(G16, A, OnPoints);;
clB := Orbit(G16, B, OnPoints);;
Print("class sizes mod 16: A ", Length(clA), "  B ", Length(clB), "\n");
T := Filtered(Concatenation(clA, clB), t -> t in I16);;
Print("forbidden involution images in I/K_4: ", Length(T), "\n");

iso := IsomorphismPcGroup(I16);;
P := Image(iso);;
TP := List(T, t -> Image(iso, t));;
Print("Frattini rank of P: ", Length(GeneratorsOfGroup(P/FrattiniSubgroup(P))), "\n");
Print("forbidden elements in Phi^3(P): ",
      Number(TP, t -> t in FrattiniSubgroup(FrattiniSubgroup(FrattiniSubgroup(P)))), "\n");

found := fail;;
nM1 := 0;; nM2 := 0;; nSolvable := 0;;
M1s := MaximalSubgroups(P);;
Print("index-2 subgroups of P: ", Length(M1s), "\n");
for M1 in M1s do
  nM1 := nM1 + 1;
  T1 := Filtered(TP, t -> t in M1);
  for M2 in MaximalSubgroups(M1) do
    nM2 := nM2 + 1;
    T2 := Filtered(T1, t -> t in M2);
    F := FrattiniSubgroup(M2);
    if ForAny(T2, t -> t in F) then continue; fi;
    hom := NaturalHomomorphismByNormalSubgroup(M2, F);
    Q := Image(hom);
    pcg := Pcgs(Q);
    rows := List(T2, t -> List(ExponentsOfPcElement(pcg, Image(hom, t)), x -> x*Z(2)));
    if Length(rows) = 0 then
      # no forbidden elements at all: any index-2 subgroup works
      nSolvable := nSolvable + 1;
      found := [M1, M2, "empty"];
      break;
    fi;
    # chi with rows * chi = (1,...,1): SolutionMat(M, v) solves x * M = v, so transpose
    sol := SolutionMat(TransposedMat(rows), List(rows, r -> Z(2)));
    if sol <> fail then
      nSolvable := nSolvable + 1;
      found := [M1, M2, sol];
      break;
    fi;
  od;
  if found <> fail then break; fi;
od;
Print("M1 visited ", nM1, "  M2 visited ", nM2, "\n");
if found = fail then
  Print("RESULT: no torsion-free index-8 subgroup of I exists\n");
else
  M2 := found[2];
  F := FrattiniSubgroup(M2);
  hom := NaturalHomomorphismByNormalSubgroup(M2, F);
  Q := Image(hom); pcg := Pcgs(Q);
  if found[3] = "empty" then
    W := PreImage(hom, Subgroup(Q, pcg{[2..Length(pcg)]}));
  else
    chi := found[3];
    C2 := CyclicGroup(IsPcGroup, 2);
    c := GeneratorsOfGroup(C2)[1];
    imgs := List([1..Length(pcg)], k -> c^IntFFE(chi[k]));
    W := PreImage(hom, Kernel(GroupHomomorphismByImages(Q, C2, AsList(pcg), imgs)));
  fi;
  Print("RESULT: found W of index ", Index(P, W), "; forbidden elements in W: ",
        Number(TP, t -> t in W), "\n");
  Wm := PreImage(iso, W);
  Print("W generators mod 16:\n", List(SmallGeneratingSet(Wm), g -> List(g, r -> List(r, Int))), "\n");
fi;
QUIT;
