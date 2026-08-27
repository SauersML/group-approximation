# Exact GAP probe for finite quotients of the two shortest Jacobson cells.
# Run on MSI; this is not part of the Cairn proof graph.

x12 := (2,3)(6,7);
x23 := (4,6)(5,7);
x31 := (1,5)(3,7);
x13 := (4,5)(6,7);
x32 := (2,6)(3,7);
x21 := (1,3)(5,7);
b23 := (2,4)(3,5);
rho := (1,2,4)(3,6,5);

ShiftPerm := function(p, n)
  local l, i;
  l := [1..14];
  for i in [1..7] do
    l[n+i] := n + i^p;
  od;
  return PermList(l);
end;

HeadPerm := function(p)
  local l, i;
  l := [1..14];
  for i in [1..7] do l[i] := i^p; od;
  return PermList(l);
end;

TailPerm := p -> ShiftPerm(p, 7);

F := Group(HeadPerm(x12), HeadPerm(x23), HeadPerm(x31),
           TailPerm(x12), TailPerm(x23), TailPerm(x31));
Print("Size F = ", Size(F), "\n");

iso := IsomorphismFpGroup(F);
FP := Image(iso);
gensFP := GeneratorsOfGroup(FP);
rels := RelatorsOfFpGroup(FP);
freeFP := FreeGroupOfFpGroup(FP);
freegensFP := GeneratorsOfGroup(freeFP);

W := FreeGroup(Length(gensFP)+1);
wg := GeneratorsOfGroup(W);
freeMap := GroupHomomorphismByImagesNC(freeFP, W, freegensFP,
                                      wg{[1..Length(freegensFP)]});
LiftWord := x -> Image(freeMap, x);
Lift := x -> LiftWord(UnderlyingElement(Image(iso, x)));
hh := wg[Length(wg)];

U := HeadPerm(x12) * TailPerm(x12);
B := HeadPerm(b23) * TailPerm(b23);
RHO := HeadPerm(rho) * TailPerm(rho);
C := HeadPerm(b23);
MARK := HeadPerm(x13);
K1 := HeadPerm(x13);
K2 := HeadPerm(x31);

newrels := List(rels, LiftWord);
Add(newrels, hh^2);
Add(newrels, Comm(hh, Lift(K1)));
Add(newrels, Comm(hh, Lift(K2)));
Add(newrels, (hh*Lift(B))^3);
a := hh*Lift(U);
cell := (Lift(RHO)^2*a*Lift(RHO)^-2) *
        (Lift(RHO)*a*Lift(RHO)^-1) * a * Lift(C)^-1;
Add(newrels, cell);

Q := W / newrels;
Print("fp generators = ", Length(GeneratorsOfGroup(Q)),
      ", relators = ", Length(RelatorsOfFpGroup(Q)), "\n");
JQ := SimplifiedFpGroup(Q);
Print("simplified generators = ", Length(GeneratorsOfGroup(JQ)),
      ", relators = ", Length(RelatorsOfFpGroup(JQ)), "\n");
Print("abelian invariants = ", AbelianInvariants(JQ), "\n");

# Search low-degree permutation quotients before attempting full closure.
qmap := GroupHomomorphismByImagesNC(W, Q, wg, GeneratorsOfGroup(Q));
markQ := Image(qmap, Lift(MARK));
for bound in [14] do
  lis := LowIndexSubgroupsFpGroup(Q, bound);
  Print("low-index <= ", bound, ": ", Length(lis),
        ", indices ", List(lis, sub -> Index(Q,sub)), "\n");
od;
for sub in lis do
  if Index(Q,sub) > 1 then
    Print("testing index ", Index(Q,sub), "\n");
    act := FactorCosetAction(Q, sub);
    Print("  mark trivial? ", IsOne(Image(act,markQ)),
          ", image size ", Size(Image(act)), "\n");
  fi;
od;
QUIT;
