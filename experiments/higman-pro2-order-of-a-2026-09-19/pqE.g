# 2-quotients of E = G'' x| C4 = < a, s | s^4, (a^s)^a = (a^s)^3, [a, a^(s^2)]^2 >, where
# G'' = H4(3)/<<[a,c]^2,[b,d]^2>> is the normal closure of a (b = a^s, c = a^(s^2), d = a^(s^3)).
F := FreeGroup("a","s"); a := F.1; s := F.2;
GE := F / [ s^4, (a^s)^a / (a^s)^3, Comm(a, a^(s^2))^2 ];
t0 := Runtime();
for cl in [1..MAXCL] do
  hom := EpimorphismPGroup(GE, 2, cl); P := Image(hom);
  Print("E class ", cl, " |P| = 2^", LogInt(Size(P),2), " ord(a) ", Order(Image(hom, GE.1)),
        " ord(s) ", Order(Image(hom, GE.2)), " s ", Int((Runtime()-t0)/1000), "\n");
  if PClassPGroup(P) < cl then Print("E finite\n"); break; fi;
od;
QUIT;
