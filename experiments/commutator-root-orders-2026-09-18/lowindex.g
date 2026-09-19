if not IsBound(KK) then KK := 2; AL := 1; BE := 1; OUT := "perms.txt"; fi;
F := FreeGroup("y","t");; y := F.1;; t := F.2;;
yi := i -> t^-i*y*t^i;;
comm := function(g,h) return g^-1*h^-1*g*h; end;;
G := F / [ yi(1)^-KK * comm(yi(0)^AL, yi(2)^BE) ];;
L := LowIndexSubgroupsFpGroup(G, 9);;
Print(Length(L), "\n");
PrintTo(OUT, "");
for H in L do
  hom := FactorCosetAction(G, H);
  a := Image(hom, G.1); b := Image(hom, G.2);
  if a <> () then
    AppendTo(OUT, Index(G,H), " [", JoinStringsWithSeparator(List(ListPerm(a, Index(G,H)),String),","), "] [", JoinStringsWithSeparator(List(ListPerm(b, Index(G,H)),String),","), "] ", Size(Image(hom)), "\n");
  fi;
od;
QUIT;
