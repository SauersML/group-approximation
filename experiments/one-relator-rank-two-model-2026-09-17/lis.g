# Finite quotients of G_2 = <a,t | a2^-1 u a2 u^-2>, u=[a,a^t], a2=a^(t^2),
# from all subgroups of index <= maxn.  For each image: does u survive, does
# b1 = [a0, a1 a0 a1^-1] survive, and is the square root v = a2 u a2^-1 of u
# separated from pi(F_-) = <pi(a0), pi(a1)> ?   (Prediction: never separated.)
F := FreeGroup("a","t");; a := F.1;; t := F.2;;
a1 := a^t;; a2 := a^(t^2);; u := Comm(a,a1);;
rel := a2^-1*u*a2*u^-2;;
G := F/[rel];;
b1 := Comm(a, a1*a*a1^-1);;
v := a2*u*a2^-1;;
maxn := 8;;
L := LowIndexSubgroupsFpGroup(G, maxn);;
stats := rec(subgroups:=0, usurv:=0, bothsurv:=0, vsep:=0);;
seen := [];;
for H in L do
  hom := FactorCosetAction(G,H);
  img := function(w) return Image(hom, MappedWord(w, [a,t], GeneratorsOfGroup(G))); end;
  stats.subgroups := stats.subgroups+1;
  if img(u) <> () then
    stats.usurv := stats.usurv+1;
    if img(b1) <> () then stats.bothsurv := stats.bothsurv+1; fi;
    if not img(v) in Group(img(a), img(a1)) then stats.vsep := stats.vsep+1; fi;
    Q := Image(hom);
    key := [Index(G,H), Size(Q), Order(img(u)), img(b1)<>(), img(v) in Group(img(a),img(a1))];
    if not key in seen then
      Add(seen, key);
      Print("index ", key[1], " |Q|=", key[2], " ord(u)=", key[3],
            " b1 survives=", key[4], " v in pi(F_-)=", key[5], "\n");
    fi;
  fi;
od;
Print(stats, "\n");
QUIT;
