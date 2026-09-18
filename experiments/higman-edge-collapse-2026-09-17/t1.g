F := FreeGroup("a","b","c","d");; a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;;
rels := [ b^a*b^-2, c^b*c^-2, d^c*d^-2, a^d*a^-2 ];;
G := F/Concatenation(rels,[Comm(a,c)]);;
Print("abelian ac: ", Size(G), "\n");
z := Comm(a,c);;
G2 := F/Concatenation(rels,[Comm(z,a),Comm(z,c)]);;
Print("class2 ac: ", Size(G2), "\n");
QUIT;
