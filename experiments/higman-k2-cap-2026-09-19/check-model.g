# check-model.g (w20, plus a consistency check): independent check of a saved model file NAME-pc.g (pc group MQ, images MEXP of a,b,c,d).
# usage: gap -q -c 'FILE:="m12-pc.g";;' check-model.g
Read(FILE);
MQ := MQ;; pc := Pcgs(MQ);;
gi := List(MEXP, e -> PcElementByExponents(pc, e));;
F := FreeGroup("a","b","c","d");; a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;;
rels := [ b^a/b^3, c^b/c^3, d^c/d^3, a^d/a^3, Comm(a,c)^2 ];;
Print(FILE, " |MQ| = 2^", LogInt(Size(MQ),2), " is 2-group: ", IsPGroup(MQ) and PrimePGroup(MQ) = 2,
  " relators hold: ", ForAll(rels, r -> IsOne(MappedWord(r, GeneratorsOfGroup(F), gi))),
  " generated: ", Size(Group(gi)) = Size(MQ), " ords ", List(gi, Order),
  " socle rank ", Length(Pcgs(Omega(Center(MQ), 2, 1))), "\n");
# consistency of the saved power-conjugate presentation (all overlaps of the collector resolve)
Print(FILE, " presentation consistent: ", IsConfluent(FamilyObj(One(MQ))!.rewritingSystem), "\n");
QUIT;
