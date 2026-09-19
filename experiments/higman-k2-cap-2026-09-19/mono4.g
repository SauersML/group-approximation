# mono4.g: the monolithic loop of mono.g on a saved model file (pc group MQ, images MEXP of a,b,c,d),
# saving the current quotient to OUT after every step, so that it can be resumed within 1200 s budgets.
# usage: gap -q -o 2g -c 'FILE:="k2-big-pc.g";; OUT:="k2-pc.g";;' mono4.g   (then FILE:="k2-pc.g" to resume)
Read(FILE);
Q := MQ;; gi := List(MEXP, e -> PcElementByExponents(Pcgs(Q), e));; one := One(GF(2));;
save := function()
  PrintTo(OUT, "# 2-quotient of H4(3)/<<[a,c]^2, b^4>> of order 2^", LogInt(Size(Q),2), " from mono4.g\n");
  AppendTo(OUT, GapInputPcGroup(Q, "MQ"), "\n");
  AppendTo(OUT, "MEXP := ", List(gi, g -> ExponentsOfPcElement(Pcgs(Q), g)), ";\n");
end;;
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
  Print("|Q| = 2^", LogInt(Size(Q),2), " soc rank ", k, " ords ", List(gi, Order), " s ",
        Int((Runtime()-t0)/1000), "\n");
  save();
until k <= 1;
Print("monolithic: ", k = 1, "\n");
QUIT;
