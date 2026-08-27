# Certify the universal mod-two H2 class hit by projective augmentation.

if LoadPackage("hap") = fail then
    Error("the HAP package is required");
fi;

TrivialH2Resolution := ResolutionArithmeticGroup("SL(3,Z)", 3);;
TrivialH2Field := GF(2);;

TrivialH2Boundary := function(degree)
    local sourceRank, targetRank, result, source, term, target;
    sourceRank := TrivialH2Resolution!.dimension(degree);
    targetRank := TrivialH2Resolution!.dimension(degree - 1);
    result := NullMat(sourceRank, targetRank, TrivialH2Field);
    for source in [1..sourceRank] do
        for term in TrivialH2Resolution!.boundary(degree, source) do
            target := AbsoluteValue(term[1]);
            result[source][target] := result[source][target]
                + One(TrivialH2Field);
        od;
    od;
    return result;
end;

TrivialH2D2 := TrivialH2Boundary(2);;
TrivialH2D3 := TrivialH2Boundary(3);;
if TrivialH2D3 * TrivialH2D2 <> NullMat(20, 4, TrivialH2Field) then
    Error("the augmented matrices do not form a chain complex");
fi;
TrivialH2Rank2 := RankMat(TrivialH2D2);;
TrivialH2Rank3 := RankMat(TrivialH2D3);;
TrivialH2Generator := ListWithIdenticalEntries(10, Zero(TrivialH2Field));;
TrivialH2Generator[1] := One(TrivialH2Field);;
if TrivialH2Generator * TrivialH2D2
        <> ListWithIdenticalEntries(4, Zero(TrivialH2Field)) then
    Error("the first degree-two generator is not a cycle");
fi;
if RankMat(Concatenation(TrivialH2D3, [TrivialH2Generator]))
        <> TrivialH2Rank3 + 1 then
    Error("the first degree-two generator is a boundary");
fi;
TrivialH2Dimension := 10 - TrivialH2Rank2 - TrivialH2Rank3;;
if TrivialH2Dimension <> 2 then
    Error("unexpected trivial-coefficient H2 dimension");
fi;

Print("rank_d2=", TrivialH2Rank2,
      " rank_d3=", TrivialH2Rank3,
      " H2_dimension=", TrivialH2Dimension,
      " first_generator_nonzero=true\n");
