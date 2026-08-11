# Verify the fixed q=0 mod-two relation over rational projective lines.
# Reduction gives the same identity on every odd projective chart.

if LoadPackage("hap") = fail then
    Error("the HAP package is required");
fi;

Q0RelationResolution := ResolutionArithmeticGroup("SL(3,Z)", 3);
Q0RelationPoints := [
    [1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0],
    [0, 0, 0, 1, 1, 1],
    [1, 0, 1, 0, 0, 1],
    fail,
    fail,
    fail,
    [1, 2, 1, 4, 2, 1]
];
Q0RelationSupport := [
    [10, 8], [11, 1], [11, 8], [12, 8]
];

Q0RelationCanonicalLine := function(vector)
    local position, scale;
    position := PositionProperty(vector, entry -> entry <> 0);
    if position = fail then
        Error("zero vector does not define a projective line");
    fi;
    scale := vector[position];
    return List(vector, entry -> entry / scale);
end;

Q0RelationToggle := function(list, value)
    local position;
    position := Position(list, value);
    if position = fail then
        Add(list, value);
    else
        Remove(list, position);
    fi;
end;

Q0RelationBoundary := function(total_degree, support)
    local output, source, point, term, image;
    output := [];
    for source in support do
        point := Q0RelationPoints[source[2] + 1];
        for term in Q0RelationResolution!.boundary(
                total_degree, source[1] + 1) do
            image := Q0RelationCanonicalLine(
                point * Q0RelationResolution!.elts[term[2]]);
            Q0RelationToggle(
                output, [AbsoluteValue(term[1]) - 1, image]);
        od;
    od;
    return Set(output);
end;

for point in [Q0RelationPoints[1], Q0RelationPoints[2], Q0RelationPoints[9]] do
    if Q0RelationBoundary(2, [[0, Position(Q0RelationPoints, point) - 1]])
            <> [] then
        Error("a claimed singleton is not a rational mod-two cycle");
    fi;
od;

Q0RelationResidual := Q0RelationBoundary(3, Q0RelationSupport);
Q0RelationExpected := Set([
    [0, Q0RelationPoints[2]],
    [0, Q0RelationPoints[9]]
]);
if Q0RelationResidual <> Q0RelationExpected then
    Error("the rational four-term relation has the wrong boundary");
fi;

Print("support=", Length(Q0RelationSupport),
      " residual=", Length(Q0RelationResidual),
      " exact_rational=true\n");
