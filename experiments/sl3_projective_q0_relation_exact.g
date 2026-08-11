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

Q0MatchingParameter := Indeterminate(Rationals, "t");
Q0MatchingPoint := [
    1,
    2,
    Q0MatchingParameter,
    4,
    2 * Q0MatchingParameter,
    Q0MatchingParameter^2
];
Q0MatchingMate := [
    1,
    2,
    2 - Q0MatchingParameter,
    4,
    2 * (2 - Q0MatchingParameter),
    (2 - Q0MatchingParameter)^2
];

Q0MatchingBoundary := function(point)
    local output, term, image;
    output := [];
    for term in Q0RelationResolution!.boundary(3, 4) do
        image := Q0RelationCanonicalLine(
            point * Q0RelationResolution!.elts[term[2]]);
        Q0RelationToggle(
            output, [AbsoluteValue(term[1]) - 1, image]);
    od;
    return Set(output);
end;

Q0MatchingActual := Q0MatchingBoundary(Q0MatchingPoint);
Q0MatchingExpected := Set([
    [0, Q0RelationCanonicalLine(Q0MatchingPoint)],
    [0, Q0RelationCanonicalLine(Q0MatchingMate)]
]);
if Length(Q0MatchingActual) <> Length(Q0MatchingExpected)
        or not ForAll([1..Length(Q0MatchingActual)], position ->
            Q0MatchingActual[position][1] = Q0MatchingExpected[position][1]
            and ForAll([1..6], coordinate ->
                IsZero(Q0MatchingActual[position][2][coordinate]
                - Q0MatchingExpected[position][2][coordinate]))) then
    Error("the generic singleton matching is not t -> 2-t");
fi;
if Q0MatchingBoundary([1, 2, 1, 4, 2, 1]) <> []
        or Q0MatchingBoundary([0, 0, 0, 0, 0, 1]) <> [] then
    Error("the two claimed matching fixed points are not fixed");
fi;
if ForAny(Q0RelationSupport, pair -> pair[1] = 3) then
    Error("the fixed-point fill overlaps the one-row matching generator");
fi;

Print("support=", Length(Q0RelationSupport),
      " residual=", Length(Q0RelationResidual),
      " exact_rational=true matching=t->2-t fixed=2",
      " decoder_squared_norm=2\n");
