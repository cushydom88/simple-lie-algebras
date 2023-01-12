# Shortened version of https://web.osu.cz/~Zusmanovich/soft/meataxe.gap by Pasha Zusmanovich 

MeataxeAdjointRep := function (A)
	local B, matrices, v;
	B := Basis (A);
	matrices := [];
	for v in B do
		Add (matrices, TransposedMat (AdjointMatrix (B, v)));
	od;
	return (GModuleByMats (matrices, LeftActingDomain (A)));
end;

MeataxeDualRep := function (M)
	local matrices, m;
	matrices := [];
	for m in MTX.Generators (M) do
		Add (matrices, - TransposedMat (m));
	od;
	return (GModuleByMats (matrices, MTX.Field (M)));
end;

MeataxeIsSimple := function (A)
	return (MTX.IsIrreducible (MeataxeAdjointRep (A)));
end;
