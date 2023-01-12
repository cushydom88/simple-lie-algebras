#Generate a "thin" Lie algebra from a list of pairs that denote special stucture constants. It will have dimension 2^n -1
#Also includes some binary helper functions for manipulation in GF(2)^n

intToVec := function( a, n )
    local V, i, b;
    b := a;
    V := [];
    for i in [1..n] do
        if ( b mod 2 ) = 1 then
            b := b - 1;
            V[ n + 1 - i ] := 1;
        else
            V[ n + 1 - i ] := 0; 
        fi;
        b := b / 2;
    od;
    return V;
end;

vecToInt := function( V )
    local a, n, i;
    n := Length( V );
    a := 0;
    for i in [1..n] do
        if V[i] = 1  then  
            a := a + 2^( n - i );
        fi; 
    od;
    return a;
end;

addVecs := function( V1, V2 )
    local V3, n, i;
    n := Length( V1 );
    V3 := [];
    for i in [1..n] do
        V3[i] := (V1[i] + V2[i]) mod 2; 
        od;
    return V3;
end;

LieAlgebraFromThinSC := function( Pairs, n )
    local T, K, dim, Pair, e1, e2, e3;
    K := GF( 2 );
    dim := 2^n - 1;
    T := EmptySCTable (dim, Zero(K), "antisymmetric"); 
    for Pair in Pairs do
        e1 := Pair[1];
        e2 := Pair[2];
        e3 := vecToInt( addVecs(intToVec( e1, n ), intToVec( e2, n ) ) );
        SetEntrySCTable (T, e1, e2, [1, e3]);
    od;
    if TestJacobi( T ) = true then    
        return (LieAlgebraByStructureConstants (K, T));
    else
        Print( TestJacobi( T ) );
        return 0;
    fi;
end;

#Here n should be 2^m-1
LieAlgebraFromThinAdjMat := function( Mat, m )
    local n, Pairs, i, j, result;
    n := Length( Mat );
    Pairs := [];
    for i in [1..n-1]  do
        for j in [i+1..n] do
            if Mat[i][j] = 1 then
                Add( Pairs, [i, j] );
            fi;
        od;
    od;
    result := LieAlgebraFromThinSC( Pairs, m );
    if 0 <> result then
        return result;
    fi; 
    return 0;
end;