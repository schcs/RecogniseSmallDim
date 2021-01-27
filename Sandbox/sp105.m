//import "smalldimreps.m":BasisMatrixForAltSquareSp;

g0 := Sp( 6, 3 );

g := sub< GL( 15, 3 ) | __funcSLdqToAltSquare( g0.1 ), 
     __funcSLdqToAltSquare( g0.2 )>;

M := GModule( g );

subs := Submodules( M );
mat := ZeroMatrix( GF( 3 ), 15 );
mat[1,1] := 1; //12 
mat[2,2] := 1; //13
mat[3,3] := 1; //14
mat[4,4] := 1; //15
mat[5,5] := 1; mat[5,10] := -1;
mat[6,6] := 1;
mat[7,7] := 1;
mat[8,9] := 1;
mat[9,11] := 1;
mat[10,12] := 1;
mat[11,13] := 1;
mat[12,14] := 1;
mat[13,15] := 1;
mat[14,5] := 1; mat[14,8] := 1; mat[14,10] := 1;
mat[15,10] := 1;

zerox := function( x )
    
    for i in [1..13] do
        x[i,14] := 0;
    end for;
    
    for i in [1..14] do
        x[15,i] := 0;
    end for;
    
    return x;
end function;
    
zeroxx := function( x )
    
    indcs := [5,8,10];
    for i in indcs do
        for j in [1..15] do
            x[i,j] := 0;
            x[j,i] := 0;
        end for;
    end for;
    
    return x;
end function;
    
      




