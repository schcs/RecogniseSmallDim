q := 19; 
g0 := Omega( 11, q );
V0 := VectorSpace( GF( q ), 11 );
G0 := sub< GL( 66, q ) | __funcSLdqToSymSquare( g0.1 ), __funcSLdqToSymSquare( g0.2 )>;
M0 := GModule( G0 );
mins := MinimalSubmodules( M0 );
basM0 := BasisMatrixForSymSquareOmega( 11, GF( q ));
M1 := mins[1];
M2 := mins[2];

w1 := 4*V0.3+15*V0.6+11*V0.9; 
w2 := 1*V0.3+11*V0.6+17*V0.9; 
w3 := 10*V0.3+0*V0.6+1*V0.9;

U := [V0.1, V0.2, w1, w3, V0.10, V0.11];
W := [V0.4, V0.5, w2, V0.7, V0.8];

UU := SymSquareBasis( U );
WW := SymSquareBasis( W );
UW := TensorProdBasis( U, W );

bas_6_min := BasisMatrixForSymSquareOmegaMinus( 6, GF(q));
bas_5_circ := BasisMatrixForSymSquareOmega( 5, GF(q) : a := 2, b := -1 );
basH := [&+[ bas_6_min[i,j]*UU[j] : j in [1..21]] : i in [1..21]];
basK := [&+[ bas_5_circ[i,j]*WW[j] : j in [1..15]] : i in [1..15]];

V65 := VectorSpace( GF( q ), 65 );

basHH := [ V65!Coordinates( M2, M0!basH[x] ) : x in [1..20]];
basKK := [ V65!Coordinates( M2, M0!basK[x] ) : x in [1..14]];
basTT := [ V65!Coordinates( M2, M0!UW[x] ) : x in [1..30]];

basOneDim := [ V65!(Eltseq( basH[21]*basM0^-1 )[1..65])];

g := sub< GL( 65, q ) | __funcSLdqToSymSquare( g0.1 : type := "Omega", a := -2, b := 1 ), 
                        __funcSLdqToSymSquare( g0.2 : type := "Omega", a := -2, b := 1 )>;

form65mat := ClassicalForms( g )`bilinearForm;

form65 := function( u, v ) 
            return (u*form65mat*Matrix( GF( q ), 65, 1, Eltseq( v )))[1];
end function;

form11mat := ClassicalForms( g0 )`bilinearForm;
form11 := function( u, v ) 
            return (u*form11mat*Matrix( GF( q ), 11, 1, Eltseq( v )))[1];
end function;


bH, bK, bT, bod := RecogniseSymSquareWithTensorDecompositionOmegaFunc( g : type := "Omega" );

m2H := Matrix( GF( q ), 20, 20, [ form65( x, y ): x, y in basHH[1..20]] );
m1H := Matrix( GF( q ), 20, 20, [ form65( x, y ): x, y in bH[1..20]] );
m1H eq m1H[1,20]*m2H;

m2K := Matrix( GF( q ), 14, 14, [ form65( x, y ): x, y in basKK[1..14]] );
m1K := Matrix( GF( q ), 14, 14, [ form65( x, y ): x, y in bK[1..14]] );
m1K eq m1K[1,14]*m2K;

m2T := Matrix( GF( q ), 30, 30, [ form65( x, y ): x, y in basTT[1..30]] );
m1T := Matrix( GF( q ), 30, 30, [ form65( x, y ): x, y in bT[1..30]] );
m1T eq (m1T[1,30]/m2T[1,30])*m2T;

