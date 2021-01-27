g0 := Sp( 8, 5 );

g := sub< SL( 28, 5 ) | __funcSLdqToAltSquare( g0.1 ), 
                        __funcSLdqToAltSquare( g0.2 ) >;
                        
inv := SL( 8, 5 )!DiagonalMatrix( GF( 5 ), [1,1,-1,-1,-1,-1,1,1] );
inv := SL(28,5)!__funcSLdqToAltSquare( inv );

inv := inv;

cd := CentraliserOfInvolution( g, inv );
genscd := [ (Random( cd ), Random( cd )) : i in [1..10]];
cd := sub< Universe( genscd ) | genscd >;

M := GModule( cd );

basM := Basis( M );

mins := MinimalSubmodules( M );
basM := Basis( M );

H := [ x : x in mins | Dimension( x ) eq 5 ][1];
K := [ x : x in mins | Dimension( x ) eq 5 ][2];
T := [ x : x in mins | Dimension( x ) eq 16 ][1];

vec0 := basM[7]+basM[12]+basM[16]+basM[19];
vec1 := basM[7]+basM[12];

basH := [ basM[1], basM[6], basM[7]-basM[12], basM[13], basM[28]];

basK := [ basM[14], basM[15], basM[16]-basM[19], basM[20], basM[23]];

basT := [ basM[2], basM[3], basM[4], basM[5], 
          basM[8], basM[9], basM[10], basM[11], 
          -basM[17], -basM[21], -basM[24], -basM[26], 
          -basM[18], -basM[22], -basM[25], -basM[27]];

form := ClassicalForms( g )`bilinearForm;
vH := Sqrt((basH[1]*form*Matrix( 27, 1, basH[5] ))[1])^-1;
vK := Sqrt((basK[1]*form*Matrix( 27, 1, basK[5] ))[1])^-1;
vO := Sqrt((basOneDim[1]*form*Matrix( 27, 1, basOneDim[1] ))[1])^-1;
    
for i in [1..#basH] do 
    basH[i] := vH*basH[i];
    basK[i] := vK*basK[i];
end for;
    
basOneDim[1] := 2*vO*basOneDim[1];

basOneDim := [ M!vec1 ];
basF := [ M!vec0 ];

BuildBasis_ := function( basH, basK, basT, basOneDim, basF )

    bas := [];
    
    bas[1] := basH[1];   //12
    bas[2] := basT[1];   //13
    bas[3] := basT[2];   //14
    bas[4] := basT[3];   //15
    bas[5] := basT[4];   //16
    bas[6] := basH[2];   //17
    bas[7] := (basH[3]+basK[3]+2*basOneDim[1])/2;   //18-45=(18-27+18+27)/2-45
    bas[8] := basT[5];   //23
    bas[9] := basT[6];   //24
    bas[10] := basT[7];  //25                  
    bas[11] := basT[8];  //26
    bas[12] := (-basH[3]+basOneDim[1]+basK[3]+basOneDim[1])/2; 
    //27-45=(-18+27+18+27)/2-45 
    bas[13] := basH[4];   //28    
    bas[14] := basK[1];   //34
    bas[15] := basK[2];   //35 
    bas[16] := basK[3];   //36-45
    bas[17] := -basT[9];  //37
    bas[18] := -basT[13]; //38
    bas[19] := basK[4];   //46
    bas[20] := -basT[10]; //47
    bas[21] := -basT[14]; //48
    bas[22] := basK[5];   //56
    bas[23] := -basT[11]; //57
    bas[24] := -basT[15]; //58
    bas[25] := -basT[12]; //67
    bas[26] := -basT[16]; //68
    bas[27] := basH[5];   //78
    
    bas[28] := basF[1];
      
    tr := MatrixAlgebra( GF( 5 ), 28 )![ Eltseq( x ) : x in bas ];   
    return tr;
end function;
