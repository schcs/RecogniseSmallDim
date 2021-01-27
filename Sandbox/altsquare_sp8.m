import "smalldimreps.m":__funcAltSquareToSLdq, __funcSLdqToAltSquare;
import "auxfunctions.m":SplitTensor, IsSimilarModScalar;

BuildBasisSp8 := function( basH, basK, basT, wH :
                        scalars := [1,1,1,1] )
              
    a := scalars[1]; b := scalars[2]; c := scalars[3];
    d := scalars[4]; 
              
    q := #Field( Parent( basH[1] ));
    
    for v in [1..#basH] do
        basH[v] := a*basH[v];
    end for;
    
    for v in [1..#basK] do
        basK[v] := b*basK[v];
    end for;
    
    for v in [1..#basT] do
        basT[v] := c*basT[v];
    end for;
    
    bone1 := d*wH;
    
    v45 := (-basK[3]-bone1)/2;
    v18 := (basH[3]+bone1)/2;
    v27 := (-basH[3]+bone1)/2;
   
    bas := [];
    
    bas[1] := basH[1];   //12
    bas[2] := basT[1];   //13
    bas[3] := basT[2];   //14
    bas[4] := basT[3];   //15
    bas[5] := basT[4];   //16
    bas[6] := basH[2];   //17
    bas[7] := v18-v45;   //18-45=(18-27+18+27)/2-45
    bas[8] := basT[5];   //23
    bas[9] := basT[6];   //24
    bas[10] := basT[7];  //25                  
    bas[11] := basT[8];  //26
    bas[12] := v27-v45;  //27-45=(-18+27+18+27)/2-45 
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
      
    tr := MatrixAlgebra( GF( q ), 27 )![ Eltseq( x ) : x in bas ];   
    return tr;
end function;

    
TestBasis := function( basH, basK, basT, wH, wK, g )
    
    scalars := [ <1,b,1,d > : b in [1,-1], d in [1,-1] ]; 
    results := [];
    maxzero := 0;
    
    
    for s in scalars do
        bas := BuildBasisSp8( basH, basK, basT, wH :
                       scalars := [s[1], s[2], s[3], s[4]] );
        x0 := Random( g );
        try
          x := bas*x0*bas^-1;
          y := __funcAltSquareToSLdq( x : type := "Sp" );
          x1 := __funcSLdqToAltSquare( y : type := "Sp" );
          if x*x1^-1 eq x^0 then
              //print s[1], s[2], s[3], s[4], s[5];
              Append( ~results, true );
              return true, s;
          else
              Append( ~results, false );
              els := Eltseq( x-x1 );
              poszero := #[ els[x] : x in [1..#els] | els[x] eq 0 ];
              if poszero gt maxzero then
                 maxzero := poszero;
                 maxs := s;
             end if;
          end if;
                            
          catch e
            Append( ~results, false );
      end try;
    end for;
    
    return true in results, maxs, maxzero;
end function;
    
Get18Plus45 := function( p )
    
    mat := Matrix( GF( p ), 4, 4, [1,0,0,-1,0,1,0,-1,0,0,1,-1,1,1,1,1] )^-1;
    return mat[1]+mat[4];
end function;
    
  
FormValue := function( form, v1, v2 );
                     
    F := Parent( form[1,1] );                 
    return (v1*form*Matrix( F, 27, 1, 
                   Eltseq( v2 )))[1];
end function;
    
    
CheckForm := function( form, bas, g : test := false )
    
    F := Parent( form[1,1] );
    checkform0 := ClassicalForms( sub< SL( 27, F ) | 
                          bas*g.1*bas^-1,
                          bas*g.2*bas^-1 >)`bilinearForm; 
   
      
    checkform := Matrix( F, 27, 27,
                         [ [ (bas[y]*form*Matrix( F, 27, 1, 
                                 Eltseq( bas[x] )))[1] :
                             x in [1..27]] : y in [1..27]] );
    if test then
        print checkform0 eq checkform;
    end if;
    
    return checkform;
end function;
    
RecogniseAltSquareSp8qWithTensorDecomposition := function ( g : 
                                                 CheckResult := true );
    
    q := #CoefficientRing( g );
    z := PrimitiveElement( GF( q ));
    g0 := g;
    
    repeat 
        _, inv := RandomElementOfOrder( g, 2 );
    until Dimension( Eigenspace( inv, -1 )) eq 16;
    
      
    cd := CentraliserOfInvolution( g, inv );
    genscd := [ (Random( cd ), Random( cd )) : i in [1..10]];
    cd := sub< Universe( genscd ) | genscd >;
    
    M := GModule( cd );
    basM := Basis( M );
    
    mins := MinimalSubmodules( M ); 
    
    H := [ x : x in mins | Dimension( x ) eq 5 ][1];
    K := [ x : x in mins | Dimension( x ) eq 5 ][2];
    T := [ x : x in mins | Dimension( x ) eq 16 ][1];
    O := [ x : x in mins | Dimension( x ) eq 1 ][1];
    
    ah := pmap< GL( 27, q ) -> GL( 5, q ) | 
          x :-> GL( 5, q )![ Eltseq( H!((M!b)^x )) : b in Basis( H )]>;
    
    ak := pmap< GL( 27, q ) -> GL( 5, q ) | 
          x :-> GL( 5, q )![ Eltseq( K!((M!b)^x )) : b in Basis( K )]>;
    
    at := pmap< GL( 27, q ) -> GL( 16, q ) | 
          x :-> GL( 16, q )![ Eltseq( T!((M!b)^x )) : b in Basis( T )]>;
    
    genst := [ x@at : x in genscd ];
    aT := sub< Universe( genst ) | genst >; 
    
    v := IsTensor( aT ); assert v; 
    
    // calculate the basis for aT that reflects the tensor structure
      
    tbas := TensorBasis( aT )^-1; 
    // set of the maps from aT into the tensor components
      
    ch := pmap< GL( 27, q ) -> GL( 4, q ) | x :-> SplitTensor( 
                    tbas*x@at*tbas^-1, 4, 4 )[2] >;
    
    ck := pmap< GL( 27, q ) -> GL( 4, q ) | x :-> SplitTensor( 
                  tbas*x@at*tbas^-1, 4, 4 )[1] >;
    
    gens1h := [ x@ch : x in genscd ];
    gens1k := [ x@ck : x in genscd ];
    
    sch := ClassicalForms( sub< Universe( gens1h ) | gens1h > : 
                   Scalars := true )`scalars;
    sck := ClassicalForms( sub< Universe( gens1k ) | gens1k > 
                   : Scalars := true )`scalars;
    
    assert sch eq sck;
    
    if -1 in sch then
        scmat := ScalarMatrix( GF( q ), 4, Sqrt( GF( q )!(-1)) );
        
        for i in [1..#gens1h] do
           if sch[i] eq -1 then
               gens1h[i] := scmat*gens1h[i];
               gens1k[i] := scmat*gens1k[i];
           end if;
       end for;
   end if;
    
   Th := TransformForm( sub< Universe( gens1h ) | gens1h > );
   Tk := TransformForm( sub< Universe( gens1k ) | gens1k > );
      
   tbas1 := TensorProduct( Th^-1, Tk^-1 )*tbas; 
   gens1h := [ x^Th : x in gens1h ];
   gens1k := [ x^Tk : x in gens1k ];
   
   /* we calculate the matrices in the irreducible exterior square
     representation of Sp( d, q ) */
     
   gens1h := [ GL(5,q)!__funcSLdqToAltSquare( x : type := "Sp") : 
               x in gens1h ];
   gens2h := [ x@ah : x in genscd ];
   
   gens1k := [ GL(5,q)!__funcSLdqToAltSquare( x : type := "Sp" ) : 
               x in gens1k ];
   gens2k := [ x@ak : x in genscd ];
   
   vh, scalarsh := IsSimilarModScalar( gens1h, gens2h ); 
   
   if vh then
       vk, scalarsk := IsSimilarModScalar( gens1k, gens2k );
       gens2h := [ ScalarMatrix( GF( q ), 5, scalarsh[i] )*
               gens2h[i] : i in [1..#genscd]];
               gens2k := [ ScalarMatrix( GF( q ), 5, scalarsk[i] )*gens2k[i] : 
                         i in [1..#genscd]];                            
    else 
       vh, scalarsh := IsSimilarModScalar( gens1h, gens2k ); 
       vk, scalarsk := IsSimilarModScalar( gens1k, gens2h ); 
       assert vh and vk;
       temp  := gens2h;
       gens2h := [ ScalarMatrix( GF( q ), 5, scalarsh[i] )*gens2k[i] : 
                 i in [1..#genscd] ];
                 gens2k := [ ScalarMatrix( GF( q ), 5, scalarsk[i] )*temp[i] : 
                         i in [1..#genscd] ];
       temp := K; K := H; H := temp;       
   end if;
   
   assert vh and vk;
   
   M1H := GModule( sub< GL( 5, q ) | gens1h >);
   M2H := GModule( sub< GL( 5, q ) | gens2h >);

   v, trmh := IsIsomorphic( M1H, M2H ); assert v;
   
   M1K := GModule( sub< GL( 5, q ) | gens1k >);
   M2K := GModule( sub< GL( 5, q ) | gens2k >);
   
   v, trmk := IsIsomorphic( M1K, M2K ); assert v;
   
   basH := [ M!(&+[trmh[j][i]*Basis( H )[i] : 
                   i in [1..5]]) : j in [1..5]];
   
   basK := [ M!(&+[trmk[j][i]*Basis( K )[i] : 
                   i in [1..5]]) : j in [1..5]];
   
   basT := [ M!(&+[tbas1[j][i]*Basis( T )[i] : 
                   i in [1..16]]) : j in [1..16]];
   
   basOneDim := [ M!(Basis( O )[1])];
   
   /* if the form on (13,68) is not a square, then there is a
      an outer automorphism at play in the first factor. */
     
   bas := BuildBasisSp8( basH, basK, basT, basOneDim[1] );
   g := sub< SL( 27, q ) | { bas*x*bas^-1 : x in Generators( g0 )}>;
   form := ClassicalForms( g )`bilinearForm;
       
   if not IsSquare( form[2,26] ) then 
       basH := [z^2*basH[1], z*basH[2], z*basH[3], z*basH[4], basH[5]];
       for i in [1..8] do
           basT[i] := z*basT[i];
       end for;
   end if; 

   bas := BuildBasisSp8( basH, basK, basT, basOneDim[1] );
   g := sub< SL( 27, q ) | { bas*x*bas^-1 : x in Generators( g0 )}>;
   form := ClassicalForms( g )`bilinearForm;
   
   vH := Sqrt( form[1,27] )^-1; 
   vK := Sqrt( form[14,22] )^-1; 
   vT := Sqrt( form[2,26] )^-1;  
               
   for i in [1..#basH] do 
       basH[i] := vH*basH[i];
       basK[i] := -vK*basK[i];
   end for;
       
   for i in [1..16] do
       basT[i] := vT*basT[i];
   end for;
   
   bas := BuildBasisSp8( basH, basK, basT, basOneDim[1] ); 
   g := sub< SL( 27, q ) | { bas*x*bas^-1 : x in Generators( g0 )}>;
   form := ClassicalForms( g )`bilinearForm;
   

   a := Sqrt( -1/form[7,12] );
   basOneDim[1] := a*basOneDim[1];
   
   bas := BuildBasisSp8( basH, basK, basT, basOneDim[1] ); 
   g := sub< SL( 27, q ) | { bas*x*bas^-1 : x in Generators( g0 )}>;
   form := ClassicalForms( g )`bilinearForm;
   
   v, coeffs := 
     TestBasis( basH, basK, basT, basOneDim[1], basOneDim[1], g0 );  
   
   print coeffs;
   assert v;
   
   tr := BuildBasisSp8( [ coeffs[1]*x : x in basH ],
                      [ coeffs[2]*x : x in basK ],
                      [ coeffs[3]*x : x in basT ],
                  coeffs[4]*basOneDim[1] );
   
   tr := GL( 27, q )!tr;
    
    // construct the maps between GL(dim,q) and G
    
    a := map< GL( 8, q ) -> GL( 27, q ) | 
         x :-> GL( 27, q )!__funcSLdqToAltSquare( x : type := "Sp" )^tr >;
    
    b := pmap< GL( 27, q ) -> GL( 8, q ) |
         x :-> GL( 8, q )!__funcAltSquareToSLdq( x^(tr^-1) : 
                 type := "Sp" ) >;
    
    
    // if CheckResult is set, we perform a check
    if CheckResult then
        gens := [ x@b : x in GeneratorsSequence( g0 )];
        M1 := GModule( sub< GL( 27, q ) | 
                      [ __funcSLdqToAltSquare( 
                              MatrixAlgebra( GF( q ), 8 )!x : 
                              type := "Sp" ) : x in gens ]>);
        if not IsIsomorphic( M1, GModule( g0 )) then
            vprint SymSquareVerbose: "# Check failed";
        else
            vprint SymSquareVerbose: "# Check passed.";
        end if;
    end if;  

    
    return true, a, b, tr;
 end function;
    