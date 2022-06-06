import "smalldimreps.m":SolveAltSquareDimEq, funcpos_altsquare, 
  __funcSLdqToAltSquare, __funcAltSquareToSLdq;

import "auxfunctions.m": MyDerivedGroupMonteCarlo, IsSimilarModMinus1List, 
  IsSimilarModScalar, SplitTensor, RandomInvolution, InvolutionWithProperty,
  IsSimilarToScalarMultiple;

import "altsquare_sp.m": RecogniseAltSquareSpFunc;

import "recogsmalldim.m":RecogniseAltSquareWithSmallDegree;

// checks if RecogniseSymSquare works for a given set of paramenters
IsValidParameterSetForAltSquare := function( type, dim, q )
    
    _, p := IsPrimePower( q );
    if p eq 2 then return false; end if;
    
    if type eq "SL" and dim in {5,6} then 
        return false;
    elif type eq "Sp" and dim lt 8 then 
        return false;
    elif type eq "SU" and dim lt 2 then 
        return false;
    elif type eq "SU" and dim in {5,6} then 
        return false;
    elif type eq "Omega+" and dim lt 12 then
        return false;
    //elif type eq "Omega+" and p eq 5 then 
    //    return false;
    elif type eq "Omega-" and dim lt 12 then 
        return false;
    elif type eq "Omega" and dim lt 9 then 
        return false;
    elif type eq "Omega" and dim eq 9 and q eq 3 then 
        return false;
    elif type eq "Omega*" and dim lt 12 then 
        return false;
    end if;

    return true;
end function;

// 2-dimensional recognition

RecogniseAltSquareDim2 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 2";
    F := CoefficientRing( G );
    
    if Dimension( G ) ne 1 and ( Generators( G )  ne { One( G )} 
               or Generators( G ) ne {} ) then
        return false;
    end if;
    
    return true, _, pmap< GL( 2, F ) -> GL( 1, F ) |
           x:->[ Determinant( x )]>, Basis( VectorSpace( F, 2 ));
end function;
    
// three dimensional recognition    

RecogniseAltSquareDim3 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 3";
    q := #CoefficientRing( G );
      
    a := map< GL(3,q) -> GL(3,q) | x :-> __funcSLdqToAltSquare( x )>;
    b := map< GL(3,q) -> GL(3,q) | x :-> __funcAltSquareToSLdq( x )>; 
        
    return true, a, b, One( GL( 3, q ));
end function;
    
// 4-dimensional recognition    
    
RecogniseAltSquareDim4 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 4";
    cputm := Cputime();
    
    /* G preserves an orthogonal form. First find the matrix that 
       transforms G to canonical form with respect to this form. */
      
    q := #CoefficientRing( G );
    mat := GL( 6, q )!TransformForm( G );
    mat := mat*GL(6,q)!DiagonalMatrix( GF( q ), [1,-1,1,1,1,1] );
        
    // construct the function SL(4,q) -> G 
      
    a := map< GL( 4, q ) -> GL( 6, q ) | 
         x :-> (SL(6,q)!__funcSLdqToAltSquare( x )^(mat^-1)) >;
    
    // construct the function G -> SL( 4, q )
    
    b := pmap< GL( 6, q ) -> GL( 4, q ) | 
         x :-> __funcAltSquareToSLdq( x^mat ) >;

    vprint SymSquareVerbose: "# Recog AltSquare dim 4 took", Cputime()-cputm;
    
    return true, a, b, mat^-1;
end function;    
    
    
/* The following function performs AltSquare recognition. */

forward RecogniseAltSquareFunc;
      
RecogniseAltSquareFunc := function( G :  Method := "Recursive",
                                         type := "SL", 
                                         IsRecursiveCall := false )
    cputm := Cputime(); 
    q := #CoefficientRing( G ); 
    _, p := IsPrimePower( q );
    dimg := Dimension( G );
    
    // the natural dimension of G
    dim := SolveAltSquareDimEq( dimg : type := type ); 
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim, 
            "type", type, "method", Method ;

    if type eq "SL" and dim in {5,6} then 
        return RecogniseAltSquareWithSmallDegree( G : type := type );
    elif type eq "SU" and dim in {5, 6} then 
        return RecogniseAltSquareWithSmallDegree( G : type := type );
     elif type eq "Omega-" and dim in {8,10} then 
        return RecogniseAltSquareWithSmallDegree( G : type := type );
    elif type eq "Sp" and dim eq 10 and p eq 3 then   
        return RecogniseAltSquareWithSmallDegree( G : type := type );
    elif type eq "Omega+" and dim eq 10 then
        return RecogniseAltSquareWithSmallDegree( G : type := type );
    elif type eq "Omega" and dim eq 9 and p eq 3 then
        return RecogniseAltSquareWithSmallDegree( G : type := type );
    end if; 

    if type eq "Sp" then
      return RecogniseAltSquareSpFunc( G : Method := Method );
    end if;
                                                                       
    // in small dimension, call other functions
    case dim: 
      when 2: return RecogniseAltSquareDim2( G );
      when 3: return RecogniseAltSquareDim3( G );
      when 4: return RecogniseAltSquareDim4( G );
    end case;
    
    //if dim le 8 then Method := "Tensor"; end if;
    /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      
    eiglim1 := case< dim | 6: 8, 11: 29, 12: 35, default: (2/9)*dim^2 >; 
    // lower limit for eigenspace dim
    eiglim2 := case< dim | 6: 8, default: (1/4)*dim^2 >; 
    // upper limit for eigenspace dim
    
    if type eq "Omega-" and dim eq 12 then 
        eiglim1 := 36; eiglim2 := 36;
    end if;
      
    // set up property function for InvolutionWithProperty  
    propfunc := function( x )
        dmin := Dimension( Eigenspace( x, -1 ));  
        return dmin ge eiglim1 and dmin le eiglim2;
    end function;
        
    // completion checking function
    
    NrGensCentInv := 10; 
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    gensC := []; gensCD := [];
    
    // the number of components in the irred decomp for the centralizer

    repeat   
        repeatflag := false;
        if not assigned inv then 
            inv := InvolutionWithProperty( G, propfunc );
        end if;
        C := CentraliserOfInvolution( G, inv : 
                     CompletionCheck := __compcheck );  
        CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv,
                      DerivedLength := case< dim | 
                      8: 2, 9: 2, 10: 2, 11: 2, 12: 2, 18: 2, 
                        default : 1 >);      
        
        gensC := gensC cat GeneratorsSequence( C );
        gensCD := gensCD cat GeneratorsSequence( CD );
        C := sub< Universe( gensC ) | gensC >;

        CD := sub< Universe( gensCD ) | gensCD >;

        M := GModule( CD );
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )]; 
        if #mins eq 2 or 1 in { Dimension( x ) : x in mins } or 
           ( type in { "Omega+", "Omega-", "Omega" } and #mins  ne 3 ) or 
           ( type in { "Omega+", "Omega-", "Omega" } and 1 in { Dimension( x ) : x in mins }) then 
            delete inv;
            gensC := [];
            gensCD := [];
            repeatflag := true;
        end if;
        until  not repeatflag and #mins eq 3 and &+[ Dimension( x ) : x in mins ] eq dimg;
    
    vprint SymSquareVerbose: "#   Cent comput dim", dim, "took ", 
      Cputime()-cputm, #gensC, "gens used.";
      
      /* The C-module V splits into three components.
         Two components are isomorphic to alt square U and alt square W, 
         respectively. The third is isomorphic to U tensor W.  
         The two alt squares lie in one of the eigenspaces of inv. The tensor 
         lies in the other eigenspace. */
    mplus := [ mins[x] : x in [1..3] | 
               (M!mins[x].1)^inv eq M!mins[x].1 ];
    mminus := [ mins[x] : x in [1..3] | 
                (M!mins[x].1)^inv eq -M!mins[x].1 ];
    
    // in the case of Sp, etc, there is a one-dimensional component
      
    if #mplus eq 2 then
        mH := mplus[1]; mK := mplus[2]; mT := mminus[1];
    else 
        mH := mminus[1]; mK := mminus[2]; mT := mplus[1];
    end if;      
        
    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );
    dH := SolveAltSquareDimEq( dimH ); 
    dK := SolveAltSquareDimEq( dimK ); 
    dT := dH*dK;
    assert Dimension( mT ) eq dT;

    // set up the projections into the components
    
    ah := pmap< GL( dimg, q ) -> GL( dimH, q ) | 
          x :-> GL( dimH, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    ak := pmap< GL( dimg, q ) -> GL( dimK, q ) | 
          x :-> GL( dimK, q )![ Eltseq( mK!((M!b)^x )) : b in Basis( mK )]>;
    
    at := pmap< GL( dimg, q ) -> GL( dimT, q ) | 
          x :-> GL( dimT, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;

    if type in { "Omega", "Omega+", "Omega-" } then
        typeh := "Omega*"; typek := "Omega*";
    else
        typeh := type; typek := type;
    end if;

    vprint SymSquareVerbose: "# components are: ", typeh, dH, " and ", typek, dK;

    if not IsValidParameterSetForAltSquare( typeh, dH, q ) or 
       not IsValidParameterSetForAltSquare( typek, dK, q ) then 
        Method := "Tensor";
    end if;

    /* For some technical reason (see (###) later), the projection of a 
       generator of C cannot be similar to its negative and we want that
       the projection by ah and ak should fall into SL.     
       If some generator fails to satisfy this, it is thrown away and is 
       replaced by another one. */  

    mnsh := GL( dimH, q )!ScalarMatrix( GF( q ), dimH, -1 );
    mnsk := GL( dimK, q )!ScalarMatrix( GF( q ), dimK, -1 );
        
    // TODO: check if this is needed in this version. I suspect not.    
        
    for i in [1..#gensCD] do
        if Determinant( gensCD[i]@ah ) ne 1 or 
              Determinant( gensCD[i]@ak ) ne 1 or 
              IsSimilarToScalarMultiple( gensCD[i]@ah ) or
              IsSimilarToScalarMultiple( gensCD[i]@ak ) or 
              IsSimilarToScalarMultiple( gensCD[i]@at ) then 
           repeat
               x := Random( CD );
           until Determinant( x@ah ) eq 1 and
                Determinant( x@ak ) eq 1 and not 
                IsSimilarToScalarMultiple( x@ah ) and not
                IsSimilarToScalarMultiple( x@ak ) and not 
                IsSimilarToScalarMultiple( x@at );
           gensCD[i] := x;
       end if;
   end for; 
   
   CD:= sub< Universe( gensCD ) | gensCD >;

   if Method eq "Tensor" then 

       // TENSOR SPECIFIC CODE START HERE

       /* Construct the image of CD in the tensor product component. It must be 
          isomorphic to the tensor product of the preimages of the 
          groups induced on the alt square components */
      
       genst := [ x@at : x in gensCD ];
       aT := sub< Universe( genst ) | genst >;

       /* find the tensor decomposition of aT. There is a weird bug in the case 
          of Omega+ in dimension 10 and in such cases only a decomposition with 
          dimensions 6X4 is acceptable. */
       
       repeat 
           delete aT`TensorProductFlag;
           v := IsTensor( aT ); assert v; 

           //get the dimensions of the tensor factors
           dt1 := Dimension( TensorFactors( aT )[1] ); 
           dt2 := Dimension( TensorFactors( aT )[2] );
       until <type,dim,dt1> ne <"Omega+",10,4>;

       /* the dimensions dt1 and dt2 of the tensor factors must be equal to 
          dH and dK in this order. If not, we must swap H and K. */

       dt1 := Dimension( TensorFactors( aT )[1] ); 
       dt2 := Dimension( TensorFactors( aT )[2] );                           
       if dt1 ne dH then 
           temp := dH; dH := dK; dK := temp;
           temp := dimH; dimH := dimK; dimK := temp;
           temp := ah; ah := ak; ak := temp;
           temp := mH; mH := mK; mK := temp;
       end if;
    
       // calculate the basis for aT that reflects the tensor structure
       tbas := TensorBasis( aT )^-1;

       // set of the maps from aT into the tensor components
       ch := pmap< GL( dimg, q ) -> GL( dH, q ) | x :-> SplitTensor( 
                     tbas*x@at*tbas^-1, dH, dK )[1] >;
    
       ck := pmap< GL( dimg, q ) -> GL( dK, q ) | x :-> SplitTensor( 
                  tbas*x@at*tbas^-1, dH, dK )[2] >;
    
       gens1h := [ GL(dimH,q)!__funcSLdqToAltSquare( x@ch ) : x in gensCD ];
       gens2h := [ x@ah : x in gensCD ]; 

       gens1k := [ GL(dimK,q)!__funcSLdqToAltSquare( x@ck ) : x in gensCD ];
       gens2k := [ x@ak : x in gensCD ];
    
       vh, scalarsh := IsSimilarModScalar( gens1h, gens2h );
       
       if vh then
           vk, scalarsk := IsSimilarModScalar( gens1k, gens2k ); assert vk;
           gens2h := [ ScalarMatrix( GF(q), dimH, scalarsh[i] )*
                       gens2h[i] : i in [1..#gensCD] ];
           gens2k := [ ScalarMatrix( GF(q), dimK, scalarsk[i] )*gens2k[i] : 
                       i in [1..#gensCD] ];                            
       else 
           vh, scalarsh := IsSimilarModScalar( gens1h, gens2k ); 
           vk, scalarsk := IsSimilarModScalar( gens1k, gens2h ); 
           assert vh and vk;
           temp  := gens2h;
           gens2h := [ ScalarMatrix( GF(q), dimK, scalarsh[i] )*gens2k[i] : 
                         i in [1..#gensCD] ];
           gens2k := [ ScalarMatrix( GF(q), dimH, scalarsk[i] )*temp[i] : 
                       i in [1..#gensCD] ];
           temp := dimK; dimK := dimH; dimH := temp;
           temp := mK; mK := mH; mH := temp;       
       end if;
    
       M1H := GModule( sub< GL( dimH, q ) | gens1h >);
       M2H := GModule( sub< GL( dimH, q ) | gens2h >);
    
       v, trmh := IsIsomorphic( M1H, M2H ); assert v; 
    
       M1K := GModule( sub< GL( dimK, q ) | gens1k >);
       M2K := GModule( sub< GL( dimK, q ) | gens2k >);
    
       v, trmk := IsIsomorphic( M1K, M2K ); assert v;

       gggh := [ __funcAltSquareToSLdq( trmh*x*trmh^-1 ) : x in gens2h ];
        
       gggk := [ __funcAltSquareToSLdq( trmk*x*trmk^-1 ) : x in gens2k ];
           
       basH := [ M!(&+[trmh[j][i]*Basis( mH )[i] : 
                       i in [1..dimH]]) : j in [1..dimH]];
    
       basK := [ M!(&+[trmk[j][i]*Basis( mK )[i] : 
                       i in [1..dimK]]) : j in [1..dimK]];

       tbas := [ M!(&+[tbas[j][i]*Basis( mT )[i] : 
                      i in [1..dT]]) : j in [1..dT]];
        
        // TENSOR SPECIFIC CODE ENDS HERE
    end if;

    if Method eq "Recursive" then 
        // RECURSIVE CODE STARTS HERE
        aH := sub< GL( dimH, q ) | [ x@ah : x in gensCD ]>;
        aK := sub< GL( dimK, q ) | [ x@ak : x in gensCD ]>;
    
        aH := MyDerivedGroupMonteCarlo( aH : 
                      DerivedLength := case< dH | 4: 2, default: 1 > ); 
        aK := MyDerivedGroupMonteCarlo( aK : 
                      DerivedLength := case< dK | 4: 2, default: 1 >); 

        v1, b1, c1, bas1 := RecogniseAltSquareFunc( aH : type := typeh, IsRecursiveCall := true );
        v2, b2, c2, bas2 := RecogniseAltSquareFunc( aK : type := typek, IsRecursiveCall := true );
        assert v1 and v2;
    
        // bas1 is [e12,e13,...,e23,...,e{k-1}{k}]
        // bas2 is [e{k+1}{k+2},...,e{d-1}d]
        basH := [ M!(&+[bas1[j][i]*Basis( mH )[i] : 
                     i in [1..dimH]]) : j in [1..dimH]];
        basK := [ M!(&+[bas2[j][i]*Basis( mK )[i] : 
                     i in [1..dimK]]) : j in [1..dimK]];

        /* Construct the image of C in the tensor product component. It must be 
        isomorphic to the tensor product of the preimages of the 
        groups induced on the alt square components */
    
        genst := [ x@at : x in gensCD ];
        genstt := [ TensorProduct( x@ah@c1, x@ak@c2 ) : x in gensCD ];
    
        /* aT might be isomorphic to aH tensor aK or (aH)^-t tensor aK or
           aH tensor (aK)^-t or (aH)^-t tensor (aK)^-t where ^-t is the inverse
           transpose isomorphism. We need to discover which one it is and 
           modify bas1 and bas2 accordingly. */
      
        //foundflag := false;   // flag to show if the right case is found
    
        v, signs := IsSimilarModMinus1List( genst, genstt );
        
        if not v then 
            for cc in [1..3] do
                if cc eq 2 then 
                    genstt := [ TensorProduct( Transpose( x@ah@c1 )^-1, x@ak@c2 ) : 
                            x in gensCD ];
                    v, signs := IsSimilarModMinus1List( genst, genstt );
                    if v then 
                        vprint SymSquareVerbose: "# TransInv in first comp";
                        basH := [ basH[6], -basH[5], basH[4], 
                                  basH[3], -basH[2], basH[1]];        
                        break;
                    end if;
                elif cc eq 3 then 
                    genstt := [ TensorProduct( x@ah@c1, Transpose( x@ak@c2 )^-1) : 
                            x in gensCD ];
                    v, signs := IsSimilarModMinus1List( genst, genstt );
                    if v then 
                        vprint SymSquareVerbose: "# TransInv in second comp";
                        basK := [ basK[6], -basK[5], basK[4], 
                                  basK[3], -basK[2], basK[1]];        
                        break;
                    end if;
                elif cc eq 1 then 
                    genstt := [ TensorProduct( Transpose( x@ah@c1 )^-1, 
                                  Transpose( x@ak@c2 )^-1 ) : x in gensCD ];
                    v, signs := IsSimilarModMinus1List( genst, genstt );
                    if v then 
                        vprint SymSquareVerbose: "# TransInv in both comps";
                        basH := [ basH[6], -basH[5], basH[4], 
                                  basH[3], -basH[2], basH[1]];
                        basK := [ basK[6], -basK[5], basK[4], 
                                  basK[3], -basK[2], basK[1]];
                        break;
                    end if;
                end if;
            end for;
        end if;
    
        assert v;
        
        genstt := [ signs[i]*genstt[i] : i in [1..#genstt]];        
        T := GModule( sub< GL( dimT, q ) | genst >);
    
        TT := GModule( sub< GL( dimT, q ) | genstt >);
        v, al := IsIsomorphic( T, TT ); assert v;
    
        /* find the vectors eij with 1 <= j <= dH and dH+1 <= j <= dimg and 
           insert them into their place in bas. */
        V := VectorSpace( GF( q ), dimT );
        tbas := [ M!(mT!(V!Eltseq( x ))*(al^-1)) : 
                  x in [ Basis( T )[i] : i in [1..dimT]]];

        // RECURSIVE CODE ENDS HERE
    end if;

    /* we place the basis vectors computed in bas1 and bas2 into their place
       in the basis of V */

    bas := [ Zero( M ) : x in [1..dimg]];

    for i in [1..dH] do
        for j in [i+1..dH] do
            bas[funcpos_altsquare( dim, i, j )] := 
            basH[funcpos_altsquare( dH, i, j )];
        end for;
    end for;
    
    for i in [dH+1..dim] do
        for j in [i+1..dim] do
            bas[funcpos_altsquare(dim, i, j )] := 
              basK[funcpos_altsquare( dK, i-dH, j-dH )];
        end for;
    end for;
    
    for i in [1..dH] do
        for j in [dH+1..dim] do
            bas[funcpos_altsquare( dim, i, j )] := tbas[(i-1)*dK+j-dH];
        end for;
    end for;
        
    tr := Matrix( GF( q ), dimg, dimg, [ Eltseq( x ) : x in bas ] );
    //if dim eq 20 then error(111); end if;
        
    tr := GL( dimg, q )![ Eltseq( x ) : x in bas ];
    p12 := funcpos_altsquare( dim, 1, 2 );
    p13 := funcpos_altsquare( dim, 1, dH+1 );
    p23 := funcpos_altsquare( dim, 2, dH+1 );
    p14 := funcpos_altsquare( dim, 1, dH+2 );
    p34 := funcpos_altsquare( dim, dH+1, dH+2 );

    repeat
        x := Random( G )^(tr^-1);
        mat1 := Matrix( GF( q ), 3, 3, [
                        x[p12,p12],    x[p12,p13],    x[p12,p23],
                        x[p13,p12],    x[p13,p13],    x[p13,p23],        
                        x[p23,p12],    x[p23,p13],    x[p23,p23]] );
        
        mat2 := Matrix( GF( q ), 3, 3, [
                        x[p13,p13],    x[p13,p14],    x[p13,p34],
                        x[p14,p13],    x[p14,p14],    x[p14,p34],        
                        x[p34,p13],    x[p34,p14],    x[p34,p34]] );
        
                
        mm1 := __funcSLdqToAltSquare( mat1 );
        mm2 := __funcSLdqToAltSquare( mat2 );
        
    until Determinant( mat1 ) ne 0 and Determinant( mat2 ) ne 0 and 
          mm1[1,3] ne 0 and mm1[1,1] ne 0 and mm2[1,2] ne 0 and mm2[1,1] ne 0;
    
    mm2 := mm1[1,1]*mm2[1,1]^-1*mm2;
    lambdasq := mm1[1,3]/mm2[1,2];  
        
    try 
      lambda := Sqrt( lambdasq ); 
      for i in [1..dH] do
           for j in [dH+1..dim] do
               pij := funcpos_altsquare( dim, i, j );
               bas[pij] := lambda*bas[pij];
           end for;
       end for; 
    catch e  
      z0 := PrimitiveElement( GF( q ));
      lambda := Sqrt( z0*lambdasq );
      for i in [1..dH] do
          for j in [dH+1..dim] do
              pij := funcpos_altsquare( dim, i, j );
              // multiply eij by lambda
              bas[pij] := lambda*bas[pij];
          end for;
      end for;
    
      for i in [dH+1..dim] do
          for j in [i+1..dim] do
              pij := funcpos_altsquare( dim, i, j );
              // multiply eij by z0
              bas[pij] := z0*bas[pij];
          end for;
      end for;
    end try; 
    
    tr := GL( dimg, q )![ Eltseq( x ) : x in bas ];
      
    // construct the maps between GL(dim,q) and G

    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToAltSquare( x )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> GL( dim, q )!__funcAltSquareToSLdq( x^(tr^-1)) >;

    
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim, "took ", 
      Cputime()-cputm;
            
    return true, a, b, tr;
end function;
                
intrinsic RecogniseAltSquare( G::GrpMat : 
            type := "SL", 
            CheckResult := true,
            Method := "Recursive" ) 
          -> BoolElt, Map, Map, GrpMatElt
                                                         
 {G should be matrix group conjugate to the alternating square representation
  of SL( d, q ). Returns true/false, a map from SL( d, q ) to G, a map from 
  G to SL( d, q ), and a matrix whose rows form a basis that exhibits the 
  alt square structure. 
                           
  Supply CheckResult := true to check the final result.
                           
  The basic algorithm is implemented in two variations. The first uses a 
  recursive call for smaller dimensional alternating square recognition, while
  the second uses recognition of tensor decomposition with IsTensor. 
  For SL(d,q) with d=5,6,8 the tensor decomposition version is used while for
  SL(d,q) with d=7 or d>8 the recursive version is called as default. 
  This choice can be overwritten by setting UseTensorDecomposition to be true.}                                                
    dimg := Dimension( G );
    dim := SolveAltSquareDimEq( dimg : type := type );        
    q := #CoefficientRing( G );                 
    _, p := IsPrimePower( q );
    
    error if p eq 2, 
        "the field cannot have characteristic 2";
  
    error if type eq "Sp" and dim lt 8, 
        "Sp needs to have dimension at least 8";
    error if type eq "Omega+" and dim lt 10, 
        "Omega+ must have dimension at least 10";
    error if type eq "Omega-" and dim lt 10,
        "Omega- must have dimension at least 10";
    error if type eq "Omega" and dim lt 9, 
        "Omega must have dimension at least 9";

    v, _, _, tr := RecogniseAltSquareFunc( G : type := type, 
                              Method := Method );  
    assert v;

    if type in { "Omega+", "Omega-", "Omega" } then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcAltSquareToSLdq( x^(tr^-1) : type := type ) : 
                            x in GeneratorsSequence( G )] >)`bilinearForm;
        tr_form := TransformForm( form, case< type | 
                                            "Omega+": "orthogonalplus", 
                                            "Omega-": "orthogonalminus", 
                                            "Omega": "orthogonalcircle", 
                                            default: false  >);        
    elif type eq "SU" then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcAltSquareToSLdq( x^(tr^-1)) : x in GeneratorsSequence( G )] >)`sesquilinearForm;
        tr_form := TransformForm( form, "unitary" );
    else 
        tr_form := One( GL( dim, q ));
    end if;
    
    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToAltSquare( x^(tr_form^-1) : type := type )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> (GL( dim, q )!__funcAltSquareToSLdq( x^(tr^-1) : type := type ))^tr_form >;

    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        try
          gens := [ x@b : x in GeneratorsSequence( G )];
        catch e
          error( "could not compute preimages of generators" );
        end try;
        M1 := GModule( sub< GL( dimg, q ) | 
                     [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), dim )!(x^(tr_form^-1)) : type := type ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
            vprint SymSquareVerbose: "# Check failed.";
            return false, a, b, tr;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;

    return true, a, b, _;
end intrinsic;
