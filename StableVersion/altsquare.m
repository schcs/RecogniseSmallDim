import "smalldimreps.m":SolveAltSquareDimEq, funcpos_altsquare, 
  __funcSLdqToAltSquare, __funcAltSquareToSLdq;

import "auxfunctions.m": MyDerivedGroupMonteCarlo, IsSimilarModMinus1List, 
  IsSimilarModScalar, SplitTensor, RandomInvolution, InvolutionWithProperty,
  IsSimilarToScalarMultiple;

import "altsquare_sp.m": RecogniseAltSquareWithTensorDecompositionSp;

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

RecogniseAltSquareDim3 := function( G : type := "SL", 
                                    CheckResult := CheckResult )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 3";
    q := #CoefficientRing( G );
      
    a := map< GL(3,q) -> GL(3,q) | x :-> __funcSLdqToAltSquare( x )>;
    b := a; // the inverse function is the same
    
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        gens := [ x@b : x in GeneratorsSequence( G )];
        M1 := GModule( sub< GL( 3, q ) | 
                      [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), 3 )!x ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
            return false, _, _, _;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;
    
    return true, a, b, Basis( VectorSpace( GF( q ), 3 ));
end function;
    
// 4-dimensional recognition    
    
RecogniseAltSquareDim4 := function( G : type := "SL", CheckResult := true )
    
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
    
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        gens := [ x@b : x in GeneratorsSequence( G )];
        M1 := GModule( sub< GL( 6, q ) | 
                      [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), 4 )!x ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
	return false, _, _, _;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;

    vprint SymSquareVerbose: "# Recog AltSquare dim 4 took", Cputime()-cputm;
    
    return true, a, b, mat^-1;
end function;    
    
    
/* The following function performs AltSquare recognition by recognising
   the tensor component and recovering the smaller alt square components 
   directly from the tensor factor. It does not use recursive call and it
   may perform better for certain inputs. */
  
      
RecogniseAltSquareWithTensorDecomposition := function( G : 
                                         type := "SL", CheckResult := true )
    cputm := Cputime(); 
    q := #CoefficientRing( G ); 
    dimg := Dimension( G );
    
    // the natural dimension of G
    dim := SolveAltSquareDimEq( dimg : type := type ); 
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim;
    
    /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      
    eiglim1 := case< dim | 6: 8, 11: 29, 12: 35, default: (2/9)*dim^2 >; 
    // lower limit for eigenspace dim
    eiglim2 := case< dim | 6: 8, default: (1/4)*dim^2 >; 
    // upper limit for eigenspace dim
    
    if type eq "Omega-" and dim eq 12 then 
        eiglim1 := 36;
        eiglim2 := 36;
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
        print [ Dimension( x ) : x in mins ];
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
              IsSimilarToScalarMultiple( gensCD[i]@ak ) then
           repeat
               x := Random( CD );
           until Determinant( x@ah ) eq 1 and
                Determinant( x@ak ) eq 1 and not 
                IsSimilarToScalarMultiple( x@ah ) and not
                IsSimilarToScalarMultiple( x@ak );
           gensCD[i] := x;
       end if;
   end for; 
   
   CD:= sub< Universe( gensCD ) | gensCD >;
        
   /* Construct the image of CD in the tensor product component. It must be 
      isomorphic to the tensor product of the preimages of the 
      groups induced on the alt square components */
      
    genst := [ x@at : x in gensCD ];
    aT := sub< Universe( genst ) | genst >;
    
    v := IsTensor( aT ); assert v; 
    
    // get the dimensions of the tensor factors
    dt1 := Dimension( TensorFactors( aT )[1] ); 
    dt2 := Dimension( TensorFactors( aT )[2] );
    
    /* the dimensions dt1 and dt2 of the tensor factors must be equal to 
       dH and dK in this order. If not, we must swap H and K. */
                                  
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
        vk, scalarsk := IsSimilarModScalar( gens1k, gens2k );
        gens2h := [ ScalarMatrix( GF(q), dimH, scalarsh[i] )*
                    gens2h[i] : 
                      i in [1..#gensCD] ];
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
    
    assert vh and vk;
    
    M1H := GModule( sub< GL( dimH, q ) | gens1h >);
    M2H := GModule( sub< GL( dimH, q ) | gens2h >);
    
    v, trmh := IsIsomorphic( M1H, M2H ); assert v;
    
    M1K := GModule( sub< GL( dimK, q ) | gens1k >);
    M2K := GModule( sub< GL( dimK, q ) | gens2k >);
    
    v, trmk := IsIsomorphic( M1K, M2K ); assert v;
    
    // bas1 is [e12,e13,...,e23,...,e{k-1}{k}]
    // bas2 is [e{k+1}{k+2},...,e{d-1}d]
      
    basH := [ M!(&+[trmh[j][i]*Basis( mH )[i] : 
                    i in [1..dimH]]) : j in [1..dimH]];
    
    basK := [ M!(&+[trmk[j][i]*Basis( mK )[i] : 
                    i in [1..dimK]]) : j in [1..dimK]];
            
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
    
    tbas := [ M!(&+[tbas[j][i]*Basis( mT )[i] : 
                     i in [1..dT]]) : j in [1..dT]];

    for i in [1..dH] do
        for j in [dH+1..dim] do
            bas[funcpos_altsquare( dim, i, j )] := tbas[(i-1)*dK+j-dH];
        end for;
    end for;
    
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
    
    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        try
          gens := [ x@b : x in GeneratorsSequence( G )];
        catch e
          return false, a, b, tr, CD;
          error(1);
        end try;
        M1 := GModule( sub< GL( dimg, q ) | 
                     [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), dim )!x ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
            vprint SymSquareVerbose: "# Check failed.";
            return false, a, b, tr, CD;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;
        
    return true, a, b, tr, CD;
end function;

            
// The general function with recursion
    
RecogniseAltSquareWithRecursion := function( G : type := "SL", 
                                               CheckResult := true )
    
    cputm := Cputime();
          
    q := #CoefficientRing( G ); 
    dimg := Dimension( G );
    dim := SolveAltSquareDimEq( dimg ); // the natural dimension of G
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim;
    
    /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      
    eiglim1 := case< dim | 6: 8, default: (2/9)*dim^2 >; 
    // lower limit for eigenspace dim
    eiglim2 := case< dim | 6: 8, default: (1/4)*dim^2 >; 
    // upper limit for eigenspace dim
      
    // set up property function for InvolutionWithProperty  
    propfunc := function( x ) 
        dmin := Dimension( Eigenspace( x, -1 )); 
        return dmin ge eiglim1 and dmin le eiglim2;
    end function;
        
    gensC := []; gensCD := [];
    flag_dim8 := case< dim | 8: false, default: true >;
                  
    vprint SymSquareVerbose: "#   Inv search dim", dim;
    
    // completion checking function
    
    NrGensCentInv := 10; 
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    gensC := []; gensCD := [];
    repeat   
        if not assigned inv then
            inv := InvolutionWithProperty( G, propfunc );
        end if;
        C := CentraliserOfInvolution( G, inv : 
                     CompletionCheck := __compcheck );  
        CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv,
                      DerivedLength := case< dim | 
                      8: 2, 9: 2, 10: 2, 11: 2, 12: 2, 
                      default : 1 >);     
        gensC := gensC cat GeneratorsSequence( C );
        gensCD := gensCD cat GeneratorsSequence( CD );
        C := sub< Universe( gensC ) | gensC >;
        CD := sub< Universe( gensCD ) | gensCD >;
        
        M := GModule( CD );
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )];
        
        if #mins eq 2 then 
            delete inv; 
            gensC := [];
            gensCD := [];  
        end if;
          
        /* In the case of SL(8,q), we need to avoid the split into 
           dimension 8 = 6 + 2 and this needs to be tested explicitly */
          
        flag_dim8 := dimg ne 8 or { Dimension( x ) : x in mins } in 
                       {{12,6},{6,16}};     
        print [ Dimension( x ) : x in mins ];
    until  #mins eq 3 and &+[ Dimension( x ) : x in mins ] eq dimg 
          and flag_dim8;

    vprint SymSquareVerbose: "#   InvCent comput dim", dim, "took ", 
      Cputime()-cputm, #gensC, "gens used.";
      
      /* The C-module V splits into three components.
         Two components are isomorphic to alt square U and alt square W, 
         respectively. The third is isomorphic to U tensor W.  
         The two alt squares lie in one of the eigenspaces of inv. The tensor 
         lies in the other eigenspace. */
      
    mplus := [ mins[x] : x in [1..3] | (M!mins[x].1)^inv eq M!mins[x].1 ];
    mminus := [ mins[x] : x in [1..3] | (M!mins[x].1)^inv eq -M!mins[x].1 ];

    if #mplus eq 2 then
        mH := mplus[1]; mK := mplus[2]; mT := mminus[1];
    else 
        vprint SymSquareVerbose: "# minus 1 at play";
        mH := mminus[1]; mK := mminus[2]; mT := mplus[1];
    end if;      
        
    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );
    dH := SolveAltSquareDimEq( dimH ); dK := SolveAltSquareDimEq( dimK ); 
    assert Dimension( mT ) eq dH*dK;
    
    // set up the projections into the components
    
    ah := pmap< GL( dimg, q ) -> GL( dimH, q ) | 
          x :-> GL( dimH, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    ak := pmap< GL( dimg, q ) -> GL( dimK, q ) | 
          x :-> GL( dimK, q )![ Eltseq( mK!((M!b)^x )) : b in Basis( mK )]>;
    
    at := pmap< GL( dimg, q ) -> GL( dimT, q ) | 
          x :-> GL( dimT, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;
    
    /* For some technical reason (see (###) later), the projection of a 
       generator of C cannot be similar to its negative and we want that
       the projection by ah and ak should fall into SL.     
       If some generator fails to satisfy this, it is thrown away and is 
       replaced by another one. */  

    mns := GL( dimT, q )!ScalarMatrix( GF( q ), dimT, -1 );

    for i in [1..#gensCD] do
        if Determinant( gensCD[i]@ah ) ne 1 or 
              Determinant( gensCD[i]@ak ) ne 1 or 
              IsSimilar( gensCD[i]@at, mns*gensCD[i]@at ) then
           repeat
               x := Random( CD );
           until Determinant( x@ah ) eq 1 and
                Determinant( x@ak ) eq 1 and not 
              IsSimilar( x@at, mns*x@at );
           gensCD[i] := x;
       end if;
   end for; 
   
   CD:= sub< Universe( gensCD ) | gensCD >;

    /* construct and recognise the two groups induced on the alt square
       components */

    aH := sub< GL( dimH, q ) | [ x@ah : x in gensCD ]>;
    aK := sub< GL( dimK, q ) | [ x@ak : x in gensCD ]>;
    
    
    aH := MyDerivedGroupMonteCarlo( aH : 
                  DerivedLength := case< dH | 4: 2, default: 1 > ); 
    aK := MyDerivedGroupMonteCarlo( aK : 
                  DerivedLength := case< dK | 4: 2, default: 1 >); 
    
    v1, b1, c1, bas1 := RecogniseAltSquare( aH : CheckResult := false );
    v2, b2, c2, bas2 := RecogniseAltSquare( aK : CheckResult := false );
    assert v1 and v2;
    
    // bas1 is [e12,e13,...,e23,...,e{k-1}{k}]
    // bas2 is [e{k+1}{k+2},...,e{d-1}d]
      
    bas1 := [ M!(&+[bas1[j][i]*Basis( mH )[i] : 
                 i in [1..dimH]]) : j in [1..dimH]];
    bas2 := [ M!(&+[bas2[j][i]*Basis( mK )[i] : 
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
      
    foundflag := false;   // flag to show if the right case is found
    
    v, signs := IsSimilarModMinus1List( genst, genstt );
    if v then
        vprint SymSquareVerbose: "# No tensor is involved in dim ", dim;
        foundflag := true;
    elif not foundflag and not v then
        genstt := [ TensorProduct( Transpose( x@ah@c1 )^-1, x@ak@c2 ) : 
                    x in gensCD ];
        v, signs := IsSimilarModMinus1List( genst, genstt );
    end if;
    
    if not foundflag and v then
        vprint SymSquareVerbose: "# Tensor is involved in first comp in dim ", 
          dim;
        bas1 := [ bas1[6], -bas1[5], bas1[4], bas1[3], -bas1[2], bas1[1]];
        foundflag := true;
    elif not foundflag and not v then
        genstt := [ TensorProduct( x@ah@c1, Transpose( x@ak@c2 )^-1 ) : 
                        x in gensCD ];
        v, signs := IsSimilarModMinus1List( genst, genstt );
    end if;
    
    if not foundflag and v then
        vprint SymSquareVerbose: "# Tensor is involved in second comp in dim ", 
          dim;
        bas2 := [ bas2[6], -bas2[5], bas2[4], bas2[3], -bas2[2], bas2[1]];
        foundflag := true;
    elif not foundflag and not v then
        genstt := [ TensorProduct( Transpose( x@ah@c1 )^-1, 
                          Transpose( x@ak@c2 )^-1 ) : x in gensCD ];
        v, signs := IsSimilarModMinus1List( genst, genstt );
    end if;
    
    if not foundflag and v then
        vprint SymSquareVerbose: "# Tensor is involved in both comp in dim ", 
          dim;
        bas1 := [ bas1[6], -bas1[5], bas1[4], bas1[3], -bas1[2], bas1[1]];
        bas2 := [ bas2[6], -bas2[5], bas2[4], bas2[3], -bas2[2], bas2[1]];
        foundflag := true;
    end if;
    
    assert foundflag;
        
    /* we place the basis vectors computed in bas1 and bas2 into their place
       in the basis of V */
      
    bas := [ Zero( M ) : x in [1..dimg]];
    
    for i in [1..dH] do
        for j in [i+1..dH] do
            bas[funcpos_altsquare( dim, i, j )] := 
              bas1[funcpos_altsquare( dH, i, j )];
        end for;
    end for;
    
    for i in [dH+1..dim] do
        for j in [i+1..dim] do
            bas[funcpos_altsquare(dim, i, j )] := 
              bas2[funcpos_altsquare( dK, i-dH, j-dH )];
        end for;
    end for;
    
    genstt := [ signs[i]*genstt[i] : i in [1..#genstt]];
        
    T := GModule( sub< GL( dimT, q ) | genst >);
    
    TT := GModule( sub< GL( dimT, q ) | genstt >);
    v, al := IsIsomorphic( T, TT ); assert v;
    
    /* find the vectors eij with 1 <= j <= dH and dH+1 <= j <= dimg and 
       insert them into their place in bas. */
    V := VectorSpace( GF( q ), dimT );
    tbas := [ M!(mT!(V!Eltseq( x ))*(al^-1)) : 
              x in [ Basis( T )[i] : i in [1..dimT]]];
    
    for i in [1..dH] do
        for j in [dH+1..dim] do
            bas[funcpos_altsquare( dim, i, j )] := tbas[(i-1)*dK+j-dH];
        end for;
    end for;
    
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
    
    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        try
          gens := [ x@b : x in GeneratorsSequence( G )];
        catch e
          error(1);
        end try;
        M1 := GModule( sub< GL( dimg, q ) | 
                     [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), dim )!x ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
            vprint SymSquareVerbose: "# Check failed.";
            return false, _, _, _;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;
        
    return true, a, b, tr;
end function;
    
forward RecogniseAltSquare;
    
intrinsic RecogniseAltSquare( G::GrpMat : 
            type := "SL", 
            CheckResult := true,
            UseTensorDecomposition := true ) 
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
  dim := Dimension( G );                         
  p := Characteristic( CoefficientRing( G ));
  
  error if p eq 2, "the field cannot have characteristic 2";
  error if type eq "SL" and dim lt 21, "SL needs to have dimension at least 7";
  error if type eq "Sp" and dim lt 27, "Sp needs to have dimension at least 8";
  error if type eq "SU" and dim lt 21, "SU needs to have dimension at least 7"; 
  error if type eq "Omega+" and dim lt 66, "Omega+ needs to have dimension at least 12"; 
  error if type eq "Omega-" and dim lt 66, "Omega- needs to have dimension at least 12"; 
  error if type eq "Omega" and dim lt 55, "Omega needs to have dimension at least 11";
      
  if type eq "Sp" then
      return RecogniseAltSquareWithTensorDecompositionSp( G : 
      CheckResult := CheckResult );
  end if;
                                                                       
  // in small dimension, call other functions
  case dim: 
      when 1: return RecogniseAltSquareDim2( G );
      when 3: return RecogniseAltSquareDim3( G : CheckResult := CheckResult );
      when 6: return RecogniseAltSquareDim4( G : CheckResult := CheckResult );
  end case;
  
  // in dimensions 5, 6 and 8 we enforce UseTensorDecomposition
    
  UseTensorDecomposition := UseTensorDecomposition or dim in { 10, 15, 28 };
  
  if UseTensorDecomposition then
      return RecogniseAltSquareWithTensorDecomposition( G : 
                     CheckResult := CheckResult, type := type );
  else
      return RecogniseAltSquareWithRecursion( G : 
              CheckResult := CheckResult, type := type );
  end if;
  
end intrinsic;
