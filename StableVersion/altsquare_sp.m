/* The following functions perform AltSquare recognition for the symplectic
   group. It follows the tensor decomposition method. */
   
import "smalldimreps.m":SolveAltSquareDimEq, funcpos_altsquare, 
funcposinv_altsquare, __funcSLdqToAltSquare, __funcAltSquareToSLdq;

import "auxfunctions.m": MyDerivedGroupMonteCarlo, 
  IsSimilarModScalar, SplitTensor, InvolutionWithProperty;
  
import "sp_aux.m": BuildBasis, TestBasis, SpTransformMatrix;

/* The recognition procedure for the exterior square representations
   of the symplectic groups. */
      
RecogniseAltSquareWithTensorDecompositionSp := function( G : 
                                               CheckResult := true )
                                               
    cputm := Cputime(); 
    
    // set up some standard things
    q := #CoefficientRing( G ); 
    _, p := IsPrimePower( q );
    dimg := Dimension( G );
    // the natural dimension of G
    dim := SolveAltSquareDimEq( dimg : type := "Sp" );
    pdividesd := dim mod p eq 0;
    if dim mod p eq 0 then 
        chardivdim := true; 
    else 
        chardivdim := false; 
    end if;
        
    assert (not chardivdim and dim*(dim-1)/2-1 eq dimg) or 
      (chardivdim and dim*(dim-1)/2-2 eq dimg);
    
    if dim lt 8 then
        print "AltSquare recognition is not implemented for these parameters";
        error( -2 );
    end if; 
    
    z := PrimitiveElement( GF( q ));
    
    G0 := G;  // we keep the orginal G
    
    // the group preserves a symmetric bilinear form
    form0 := ClassicalForms( G0 )`bilinearForm;    
     
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim;
    
   /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      

    //c1 := 0.2; c2 := 0.3; 
    c1 := 2/9; c2 := 1/4;

    eiglim1 := case< dim | 6: 9, 14: 40, default: c1*dim^2 >; 
    // lower limit for eigenspace dim
    eiglim2 := case< dim | 6: 9, default: c2*dim^2 >; 
    // upper limit for eigenspace dim

    // set up property function for InvolutionWithProperty  
    propfunc := function( x )
        dmin := Dimension( Eigenspace( x, -1 ));
        dplus := Dimension( Eigenspace( x, 1 ));

        //return dmin ge 6 and dplus ge 6;
        return dmin ge eiglim1 and dmin le eiglim2;
    end function;
        
    // completion checking function

    NrGensCentInv := 10; 
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    gensC := []; gensCD := [];
    
    /* the following block will find an involution with the right
      minus one eigenspace and sets up its centralizer */      
      
    nocomponents := case< chardivdim | true: 3, default: 4 >;


    __dimcheck := function( dims )

        if #dims ne 3 then return true; end if;
        dims0 := [ SolveAltSquareDimEq( x : type := "Sp" ) : x in dims ];
        notz := [ i : i in [1..3] | dims0[i] ne 0 ];
        if #notz ne 2 then print dims, "rejected"; return false; end if;
        ind := [ x : x in [1..3] | not x in notz ][1];

        res := dims0[notz[1]]*dims0[notz[2]] eq dims[ind];

        if not res then print dims, "rejected!!!!!!!!!!!!!!!!!!!!"; end if;

        return res;
    end function; 

    repeat   
        if not assigned inv then 
            inv := InvolutionWithProperty( G, propfunc );
        end if; 
        C := CentraliserOfInvolution( G, inv : 
                     CompletionCheck := __compcheck );  
        CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv,
                      DerivedLength := 3 );
        gensCD := gensCD cat GeneratorsSequence( CD );
        CD := sub< Universe( gensCD ) | gensCD >;
        
        M := GModule( CD );
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )];
            
        if #mins ne nocomponents or &+[ Dimension( x ) : x in mins ] lt dimg or 
           not __dimcheck([ Dimension( x ) : x in mins ]) then
            delete inv, C, CD;
            gensCD := [];
            mins := [];
            continue;
        end if;
    until  #mins eq nocomponents and &+[ Dimension( x ) : x in mins ] eq dimg;
    vprint SymSquareVerbose: "#   Cent comput dim", dim, "took ", 
      Cputime()-cputm, #gensCD, "gens used.";
      
      /* The C-module V splits into four components.
         There is a one-dimensional component. 
         Two components are isomorphic to the 
         large irreducible factors of alt square U and alt square W, 
         respectively. The third is isomorphic to U tensor W.
         The two alt squares lie in one of the eigenspaces of inv. The tensor 
         lies in the other eigenspace. */
      
    // find which component lies in the minus one or the plus one eigenspace  
    mplus := [ mins[x] : x in [1..#mins] | 
               (M!mins[x].1)^inv eq M!mins[x].1 and 
               Dimension( mins[x] ) ge 2 ];
    mminus := [ mins[x] : x in [1..#mins] | 
                (M!mins[x].1)^inv eq -M!mins[x].1 and 
                Dimension( mins[x] ) ge 2 ];
    
    // in the case of Sp and char ndiv dim there is a one-dimensional component
    if not chardivdim then
        monedim := [ mins[x] : x in [1..#mins] | Dimension( mins[x] ) eq 1 ][1];
    end if;
        
    // we select the two irreducible exterior square components
    if #mplus eq 2 then
        mH := mplus[1]; mK := mplus[2]; mT := mminus[1];
    else 
        mH := mminus[1]; mK := mminus[2]; mT := mplus[1];
    end if;      
    
    // set up the variables for the dimensions of H, K and T 
    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );
    dH := SolveAltSquareDimEq( dimH : type := "Sp" ); 
    dK := SolveAltSquareDimEq( dimK : type := "Sp" ); 
    dT := dH*dK;
    assert Dimension( mT ) eq dT; // print dH, dK;
    
    // set up the projections into the components
    
    ah := pmap< GL( dimg, q ) -> GL( dimH, q ) | 
          x :-> GL( dimH, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    ak := pmap< GL( dimg, q ) -> GL( dimK, q ) | 
          x :-> GL( dimK, q )![ Eltseq( mK!((M!b)^x )) : b in Basis( mK )]>;
    
    at := pmap< GL( dimg, q ) -> GL( dimT, q ) | 
          x :-> GL( dimT, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;
    
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
 
    gens1h := [ x@ch : x in gensCD ];
    gens1k := [ x@ck : x in gensCD ];
    
    /* The groups generated by gens1h and gens1k are isomorphic to 
       Sp( dH, q ) and Sp( dK, q ). They need to be conjugated into
       the right copy of Sp( d*, q ) by finding the alternating     
       bilinear form that it preserves. */
      
    /* the groups generated by gens1h and gens1k preseve an alternating
       bilin form possibly modulo minus one. */
    sch := ClassicalForms( sub< Universe( gens1h ) | gens1h > : 
                   Scalars := true )`scalars;
    sck := ClassicalForms( sub< Universe( gens1k ) | gens1k > 
                   : Scalars := true )`scalars;
                   
    // if a generator preseve the form module -1, then this is fixed.
    for i in [1..#sch] do
        if sch[i] ne 1 then
           gens1h[i] := gens1h[i]*ScalarMatrix( GF( q ), dH, 
                             Sqrt( GF( q )!(sch[i]))^-1);
           gens1k[i] := gens1k[i]*ScalarMatrix( GF( q ), dK, 
                                Sqrt( GF( q )!(sck[i]))^-1 );
        end if;
    end for;
    
    /* now sub< gens1h > and sub< gens1k > preserve the form. 
       we calculate the transformation matrices  and conjugate the 
       generators to the right form. */
      
    Th := TransformForm( sub< Universe( gens1h ) | gens1h > );
    Tk := TransformForm( sub< Universe( gens1k ) | gens1k > );
    
    tbas := TensorProduct( Th^-1, Tk^-1 )*tbas;
    gens1h := [ x^Th : x in gens1h ];
    gens1k := [ x^Tk : x in gens1k ];
    
    /* we calculate the matrices in the irreducible exterior square
       representation of Sp( d, q ) */
      
    gens1h := [ GL(dimH,q)!__funcSLdqToAltSquare( x : type := "Sp") : 
                x in gens1h ];
    gens2h := [ x@ah : x in gensCD ];
    
    gens1k := [ GL(dimK,q)!__funcSLdqToAltSquare( x : type := "Sp" ) : 
                x in gens1k ];
    gens2k := [ x@ak : x in gensCD ];
    
    /* we need to identify the two tensor components with the two 
       Sp components obtained earlier. */
    
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
    
    M1H := GModule( sub< GL( dimH, q ) | gens1h >);
    M2H := GModule( sub< GL( dimH, q ) | gens2h >);
    
    v, trmh := IsIsomorphic( M1H, M2H ); assert v;
    
    M1K := GModule( sub< GL( dimK, q ) | gens1k >);
    M2K := GModule( sub< GL( dimK, q ) | gens2k >);
    
    v, trmk := IsIsomorphic( M1K, M2K ); assert v;
    
    // now we can build the bases of H, K, and T
      
    basH := [ M!(&+[trmh[j][i]*Basis( mH )[i] : 
                    i in [1..dimH]]) : j in [1..dimH]];
    
    basK := [ M!(&+[trmk[j][i]*Basis( mK )[i] : 
                    i in [1..dimK]]) : j in [1..dimK]];
    
    basT := [ M!(&+[tbas[j][i]*Basis( mT )[i] : 
                    i in [1..dT]]) : j in [1..dT]];
    
    if not chardivdim then
        basOneDim := [ M!(Basis( monedim )[1])];
    else
        basOneDim := [ Zero( M )];
    end if;

    bas := BuildBasis( basH, basK, basT : wH := basOneDim[1] );
    tr := GL( dimg, q )!bas;
    
    g := sub< SL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
    form := ClassicalForms( g )`bilinearForm;
    
    posT := funcpos_altsquare( dim, dim, dim-dH div 2 : type := "Sp" );
    if pdividesd then posT := posT-1; end if;
      
    if not IsSquare( form[dH div 2,posT] ) then 
        for i in [1..#basH] do 
                pos := funcposinv_altsquare( dH, i : type := "Sp" );
            if pos[1] le dH div 2 and pos[2] le dH div 2 then
                basH[i] := z^2*basH[i];
            elif pos[1] le dH div 2 and pos[2] gt dH div 2 then
                basH[i] := z*basH[i];
           end if;
       end for;
       
       for i in [1..#basT/2] do 
           basT[i] := z*basT[i];
       end for;
   end if; 
   
   bas := BuildBasis( basH, basK, basT : wH := basOneDim[1] );
   tr := GL( dimg, q )!bas;
   
   g := sub< SL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
   form := ClassicalForms( g )`bilinearForm; 
   
   vH := Sqrt( form[1,dimg] )^-1; 
   posK1 := funcpos_altsquare( dim, dH/2+1,dH/2+2 : type := "Sp" );
   posK2 := funcpos_altsquare( dim, dim-dH/2-1,dim-dH/2 : type := "Sp" );
   if pdividesd then posK2 := posK2 - 1; end if;
   vK := Sqrt( form[posK1,posK2] )^-1; 
   posT := funcpos_altsquare( dim, dim, dim-dH div 2 : type := "Sp" );
   if pdividesd then posT := posT - 1; end if;
   vT := Sqrt( form[dH div 2,posT] )^-1;  
      
   for i in [1..#basH] do 
       basH[i] := vH*basH[i];
   end for;
   
   for i in [1..#basK] do
       basK[i] := -vK*basK[i];
   end for;

       
   for i in [1..#basT] do
       basT[i] := vT*basT[i];
   end for;
   
   bas := BuildBasis( basH, basK, basT : wH := basOneDim[1] ); 
         
   g := sub< SL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
   form := ClassicalForms( g )`bilinearForm; 
   
   if not pdividesd then
   
       b := form[dim-1,dim-1];
       auxmat := SpTransformMatrix( dH, dK, GF( q ));
       vec := (auxmat^-1)[1]-(auxmat^-1)[dim div 2];
       u := vec[dH div 2]; v := vec[dim div 2];
       
       P<x> := PolynomialRing( GF( q ));
       pol := -b-2-(2*u-2*v)*(x-1)-(u^2*(dH div 2)+v^2*(dK div 2))*(x-1)^2;
       roots := AllRoots( pol );
       
       basOneDim[1] := roots[1,1]^-1*basOneDim[1];
              
   end if;

   v, coeffs := 
     TestBasis( basH, basK, basT, basOneDim[1], basOneDim[1], G0 );  
   assert v; 

   vprint SymSquareVerbose: "# Recog AltSquare dim", dim, "took ", 
     Cputime()-cputm;
   
   tr := BuildBasis( [ coeffs[1]*x : x in basH ],
                      [ coeffs[2]*x : x in basK ],
                      [ coeffs[3]*x : x in basT ] :
                 wH := coeffs[4]*basOneDim[1] );
   
   tr := GL( dimg, q )!tr;
    
   // construct the maps between GL(dim,q) and G
    
   a := map< GL( dim, q ) -> GL( dimg, q ) | 
        x :-> GL( dimg, q )!__funcSLdqToAltSquare( x : type := "Sp" )^tr >;
    
   b := pmap< GL( dimg, q ) -> GL( dim, q ) |
        x :-> GL( dim, q )!__funcAltSquareToSLdq( x^(tr^-1) : 
                type := "Sp" ) >;

   
   // if CheckResult is set, we perform a check
   if CheckResult then
       vprint SymSquareVerbose: "# Checking final result";
       try
         gens := [ x@b : x in GeneratorsSequence( G )];
       catch e
         error( "calculation of preimages failed" ); 
       end try;
       M1 := GModule( sub< GL( dimg, q ) | 
                     [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), dim )!x 
                             : type := "Sp" ) 
                       : x in gens ]>);
       if not IsIsomorphic( M1, GModule( G )) then
           vprint SymSquareVerbose: "# Check failed.";
           error( "module isomorphism check failed");
       end if;
       vprint SymSquareVerbose: "# Check passed.";
   end if; 
    
   return true, a, b, tr; 
end function;