/* This file contains the functions for the recognition procedure for the symmetric
    square of Omega(d,q) (Omega+, Omega-, and Omega in odd dim) */

import "smalldimreps.m":__funcSLdqToSymSquare, __funcSymSquareToSLdq, 
SolveSymSquareDimEq, funcpos_symsquare, funcposinv_symsquare, BasisMatrixForSymSquareOmega;

import "auxfunctions.m": MyDerivedGroupMonteCarlo, IsSimilarToScalarMultiple, 
    SplitTensor, IsSimilarModScalar;

import "symsquare_omega_aux.m":TestBasisOmega, OmegaBasisFromComponents, 
    BuildBasisOmega, TypeOfSymSquareOmega, SymSquareOmegaBasisWithOmegaMinus, 
    AssignOmegaBasisFromComponents;


AddAttribute( GrpMat, "BasisMatrixFromComponents" );

// The main function 

RecogniseSymSquareWithTensorDecompositionOmegaFunc := function( G : type := "Omega+", 
    CheckResult := true )
    
    cputm := Cputime();
          
    // first getting the parameters
    q := #CoefficientRing( G ); 
    _, p := IsPrimePower( q );
    dimg := Dimension( G );
    G0 := G; //keeping the original group
    z := PrimitiveElement( GF( q ));
    
    // the natural dimension of G
    dim := SolveSymSquareDimEq( dimg : type := type );
    // see if char divides dimension; 
    pdivdim := dim mod p eq 0;    

    vprint SymSquareVerbose: "# Recog SymSquare dim", dim;
    
    /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      
    eiglim1 := Ceiling((2/9)*dim^2); // lower limit for eigenspace dim
    eiglim2 := Floor((1/4)*dim^2); // upper limit for eigenspace dim

    // normally use 10 generators for 
    NrGensCentInv := 10; 
    
    /* completion checking function required for the calculation of the 
        centralizer of an involution */
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    /* The following internal function checks if an involution gives the right 
       decomposition for the procedure. 

       We want that the smaller-dimensional components shouldn't have dimensions
       that are divisible by p.

       Also, the three larger-dimensional components preserve orthogonal forms and 
       we want the types of these forms as prescribed. 
       
       The argument mins is the list of minimal C-submodules in M where C is the centralizer 
       of an involution. It typically has four such mininals, U, V, U tensor V and a 
       1-dimensional W. If p divides dim, then the 1-dimensional component does not occur. */

    __isonefactoromegaminus := function( mins )
        
        q := #CoefficientRing( mins[1] );
        // first get the larger-dimensional minimals
        mins := [ x : x in mins | Dimension( x ) gt 1 ];

        // get their dimensions and see which correspond to symmetric square
        dims := [ Dimension( x ) : x in mins ];
        dims0 := [ SolveSymSquareDimEq( x : type := type ) : x in dims ];

        /* find which component is U tensor V. we set up the list inds such that 
            inds[1] and inds[2] point to U and V, and inds[3] to U tensor V. */
        if 0 in dims0 then 
            pos_tensor := Position( dims0, 0 );
            inds := <Remove( [1,2,3], pos_tensor )[1],Remove( [1,2,3], pos_tensor )[2],
                    pos_tensor>;  
        else 
            inds := [ <x,y,z> : x,y,z in [1..3] | x lt y and dims0[x]*dims0[y] eq dims[z]];
            assert #inds eq 1;
            inds := inds[1];
        end if;

        // they preserve symmetric bilinear forms; get the types
        types := < ClassicalForms( ActionGroup( mins[inds[1]] ))`formType,
                ClassicalForms( ActionGroup( mins[inds[2]] ))`formType >;
       // types := [ ClassicalForms( ActionGroup( x ))`formType : x in mins ];

        goodtypes := case< type | 
                    "Omega+": {<TypeOfSymSquareOmega( "Omega+", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega+", dims0[inds[2]],q)>},
                    "Omega-": {<TypeOfSymSquareOmega( "Omega+", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega-", dims0[inds[2]],q)>,
                                <TypeOfSymSquareOmega( "Omega+", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega-", dims0[inds[2]],q)>},
                    "Omega": {<TypeOfSymSquareOmega( "Omega+", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega", dims0[inds[2]],q)>,
                                <TypeOfSymSquareOmega( "Omega", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega+", dims0[inds[2]],q)>
                                ,
                                <TypeOfSymSquareOmega( "Omega-", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega", dims0[inds[2]],q)>,
                                <TypeOfSymSquareOmega( "Omega", dims0[inds[1]],q),
                                TypeOfSymSquareOmega( "Omega-", dims0[inds[2]],q)>
                                
                                },
                    default: false >;

        //print types, goodtypes, dims0; 

        return (dims0[inds[1]] mod p eq 0) or 
               (dims0[inds[2]] mod p eq 0) or 
               not types in goodtypes;
    end function;

    gensC := []; gensCD := [];
    numberofminsubs := case< pdivdim | true: 3, false: 4, default: false >;
     
    count := 0;
    repeat  
    count := count+1;
    if count mod 10 eq 0 then print count, "tries!!!!!!!!!!!!!!"; end if;

        tryagain := false;
        if not assigned inv then 
            _, inv := RandomElementOfOrder( G, 2 );
            de := Dimension( Eigenspace( inv, -1 ));
            if not de in [eiglim1..eiglim2] then 
                gensC := [];
                gensCD := [];
                delete inv; 
                tryagain := true;
                continue;
            end if;
        end if;         
        assert assigned inv;
        C := CentraliserOfInvolution( G, inv : 
                     CompletionCheck := __compcheck );  
        CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv );
        gensC := gensC cat GeneratorsSequence( C );
        gensCD := gensCD cat GeneratorsSequence( CD );
        C := sub< Universe( gensC ) | gensC >;
        CD := sub< Universe( gensCD ) | gensCD >;
        M := GModule( CD );
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )]; 
        if #mins ne numberofminsubs or  &+[ Dimension( x ) : x in mins ] ne dimg or 
                __isonefactoromegaminus( mins ) then
            delete inv;
            gensC := [];
            gensCD := [];
            tryagain := true;
            continue;
        end if;
    until  not tryagain and #mins eq numberofminsubs and 
            &+[ Dimension( x ) : x in mins ] eq dimg;

    vprint SymSquareVerbose: "#   Cent comput dim", dim, "took ", 
      Cputime()-cputm, #gensC, "gens used.";
      
      /* The C-module V splits into three components.
         Two components are isomorphic to sym square U and sym square W, 
         respectively. The third is isomorphic to U tensor W.  
         The two sym squares lie in the one eigenspace of inv. The tensor 
         lies in the minus one eigenspace. */
        

    // find which component lies in the minus one or the plus one eigenspace  
    mplus := [ mins[x] : x in [1..#mins] | 
               (M!mins[x].1)^inv eq M!mins[x].1 and 
               Dimension( mins[x] ) ge 2 ];
    mminus := [ mins[x] : x in [1..#mins] | 
                (M!mins[x].1)^inv eq -M!mins[x].1 and 
                Dimension( mins[x] ) ge 2 ];
    
    if not pdivdim then
        monedim := [ mins[x] : x in [1..#mins] | Dimension( mins[x] ) eq 1 ][1];
    end if;
        
    // we select the two irreducible exterior square components
    if #mplus eq 2 then
        mH := mplus[1]; mK := mplus[2]; mT := mminus[1];
    else 
        mH := mminus[1]; mK := mminus[2]; mT := mplus[1];
    end if;      

    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );
    dH := SolveSymSquareDimEq( dimH : type := type ); 
    dK := SolveSymSquareDimEq( dimK : type := type ); 
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
    tf := TensorFactors( aT );
    ft1 := ClassicalForms( tf[1] : Scalars := true )`formType;
    ft2 := ClassicalForms( tf[2] : Scalars := true )`formType;
  
    if ft1 eq "orthogonalplus" or <ft1,ft2> eq <"orthogonalminus","orthogonalcircle"> then
        t1 := 1; t2 := 2;
        pm := IdentityMatrix( GF( q ), dT );
    else
        t1 := 2; t2 := 1;
        pm := PermutationMatrix( GF( q ), Sym( dT )!
        Flat( [[z+k*dK : k in [0..dH-1]] : z in [1..dK]] ));
    end if; 
    
    if ft1 eq "symplectic" then 
        print "SYMPLECTIC!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"; 
        symp := true;
    else 
        symp := false;
    end if;

    dt1 := Dimension( tf[t1] ); 
    dt2 := Dimension( tf[t2] );

    // get the dimensions of the tensor factors
    
    /* the dimensions dt1 and dt2 of the tensor factors must be equal to 
       dH and dK in this order. If not, we must swap H and K. */
                                  
    if dt1 ne dH then 
        temp := dH; dH := dK; dK := temp;
        temp := dimH; dimH := dimK; dimK := temp;
        temp := ah; ah := ak; ak := temp;
        temp := mH; mH := mK; mK := temp;
        pm := pm^-1;
    end if;
    
    // calculate the basis for aT that reflects the tensor structure
    
    tbas := pm^-1*TensorBasis( aT )^-1;
    
    // set of the maps from aT into the tensor components
    
    ch := pmap< GL( dimg, q ) -> GL( dH, q ) | x :-> SplitTensor( 
                  tbas*x@at*tbas^-1, dH, dK )[1] >;
    
    ck := pmap< GL( dimg, q ) -> GL( dK, q ) | x :-> SplitTensor( 
                  tbas*x@at*tbas^-1, dH, dK )[2] >;

    //if pm ne pm^0 then return <TensorBasis( aT ),pm,gensCD,at>; end if;    
    
    gens1h := [ x@ch : x in gensCD ];
    gens1k := [ x@ck : x in gensCD ];
    
    /* The groups generated by gens1h and gens1k are isomorphic to 
       Omega( dH, q ) and Omega( dK, q ). They need to be conjugated into
       the right copy of Omega( d*, q ) by finding the symmetric     
       bilinear form that it preserves. */
      
    /* the groups generated by gens1h and gens1k preseve an symmetric
       bilin form possibly modulo minus one. */

    formh := ClassicalForms( sub< Universe( gens1h ) | gens1h > : 
                   Scalars := true );
    formk := ClassicalForms( sub< Universe( gens1k ) | gens1k > : 
                   Scalars := true );

    sch := formh`scalars;
    sck := formk`scalars;
    typeh := case< formh`formType | "orthogonalplus": "Omega+", 
                    "orthogonalminus": "Omega-", 
                    "orthogonalcircle": "Omega",  
                    default: false >;
    
    typek := case< formk`formType | "orthogonalplus": "Omega+", 
                    "orthogonalminus": 
                    "Omega-", 
                    "orthogonalcircle": "Omega",
                    default: false >;

    // if both are Omega-, then make them Omega+
/*    if typeh eq "Omega-" and typek eq "Omega-" then print "both Omega-";
        typeh := "Omega+"; typek := "Omega+"; print "CHANGE TYPEH!!!!!!!!!";
    elif typeh eq "Omega-" and typek eq "Omega" then 
        typeh := "Omega+"; print "CHANGE TYPEH!!!!!!!!!";
    end if;
*/
                   
    // if a generator preseves the form module -1, then this is fixed.
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

    if typeh eq "Omega-" and typek eq "Omega" then
        formcircle := ZeroMatrix( GF( q ), dK );
        issq1 := IsSquare( GF(q)!(-1)^(dim div 2)*(1/2));
        issq2 := IsSquare( GF(q)!(-1)^(dK div 2)*(1/2)*
                Determinant( ClassicalForms( OmegaMinus( dH, q ))`bilinearForm));

        if issq1 eq issq2 then
            ww := 1/2;
        else 
            ww := 1/2*PrimitiveElement( GF( q ));
        end if;

        for i in [1..dK div 2] do 
            formcircle[i,dK-i+1] := 1; formcircle[dK-i+1,i] := 1;
        end for;
        
        formcircle[dK div 2+1, dK div 2+1] := ww;
        trmat := TransformForm( formcircle, "orthogonalcircle" )^-1;
    
        Tk := GL(dK,q)!(Tk*trmat);
    else 
        ww := 1/2;
    end if;
    
    AssignOmegaBasisFromComponents( ~G, dH, dK, GF( q ) : type := type, 
                                                          typeh := typeh, 
                                                          typek := typek,
                                                          ww := ww );

    //return sub< Universe( gens1k ) | gens1k >, Tk;
    
    tbas := TensorProduct( Th^-1, Tk^-1 )*tbas;
    gens1h := [ x^Th : x in gens1h ];
    gens1k := [ x^Tk : x in gens1k ];

    gens1h := [ GL(dimH,q)!__funcSLdqToSymSquare( x : type := typeh ) : 
                x in gens1h ];
    gens2h := [ x@ah : x in gensCD ];
    gens1k := [ GL(dimK,q)!__funcSLdqToSymSquare( x : type := typek, ww := ww ) : 
                x in gens1k ];
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

    basT := [ M!(&+[tbas[j][i]*Basis( mT )[i] : 
                    i in [1..dT]]) : j in [1..dT]];

    if not pdivdim then
        basOneDim := [ M!(Basis( monedim )[1])]; wH := basOneDim[1];
    else 
        basOneDim := [ Zero( M )];
    end if;

   // return basH, basK, basT, basOneDim;
            
    /* we place the basis vectors computed in bas1 and bas2 into their place
       in the basis of V */
    //bas1 := BuildBasisOmega( basH, basK, basT : wH := basOneDim[1] );
    bas := BuildBasisOmega( G, basH, basK, basT : type := type, 
                                               typeh := typeh, 
                                               typek := typek,
                                               wH := basOneDim[1], 
                                               ww := ww );
    tr := GL( dimg, q )!bas;
    g := sub< SL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
    form := ClassicalForms( g )`bilinearForm;
    
    posT := funcpos_symsquare( dim, dim-dH div 2, dim : type := type );
    if pdivdim then posT := posT-1; end if;
    if not IsSquare( 2*form[dH div 2+1,posT] ) then
        if typeh eq "Omega+" then 
            for i in [1..#basH] do 
                pos := funcposinv_symsquare( dH, i : type := typeh );
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

        if typeh eq "Omega-" then  
            trh := IdentityMatrix( GF( q ), dH );
            for i in [1..dH div 2 -1 ] do 
                trh[i,i] := -1;
            end for;

            m2 := Matrix( GF( q ), 2, 2, [-1,0,0,-1]);
            t2 := TransformForm( m2, "orthogonalminus" );
            
            trh[dH div 2,dH div 2] := t2[1,1]; trh[dH div 2,dH div 2+1] := t2[1,2];
            trh[dH div 2+1,dH div 2] := t2[2,1]; trh[dH div 2+1,dH div 2+1] := t2[2,2];

            bas := BasisMatrixForSymSquareOmega( "Omega-", dH, GF(q));
            trh1 := bas*__funcSLdqToSymSquare( trh )*bas^-1;
            newbasH := [ &+[ trh1[i,j]*basH[j] : j in [1..#basH]] : 
                            i in [1..#basH]];
            basH := newbasH;

            trT := TensorProduct( trh, IdentityMatrix( GF( q ), dK ) );
            newbasT := [ &+[ trT[i,j]*basT[j] : j in [1..#basT]] : i in [1..#basT] ];
            basT := newbasT;
        end if;
    end if; 

   bas := BuildBasisOmega( G, basH, basK, basT : type := type, 
                                              typeh := typeh, 
                                              typek := typek,
                                              wH := basOneDim[1], 
                                              ww := ww );
   tr := GL( dimg, q )!bas;
   //return CD, tr;
   g := sub< SL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
   form := ClassicalForms( g )`bilinearForm; 
   vH := Sqrt( form[1,dimg] )^-1; 
    
   posK1 := funcpos_symsquare( dim, (dH div 2)+1,(dH div 2)+2 : type := type );
   
   if type eq "Omega-" and dH div 2 + 2 eq dim div 2 then 
       posK2 := funcpos_symsquare( dim, (dH div 2)+2,dim-(dH div 2) : type := type );
   else
       posK2 := funcpos_symsquare( dim, dim-(dH div 2)-1,dim-(dH div 2) : type := type );
   end if;

   if pdivdim then posK2 := posK2 - 1; end if;

   vK := Sqrt( 2*form[posK1,posK2] )^-1; 
   posT := funcpos_symsquare( dim, dim-dH div 2, dim : type := type );
   if pdivdim then posT := posT -1; end if;
   vT := Sqrt( 2*form[dH div 2+1,posT] )^-1;   
      
   for i in [1..#basH] do 
       basH[i] := vH*basH[i];
   end for;
   
   for i in [1..#basK] do
       basK[i] := vK*basK[i];
   end for;
       
   for i in [1..#basT] do
       basT[i] := vT*basT[i];
   end for;
   
   bas := BuildBasisOmega( G, basH, basK, basT : type := type, 
                                              typeh := typeh,
                                              typek := typek,
                                              wH := basOneDim[1], 
                                              ww := ww ); 
   g := sub< SL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
   //return CD, bas;

   if not pdivdim then 

        form := ClassicalForms( g )`bilinearForm;
        b := form[dim,dim];
        assert form[1,dimg] eq 1 and form[2,dimg-1] eq 1/2;
        P<x> := PolynomialRing( GF( q ));

        if type eq "Omega+" then 
        
            auxmat := BasisMatrixForSymSquareOmega( "Omega+", dH+dK, GF(q) )*
            OmegaBasisFromComponents( G )^-1;
            u := auxmat[dim,dimg]; v := auxmat[dim,dimg+1];
            pol := -b+1+(u-v)*(x-1)+(u^2*(dH div 2)/2+v^2*(dK div 2)/2)*(x-1)^2;
        
        elif type eq "Omega-" then
        
            auxmat := BasisMatrixForSymSquareOmega( "Omega-", dH+dK, GF(q) )*
            OmegaBasisFromComponents( G )^-1;
            u := auxmat[dim,dimg]; v := auxmat[dim,dimg+1];
            pol := -b+3/2+(u-v)*(x-1)+(u^2*(dH div 2)/2+v^2*(dK div 2)/2)*(x-1)^2;
        
        elif type eq "Omega" and typeh eq "Omega+" then
        
            auxmat := BasisMatrixForSymSquareOmega( "Omega", dH+dK, GF(q) )*
            OmegaBasisFromComponents( G )^-1;
            u := auxmat[dim,dimg]; v := auxmat[dim,dimg+1]; 
            pol := -b+3/2 + 2*u*(x-1)*1/2+2*v*(x-1)*(-1/2)+u^2*(x-1)^2*(dH div 2)/2+
            v^2*(x-1)^2*(((dK-1) div 2)/2+1/4);
        
        elif type eq "Omega" and typeh eq "Omega-" then
                
            auxmat, vals := 
                        OmegaBasisFromComponents( G );
            aa := vals[1]; awH := vals[2]; awK := vals[3]; 
            wHwH := vals[4]; wKwK := vals[5];
            
            auxmat := BasisMatrixForSymSquareOmega( "Omega", dH+dK, GF(q) )*auxmat^-1;
            u := auxmat[dim,dimg]; v := auxmat[dim,dimg+1]; 
            // error(1);
            //aa := 1; awH := 6; awK := 4; wHwH := 5; wKwK := 3;
            pol := -b+aa+2*u*(x-1)*awH+2*v*(x-1)*awK+u^2*(x-1)^2*wHwH+v^2*(x-1)^2*wKwK;
        
        end if;

        roots := AllRoots( pol ); 
        basOneDim[1] := roots[1,1]^-1*basOneDim[1]; 

    end if;

   v, coeffs := TestBasisOmega( G, basH, basK, basT, basOneDim[1], basOneDim[1], G0 :
                                type := type, 
                                typeh := typeh,
                                typek := typek, 
                                ww := ww );  
   assert v;     

   bas := BuildBasisOmega( G, basH, basK, basT : type := type, 
                                              typeh := typeh,
                                              typek := typek,
                                              wH := basOneDim[1], 
                                              scalars := coeffs, 
                                              ww := ww );
   tr := GL( dimg, GF( q ))!bas;
    // construct the maps between GL(dim,q) and G
    
    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToSymSquare( x : type := type )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> GL( dim, q )!__funcSymSquareToSLdq( x^(tr^-1) : type := type ) >;
    
    vprint SymSquareVerbose: "# Recog SymSquare dim", dim, "took ", 
      Cputime()-cputm;
    
    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        gens := [ x@b : x in GeneratorsSequence( G )];
        M1 := GModule( sub< GL( dimg, q ) | 
                      [ __funcSLdqToSymSquare( x : type := type ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
	return false, _, _, _;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;
        
    return true, a, b, tr;
end function;