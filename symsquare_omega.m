/* This file contains the functions for the recognition procedure for the symmetric
    square of Omega(d,q) (Omega+, Omega-, and Omega in odd dim) */

import "smalldimreps.m":__funcSLdqToSymSquare, __funcSymSquareToSLdq, 
SolveSymSquareDimEq, funcpos_symsquare, funcposinv_symsquare, BasisMatrixForSymSquareOmega;

import "auxfunctions.m": MyDerivedGroupMonteCarlo, IsSimilarToScalarMultiple, 
    SplitTensor, IsSimilarModScalar, TransformToForm, OldFormOmegaMinus;

import "symsquare_omega_aux.m":TestBasisOmega, OmegaBasisFromComponents, 
    BuildBasisOmega, TypeOfSymSquareOmega, SymSquareOmegaBasisWithOmegaMinus, 
    AssignBasisFromComponents;

// The main function 
forward RecogniseSymSquareOmegaFunc;

RecogniseSymSquareOmegaFunc := function( G : 
                            type := "Omega+", 
                            Method := "Recursion", 
                            RecursiveCall := false )
    
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
      
    eiglim1 := case< <type,dim> | <"Omega",9>: 20,
                                  //<"Omega",11>: 30,
                                  <"Omega-",14>: 40,
                                  <"Omega+",14>: 40,
                    default: Ceiling((2/9)*dim^2)>; // lower limit for eigenspace dim

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
        return (dims0[inds[1]] mod p eq 0) or 
               (dims0[inds[2]] mod p eq 0) //or 
               //not types in goodtypes;
               ;
    end function;

    gensC := []; gensCD := [];
    numberofminsubs := case< pdivdim | true: 3, false: 4, default: false >;
     
    count := 0;
    repeat  
    count := count+1;;

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

    // we want dH to be even-dimensional. if it is not, then we swap

    if IsOdd( dH ) then 
        t := dH; dH := dK; dK := t;
        t := dimH; dimH := dimK; dimK := t;
        t := mH; mH := mK; mK := t;
    end if;        

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

   if dH lt 9 or dK lt 9 or <dK,p> eq <9,5> or <dH,p> eq <10,3> 
        or <dK,p> eq <10,3> then 
        Method := "Tensor"; 
   end if;

   if Method eq "Recursion" then 
        // ************* RECURSIVE CODE STARTS HERE ****************
        aH := sub< GL( dimH, q ) | [ x@ah : x in gensCD ]>;
        aK := sub< GL( dimK, q ) | [ x@ak : x in gensCD ]>;
        
        //get the type of the component H
        v1, typeh := LieType( aH, p ); assert v1;
        typeh := case< typeh[1] | "D": "Omega+", "2D": "Omega-", "B": "Omega", 
                        default: false >;

        // this determines the type of the component K
        if type eq "Omega+"  and typeh eq "Omega+" then
            typek := "Omega+";
        elif type eq "Omega+" and typeh eq "Omega-" then 
            typek := "Omega-";
        elif type eq "Omega-" and typeh eq "Omega+" then 
            typek := "Omega-";
        elif type eq "Omega-" and typeh eq "Omega-" then 
            typek := "Omega+";
        elif type eq "Omega" then 
            typek := "Omega";
        end if;

        // if H is Omega- and K is Omega+ then swap
        if typeh eq "Omega-" and typek eq "Omega+" then 
            t := dH; dH := dK; dK := t;
            t := dimH; dimH := dimK; dimK := t;
            t := mH; mH := mK; mK := t;
            t := ah; ah := ak; ak := t;
            t := aH; aH := aK; aK := t;
            typeh := "Omega+"; typek := "Omega-";
        end if;        

        vprint SymSquareVerbose: "# types of components are ", typeh, typek, "of dims", 
                    dH, dK;

        // the recursive call to recognise the smaller-dimensional sym squares aH and aK
    
        vh, b1, c1, bas1 := RecogniseSymSquareOmegaFunc( aH : type := typeh, RecursiveCall := true );
        vk, b2, c2, bas2 := RecogniseSymSquareOmegaFunc( aK : type := typek, RecursiveCall := true );
        
        assert vh and vk;

        if typeh eq "Omega-" and typek eq "Omega" then
            
            formcircle := ZeroMatrix( GF( q ), dK );
            issq1 := IsSquare( GF(q)!(-1)^(dim div 2)*(1/2));
            issq2 := IsSquare( GF(q)!(-1)^(dK div 2)*(1/2)*
                                (-1)^((dH - 2) div 2+1)*Nonsquare( GF( q )));
                    //Determinant( ClassicalForms( OmegaMinus( dH, q ))`bilinearForm));

            if issq1 eq issq2 then
                ww := 1/2;
            else 
                ww := 1/2*PrimitiveElement( GF( q ));
            end if;

            for i in [1..dK div 2] do 
                formcircle[i,dK-i+1] := 1; formcircle[dK-i+1,i] := 1;
            end for;
            
            formcircle[dK div 2+1, dK div 2+1] := ww;
            Tk := TransformForm( formcircle, "orthogonalcircle" );

            g12 := Omega( dK, q );
            gw := g12^(Tk^-1);
            m12 := GModule( sub< GL( dimK, q ) | [ __funcSLdqToSymSquare( x : type := "Omega", ww := 1/2 ) : 
                                x in GeneratorsSequence( g12 )] >); 
            mw := GModule( sub< GL( dimK, q ) | [ __funcSLdqToSymSquare( x : type := "Omega", ww := ww ) : 
                                x in GeneratorsSequence( gw )] >);     
            v, tr := IsIsomorphic( m12, mw ); 
            assert v;       
            bas2 := tr^-1*bas2;

        else 
            Tk := IdentityMatrix( GF( q ), dK );
            ww := 1/2;
        end if;

        // bas1 is [e11, e12,...,e1k,...,ekk]
        // bas2 is [e{k+1}{k+1},...,edd]

        basH := [ M!(&+[bas1[j][i]*Basis( mH )[i] : 
                    i in [1..dimH]]) : j in [1..dimH]];
        basK := [ M!(&+[bas2[j][i]*Basis( mK )[i] : 
                    i in [1..dimK]]) : j in [1..dimK]];


        //if dim eq 19 then return aK, bas2, Tk; end if; // *****

        /* Construct the image of C in the tensor product component. It must be 
        isomorphic to the tensor product of the preimages of the 
        groups induced on the sym square components */
        
        genst := [ x@at : x in gensCD ];
        genstt := [ TensorProduct( x@ah@c1, Tk*x@ak@c2*Tk^-1 ) : x in gensCD ];
        
        T := GModule( sub< GL( dimT, q ) | genst >);
        
        /* The generators of the modules generated by genst and genstt are 
        lined up modulo a possible -1 scalar. The presence of the -1 is detected
        by comparing minimal polynomials. 
        
        (###) This is why the previous step with min pols was performed. */

        listch := [ x : x in [1..#genst] | MinimalPolynomial( genst[x] ) ne
                    MinimalPolynomial( genstt[x]  )];
        mns := GL( dimT, q )!ScalarMatrix( GF( q ), dimT, -1 ); // scalar matrix -I 
        for i in listch do
            genstt[i] := mns*genstt[i];
            assert MinimalPolynomial( genstt[i] ) eq MinimalPolynomial( genst[i] );
        end for;
        
        // get the isomorphism between the two GModules 
        TT := GModule( sub< GL( dimT, q ) | genstt >);
        v, al := IsIsomorphic( T, TT );
        
        assert v;

        V := VectorSpace( GF( q ), dimT );
        basT := [ M!(mT!(V!x)*(al^-1)) : x in [ Basis( T )[i] : i in [1..dimT]]];

        // *************** RECURSIVE CODE ENDS HERE *********************
    
    else

        // ******************** TENSOR DECOMP SPECIFIC CODE STARTS HERE ************** 
            
        /* Construct the image of CD in the tensor product component. It must be 
        isomorphic to the tensor product of the preimages of the 
        groups induced on the alt square components */

        genst := [ x@at : x in gensCD ];
        aT := sub< Universe( genst ) | genst >;
        v := IsTensor( aT : Factors := [[dH, dK]]); assert v; 
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

        g1h := sub< Universe( gens1h ) | gens1h >; 
        g1k := sub< Universe( gens1k ) | gens1k >;
        formh := ClassicalForms( g1h : Scalars := true );
        formk := ClassicalForms( g1k : Scalars := true );

        sch := formh`scalars;
        sck := formk`scalars;

        /* it might happen that an elment of gens1k or gens1h is the identity. 
        in this case, the corresponding scalar 1 will be mssing from sck and/or sch */

        if #sch lt #gens1h then
            gens1h_ := GeneratorsSequence( g1h );
            Append( ~gens1h_, gens1h_[1]^0 );
            Append( ~sch, 1 );
            sch := [ sch[Position( gens1h_, gens1h[x] )] : x in [1..#gens1h]];
        end if;

        if #sck lt #gens1k then  
            gens1k_ := GeneratorsSequence( g1k );
            Append( ~gens1k_, gens1k_[1]^0 );
            Append( ~sck, 1 );
            sch := [ sck[Position( gens1k_, gens1k[x] )] : x in [1..#gens1k]];
        end if;

        typeh := case< formh`formType | "orthogonalplus": "Omega+", 
                        "orthogonalminus": "Omega-", 
                        "orthogonalcircle": "Omega",  
                        default: false >;
        
        typek := case< formk`formType | "orthogonalplus": "Omega+", 
                        "orthogonalminus": 
                        "Omega-", 
                        "orthogonalcircle": "Omega",
                        default: false >;
                    
        vprint SymSquareVerbose: "# Subspace types: ", typeh, dH, typek, dK; 

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
        
        Th := TransformToForm( sub< Universe( gens1h ) | gens1h > );
        Tk := TransformToForm( sub< Universe( gens1k ) | gens1k > );

        if typeh eq "Omega-" and typek eq "Omega" then
            formcircle := ZeroMatrix( GF( q ), dK );
            issq1 := IsSquare( GF(q)!(-1)^(dim div 2)*(1/2));
            issq2 := IsSquare( GF(q)!(-1)^(dK div 2)*(1/2)*
                        (-1)^((dH - 2) div 2+1)*Nonsquare( GF( q )));
                    //Determinant( ClassicalForms( OmegaMinus( dH, q ))`bilinearForm));

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

        tbas := TensorProduct( Th^-1, Tk^-1 )*tbas;
        gens1h := [ x^Th : x in gens1h ];
        gens1k := [ x^Tk : x in gens1k ];
        //error(111);
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

    // ********************** TENSOR DECOMP SPECIFIC CODE ENDS HERE **************
    end if;

    if not assigned ww then ww := 1/2; end if;

    AssignBasisFromComponents( ~G, dH, dK, GF( q ) : type := type, 
                                                    typeh := typeh, 
                                                    typek := typek,
                                                        ww := ww ); 

    if not pdivdim then
        basOneDim := [ M!(Basis( monedim )[1])]; wH := basOneDim[1];
    else 
        basOneDim := [ Zero( M )];
    end if;

    //if not assigned ww then ww := 1; end if;
            
    /* we place the basis vectors computed in bas1 and bas2 into their place
       in the basis of V */

    bas := BuildBasisOmega( G, basH, basK, basT : type := type, 
                                               typeh := typeh, 
                                               typek := typek,
                                               wH := basOneDim[1], 
                                               ww := ww );
    tr := GL( dimg, q )!bas;

    //error(111);
    // return CD, tr;

    g := sub< GL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
    form := ClassicalForms( g )`bilinearForm;

    //return form;

    if <type,typeh,typek> ne <"Omega+","Omega-","Omega-"> then
        posT1 := dH div 2+1;
        posT2 := funcpos_symsquare( dim, dim-dH div 2, dim : type := type );
    else 
        posT1 := dH div 2;
        posT2 := funcpos_symsquare( dim, dim-dH div 2+1, dim : type := type );
    end if;

    if pdivdim then posT2 := posT2-1; end if;
    
    oldbasH := basH; oldbasT := basT;

    if not IsSquare( 2*form[posT1,posT2] ) then 
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
                trh[i,i] := z;
            end for;

            if q mod 4 eq 3 then 
                m2 := Matrix( GF( q ), 2, 2, [z,0,0,z]);
            else 
                m2 := Matrix( GF( q ), 2, 2, [z,0,0,-z*Nonsquare( GF( q ))]);
            end if;
            // problem???
            oldform := Matrix( GF( q ), 2, 2, [1,0,0,-Nonsquare( GF( q ))]);
            t2 := TransformForm( m2, "orthogonalminus" )*
                    TransformForm( oldform, "orthogonalminus" )^-1;
            
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

   g := sub< GL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
   form := ClassicalForms( g )`bilinearForm; 
   assert IsSquare( 2*form[posT1,posT2] ); //IsSquare( 2*form[dH div 2+1,posT] ); 
   vH := Sqrt( form[1,dimg] )^-1; 
    
   posK1 := funcpos_symsquare( dim, (dH div 2)+1,(dH div 2)+2 : type := type );
   
   if type in "Omega-"  and dH div 2 + 2 eq dim div 2 then 
       posK2 := funcpos_symsquare( dim, (dH div 2)+2,dim-(dH div 2) : 
                                    type := type );
   else
       posK2 := funcpos_symsquare( dim, dim-(dH div 2)-1,dim-(dH div 2) : 
                                    type := type );
   end if;

   if typeh  eq "Omega-" and typek eq "Omega-" and dK eq 6 then
        posK1 := funcpos_symsquare( dim, (dH div 2),(dH div 2)+1 : 
                                    type := type );
        posK2 := funcpos_symsquare( dim, dim-(dH div 2),dim-(dH div 2)+1 : 
                                    type := type );
   end if;

   if typeh eq "Omega-" and typek eq "Omega-" then 
        //error(1);
        posK1 := funcpos_symsquare( dim, dH div 2, dH div 2 : type := type );
        posK2 := funcpos_symsquare( dim, dim - dH div 2 + 1, dim - dH div 2 + 1 : type := type );
    else
        posK1 := funcpos_symsquare( dim, dH div 2+1, dH div 2+1 : type := type );
        posK2 := funcpos_symsquare( dim, dim - dH div 2, dim - dH div 2 : type := type );
   end if;

   if pdivdim then posK2 := posK2 - 1; end if;

   vK := Sqrt( form[posK1,posK2] )^-1; 
   //posT := funcpos_symsquare( dim, dim-dH div 2, dim : type := type );
   //if pdivdim then posT := posT -1; end if;
   vT := Sqrt( 2*form[posT1,posT2] )^-1;   
      
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
   g := sub< GL( dimg, q ) | { bas*x*bas^-1 : x in Generators( G0 )}>;
  
   //return CD, GL( dimg, q )!bas;

   if not pdivdim then 

        form := ClassicalForms( g )`bilinearForm;
        b := form[dim,dim];
        assert form[1,dimg] eq 1 and form[2,dimg-1] eq 1/2;
        P<x> := PolynomialRing( GF( q ));

        if type eq "Omega+" and typeh eq "Omega+" then 
        
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
            auxmat, vals := OmegaBasisFromComponents( G );
            aa := vals[1]; awH := vals[2]; awK := vals[3]; 
            wHwH := vals[4]; wKwK := vals[5];
            
            auxmat := BasisMatrixForSymSquareOmega( "Omega", dH+dK, GF(q) )*auxmat^-1;
            u := auxmat[dim,dimg]; v := auxmat[dim,dimg+1]; 
            // error(1);
            //aa := 1; awH := 6; awK := 4; wHwH := 5; wKwK := 3;
            pol := -b+aa+2*u*(x-1)*awH+2*v*(x-1)*awK+u^2*(x-1)^2*wHwH+v^2*(x-1)^2*wKwK; 
        
        elif type eq "Omega+" and typeh eq "Omega-" then

            auxmat, vals := OmegaBasisFromComponents( G );
            aa := vals[1]; awH := vals[2]; awK := vals[3]; 
            wHwH := vals[4]; wKwK := vals[5];
            
            auxmat := BasisMatrixForSymSquareOmega( "Omega+", dH+dK, GF(q) )*auxmat^-1;
            u := auxmat[dim,dimg]; v := auxmat[dim,dimg+1]; 
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
   //return form;
   assert v;     
   
   bas := BuildBasisOmega( G, basH, basK, basT : type := type, 
                                              typeh := typeh,
                                              typek := typek,
                                              wH := basOneDim[1], 
                                              scalars := coeffs, 
                                              ww := ww );
   tr := GL( dimg, GF( q ))!bas;
   
   if not RecursiveCall and type eq "Omega-" then
        tr_new_form := TransformForm( OldFormOmegaMinus( dim, q), "orthogonalminus" );
   else 
        tr_new_form := One( GL( dim, q ));
   end if; 

   // construct the maps between GL(dim,q) and G
    
    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToSymSquare( x^(tr_new_form^-1) : type := type )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> GL( dim, q )!__funcSymSquareToSLdq( x^(tr^-1) : type := type )^tr_new_form >;
    
    vprint SymSquareVerbose: "# Recog SymSquare dim", dim, "took ", 
      Cputime()-cputm;
            
    return true, a, b, tr;
end function;