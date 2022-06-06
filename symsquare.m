/* 
   The implementation of the algorithm suggested by Charles Leedham-Green
   to solve the recognition problem in symmetric square representations of 
   classical groups.
  
   This file contains the implementation for SL, Sp, SU. These groups will 
   be referred to as SX(n,q). The implementations 
   for the Omega groups are contained in a separate file. 
  
   The basis for the underlying vector space in the symmetric square action
   is always assumes to be in the order e11, e12, ..., e1d, e22,..., edd 
   where eij = ei wedge ej.
  
*/
  
import "smalldimreps.m":__funcSLdqToSymSquare, 
  __funcSymSquareToSLdq, SolveSymSquareDimEq, funcpos_symsquare;
import "auxfunctions.m": MyDerivedGroupMonteCarlo;
import "symsquare_omega.m":RecogniseSymSquareOmegaFunc;
import "symsquare_omega_aux.m":AssignBasisFromComponents, BuildBasisOmega;
import "recogsmalldim.m":RecogniseSymSquareWithSmallDegree;

AddAttribute( GrpMat, "BasisMatrixFromComponents" );

/* The recognition procedure for SX( 2, q ). It is based on the fact that 
   SymSquare( SL( 2, q )) is 3-dimensional and preserves a quadratic form. */
    
RecogniseSymSquareDim2 := function( G )
    
    vprint SymSquareVerbose: "# Recog SymSquare dim 2";
    cputm := Cputime();
    
    /* G preserves an orthogonal form. First find the matrix that 
       transforms G to canonical form with respect to this form. */
      
    q := #CoefficientRing( G );
    mat := TransformForm( G : Scalars := true )*GL(3,q)![-1, 0, 0,
                                        0, 1, 0,
                                        0, 0, 1];
      
    // construct the function SL(2,q) -> G 
      
    a := map< GL( 2, q ) -> GL( 3, q ) | 
         x :-> (GL(3,q)!__funcSLdqToSymSquare( x ))^(mat^-1) >;
    
    // construct the function G -> SL( 2, q )
    
    b := pmap< GL(3,q) -> GL( 2, q ) | 
         x :-> __funcSymSquareToSLdq( x^mat )>;
    
    vprint SymSquareVerbose: "# Recog SymSquare dim 2 took", Cputime()-cputm;

    return true, a, b, mat^-1;
end function;    
    
// The recognition procedure for SX(3,q)    
    
RecogniseSymSquareDim3 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog SymSquare dim 3";
    cputm := Cputime();

    q := #CoefficientRing( G ); 
    
    // find an involution that corresponds to diag(-1,1,1)
    repeat  
        _, inv := RandomElementOfOrder( G, 2 );
    until Dimension( Eigenspace( inv, -1 )) eq 2;     
    vprint SymSquareVerbose: "#   Inv found dim 3 in ", Cputime()-cputm;
    
    // find the centralizer of inv and take its derived subgroup
    C := CentraliserOfInvolution( G, inv ); 
    C := MyDerivedGroupMonteCarlo( C );     
    
    vprint SymSquareVerbose: "#   Cent comput dim 3 took ", Cputime()-cputm;
    
    /* The C-module V splits into three components of dimension 3, 1, 2
       which are isomorphic to symmetric square of SX(2,q), trivial module, 
       and natural module for SX(2,q) */

    M := GModule( C );
    mins := [ x : x in MinimalSubmodules( M ) ];
            
    mH := [ x : x in mins | Dimension( x ) eq 3 ][1]; // sym square of SX(2,q)
    mK := [ x : x in mins | Dimension( x ) eq 1 ][1]; // trivial module
    mT := [ x : x in mins | Dimension( x ) eq 2][1];  // natural module of SX(2,q)
      
    // the first basis element e11 will be a generator of the 1-dim component
    e11 := Basis( mK )[1];
    
    // construct the projections of C onto the components
    ah := pmap< GL( 6, q ) -> GL( 3, q ) | 
          x :-> GL( 3, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    at := pmap< GL( 6, q ) -> GL( 2, q ) | 
          x :-> GL( 2, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;
    
    /* For some technical reason (see (***) later), the projection of a 
       generator of C cannot have the same minimal polynomial as its negative. 
       If some generator fails to satisfy this, it is thrown away and is 
       replaced by another one. */  
    
    gensC := GeneratorsSequence( C );
    mns := GL( 2, q )!ScalarMatrix( GF( q ), 2, -1 ); // scalar matrix -I
    
    for i in [1..#gensC] do
        gi := gensC[i]@at;
        if MinimalPolynomial( gi ) eq MinimalPolynomial( mns*gi ) then
           repeat
               x := Random( C ); xa := x@at;
           until MinimalPolynomial( xa ) ne MinimalPolynomial( mns*xa );
           gensC[i] := x;
       end if;
    end for;
    
    // C should not change by the next line
    C := sub< Universe( gensC ) | gensC >;
    
    /* construct the projection of C in the sym square of SL(2,q) 
       and recognise it as sym square */
    aH := sub< GL( 3, q ) | [ x@ah : x in gensC ]>;
    
    // I'm not sure any more why the following line is needed.
    if q ne 3 and <type,q> ne <"SU",9> then 
        aH := MyDerivedGroupMonteCarlo( aH );
    end if;
    
    _, b1, c1, bas1 := RecogniseSymSquareDim2( aH );
    
    // bas1 contains the basis elements e22, e23, e33
    bas1 := [ M!(&+[bas1[j][i]*Basis( mH )[i] : i in [1..3]]) : j in [1..3]];
    e22 := bas1[1]; e23 := bas1[2]; e33 := bas1[3];
    
    /* Construct the projection of C into the natural rep of SL(2,q).
       Also construct the preimage of the sym square of SL(2,q). This
       gives two isomorphic modules. */
    
    genst := [ x@at : x in gensC ];     // gens of im of C in SL(2,q)
    genstt := [ x@ah@c1 : x in gensC ]; // gens of preimage of sym square
    
    T := GModule( sub< GL( 2, q ) | genst >);
    
    /* The generators of the modules generated by genst and genstt are 
       lined up modulo a -1 scalar. The presence of the -1 scalar is detected
       by comparing minimal polynomials. 
      
       (***) This is why the previous step with min pols was performed. */
    listch := [ x : x in [1..#genst] | MinimalPolynomial( genst[x] ) ne
                MinimalPolynomial( genstt[x]  )];
    
    for i in listch do
        genstt[i] := mns*genstt[i];
        assert MinimalPolynomial( genstt[i] ) eq MinimalPolynomial( genst[i] );
    end for;
    
    // now test isomorphism between T and TT
    
    TT := GModule( sub< GL( 2, q ) | genstt >);
    v, al := IsIsomorphic( T, TT );
    
    if not v then
        error( "Module isomorphism is not found in dim 3" );
    end if;
    
    // we get the basis vectors e12, e13 module a scalar from the module isom
    V := VectorSpace( GF( q ), 2 );
    tbas := [ M!(mT!(V!Eltseq( mT!x ))*(al^-1)) : 
              x in [ Basis( mT )[i] : i in [1..2]]];
    e12 := tbas[1]; e13 := tbas[2];
    
    /* Finally we have a complete basis. However, the vectors 
       e12 and e13 are only determined up to a scalar c and e11 is only 
       determined up to squares. We solve this as follows. We write
       a  random element <test> of G in the present basis. 
       Then the scalar c and the possible non-square factor z0 can be 
       picked up by considering the value of
       test[1,2]*test[1,3]*(2*test[1,1]*test[1,5])^-1. This value should be c^2*z0. */
      
    bas := [e11,e12,e13,e22,e23,e33];
    tr := GL( 6, q )![ Eltseq( x ) : x in bas ];
    
    z0 := PrimitiveElement( GF( q ));
    repeat 
        test := Random( G )^(tr^-1);
    until test[1,1] ne 0 and test[1,5] ne 0;
        
    lambdasq := test[1,2]*test[1,3]*(2*test[1,1]*test[1,5])^-1;

    try 
      lambda := Sqrt( lambdasq ); 
      bas[2] := lambda*bas[2];
      bas[3] := lambda*bas[3];
    catch e 
      lambda := Sqrt( z0*lambdasq ); 
      bas[2] := lambda*bas[2];
      bas[3] := lambda*bas[3];
      bas[1] := z0*bas[1];
    end try;
    
    // get new basis
    tr := GL( 6, q )![ Eltseq( x ) : x in bas ];
    
    // create maps between G and SL( 6, q )
    a := map< GL( 3, q ) -> GL( 6, q ) | 
         x :-> GL( 6, q )!__funcSLdqToSymSquare( x )^tr >;
    
    b := pmap< GL( 6, q ) -> GL( 3, q ) |
         x :-> GL( 3, q )!__funcSymSquareToSLdq( x^(tr^-1)) >;
    vprint SymSquareVerbose: "# Recog SymSquare dim 3 took ", Cputime()-cputm;

    return true, a, b, tr;
end function;

// checks if RecogniseSymSquare works for a given set of paramenters
IsValidParameterSetForSymSquare := function( type, dim, q )
    _, p := IsPrimePower( q );
    if p eq 2 then return false;  
    elif type in {"SL","Sp","SU" } and dim lt 2 then return false;
    elif <type,dim,q> eq <"Omega+",10,3> then return false; 
    elif <type,dim,q> eq <"Omega-",10,3> then return false; 
    elif type eq "Omega+" and dim lt 10 then return false; 
    elif type eq "Omega-" and dim lt 8 then return false; 
    elif type eq "Omega" and dim lt 7 then return false; end if;

    return true;
end function;
        
// The general recursive function. 
forward RecogniseSymSquareFunc;
RecogniseSymSquareFunc := function( G : type := "SL", IsRecursiveCall := false )
    
    cputm := Cputime();

    q := #CoefficientRing( G ); 
    _, p := IsPrimePower( q );
    dimg := Dimension( G );
    // the natural dimension of G
    dim := SolveSymSquareDimEq( dimg : type := type ); 
    vprint SymSquareVerbose: "# Recog SymSquare dim", dim;
    
    // in small dimension, call other functions
    case dim: 
      when 2: return RecogniseSymSquareDim2( G );
      when 3: return RecogniseSymSquareDim3( G : type := type );
    end case;

    if <type,dim,p> eq <"Omega",9,5> then 
        return  RecogniseSymSquareWithSmallDegree( G : type := type );
    elif <type,dim,p> eq <"Omega+",10,3> then 
        return  RecogniseSymSquareWithSmallDegree( G : type := type );
    elif <type,dim,p> eq <"Omega-",10,3> then 
        return  RecogniseSymSquareWithSmallDegree( G : type := type );
    elif type eq "Omega" and dim lt 9 then
        return  RecogniseSymSquareWithSmallDegree( G : type := type );
    end if;

    // For Omega groups we call other function 

    if type in { "Omega+", "Omega-", "Omega" } then 
      return RecogniseSymSquareOmegaFunc( G : type := type );
    end if;
        
    /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      
    eiglim1 := (2/9)*dim^2; // lower limit for eigenspace dim
    eiglim2 := (1/4)*dim^2; // upper limit for eigenspace dim
      
    repeat  
        _, inv := RandomElementOfOrder( G, 2 );
        de := Dimension( Eigenspace( inv, -1 ));
    until de ge eiglim1 and de le eiglim2;
    vprint SymSquareVerbose: "#   Inv found dim", dim, "in ", Cputime()-cputm;

    if type eq "SU" and q eq 9 then 
        NrGensCentInv := 20;
    elif type eq "SU" and dim le 10 and q le 25 then 
        NrGensCentInv := 20;
    else    
        NrGensCentInv := 10; 
    end if;

    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    /* Next we find the generating set of the centralizer of the involution.
       We add generators until the the natural module of < gensC > has precisely three 
       components. */

    gensC := []; gensCD := [];

    if <dim,q> eq <6,3> then 
        take_derived_subgroup := false;
    else
        take_derived_subgroup := true;
    end if;

    if type ne "SU" and ( q ge 5 or dim ge 6 ) then 
        DerivedLength := 2; 
    elif type eq "SU" and dim gt 4 then 
        DerivedLength := 1;
    elif type eq "SU" and dim le 4 then 
        DerivedLength := 1;
    else
        DerivedLength := 1; 
    end if;
    
    count := 1;
    repeat            
        count := count + 1; 
        if count gt 100 then error( 111 ); end if;
        C := CentraliserOfInvolution( G, inv : 
                         CompletionCheck := __compcheck );
        
        if take_derived_subgroup then 
            CD := MyDerivedGroupMonteCarlo( C : 
                          NumberGenerators := NrGensCentInv,
                          DerivedLength := DerivedLength );
        else 
            CD := C;
        end if;

        gensC := gensC cat GeneratorsSequence( C );
        gensCD := gensCD cat GeneratorsSequence( CD );
        C := sub< Universe( gensC ) | gensC >;
        CD := sub< Universe( gensCD ) | gensCD >;
        M := GModule( CD ); 
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )];
    until  #mins eq 3 and &+[ Dimension( x ) : x in mins ] eq dimg;

    vprint SymSquareVerbose: "#   Cent comput dim", dim, "took ", 
      Cputime()-cputm, #gensC, "gens used.";
      
      /* The C-module V splits into three components.
         Two components are isomorphic to sym square U and sym square W, 
         respectively. The third is isomorphic to U tensor W.  
         The two sym squares lie in the one eigenspace of inv. The tensor 
         lies in the minus one eigenspace. */
        
    mH := [ mins[x] : x in [1..#mins] | (M!mins[x].1)^inv eq M!mins[x].1 ][1];
    mK := [ mins[x] : x in [1..#mins] | (M!mins[x].1)^inv eq M!mins[x].1 ][2];
    mT := [ mins[x] : x in [1..#mins] | (M!mins[x].1)^inv eq -M!mins[x].1 ][1];
    
    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );

    dH := SolveSymSquareDimEq( dimH ); dK := SolveSymSquareDimEq( dimK ); 
    assert dimT eq dH*dK;

    // we want dH to be even-dimensional. if it is not, then we swap

    if IsOdd( dH ) then 
        t := dH; dH := dK; dK := t;
        t := dimH; dimH := dimK; dimK := t;
        t := mH; mH := mK; mK := t;
    end if;        
    
    // set up the projections into the components
    
    ah := pmap< GL( dimg, q ) -> GL( dimH, q ) | 
          x :-> GL( dimH, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    ak := pmap< GL( dimg, q ) -> GL( dimK, q ) | 
          x :-> GL( dimK, q )![ Eltseq( mK!((M!b)^x )) : b in Basis( mK )]>;
    
    at := pmap< GL( dimg, q ) -> GL( dimT, q ) | 
          x :-> GL( dimT, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;
    
    /* For some technical reason (see (###) later), the projection of a 
       generator of C cannot have the same minimal polynomial as its negative. 
       If some generator fails to satisfy this, it is thrown away and is 
       replaced by another one. */  

    mns := GL( dimT, q )!ScalarMatrix( GF( q ), dimT, -1 );
    
    for i in [1..#gensCD] do
        gi := gensCD[i]@at;
        if MinimalPolynomial( gi ) eq MinimalPolynomial( mns*gi) then
           repeat
               x := Random( CD ); xa := x@at;
           until MinimalPolynomial( xa ) ne MinimalPolynomial( mns*xa );
           gensCD[i] := x;
       end if;
    end for;
   
    mins := MinimalSubmodules( GModule( sub< Universe( gensCD ) | gensCD > ) : 
                                Limit := 4 ); 

    while #mins ne 3 or &+[ Dimension( x ) : x in mins ] ne dimg do

        repeat
            x := Random( CD ); xa := x@at;
        until MinimalPolynomial( xa ) ne MinimalPolynomial( mns*xa );
        Append( ~gensCD, x );        
        mins := MinimalSubmodules( GModule( sub< Universe( gensCD ) | gensCD > ) : 
                                    Limit := 4 ); 
    end while;
    
    /* construct and recognise the two groups induced on the sym square
       components */

    aH := sub< GL( dimH, q ) | [ x@ah : x in gensCD ]>;
    aK := sub< GL( dimK, q ) | [ x@ak : x in gensCD ]>;
    
    if dH gt 3 then 
        aH := MyDerivedGroupMonteCarlo( aH );
    end if;

    if dK gt 3 then 
        aK := MyDerivedGroupMonteCarlo( aK );       
    end if;

    //error(111);
    assert IsIrreducible( aH ) and IsIrreducible( aK );
    //  assert IsProbablyPerfect( aH ) and IsProbablyPerfect( aK );
     
    // the recursive call to recognise the smaller-dimensional sym squares aH and aK
    _, b1, c1, bas1 := RecogniseSymSquareFunc( aH : type := type, IsRecursiveCall := true );
    _, b2, c2, bas2 := RecogniseSymSquareFunc( aK : type := type, IsRecursiveCall := true );
    
    // bas1 is [e11, e12,...,e1k,...,ekk]
    // bas2 is [e{k+1}{k+1},...,edd]

    bas1 := [ M!(&+[bas1[j][i]*Basis( mH )[i] : 
                 i in [1..dimH]]) : j in [1..dimH]];
    bas2 := [ M!(&+[bas2[j][i]*Basis( mK )[i] : 
                 i in [1..dimK]]) : j in [1..dimK]];
            
    /* Construct the image of C in the tensor product component. It must be 
       isomorphic to the tensor product of the preimages of the 
       groups induced on the sym square components */
    
    genst := [ x@at : x in gensCD ];
    genstt := [ TensorProduct( x@ah@c1, x@ak@c2 ) : x in gensCD ];
    
    T := GModule( sub< GL( dimT, q ) | genst >);
    
    /* The generators of the modules generated by genst and genstt are 
       lined up modulo a possible -1 scalar. The presence of the -1 is detected
       by comparing minimal polynomials. 
      
       (###) This is why the previous step with min pols was performed. */

    listch := [ x : x in [1..#genst] | MinimalPolynomial( genst[x] ) ne
                MinimalPolynomial( genstt[x]  )];

    for i in listch do
        genstt[i] := mns*genstt[i];
        //assert MinimalPolynomial( genstt[i] ) eq MinimalPolynomial( genst[i] );
    end for;
     
    // get the isomorphism between the two GModules 
    TT := GModule( sub< GL( dimT, q ) | genstt >);
    v, al := IsIsomorphic( T, TT );
    
    if not v then
        error( "Module isomorphism is not found for the tensor product in dim", dimg );
    end if;

    V := VectorSpace( GF( q ), dimT );
    tbas := [ M!(mT!(V!x)*(al^-1)) : x in [ Basis( T )[i] : i in [1..dimT]]];

    // assgn the basis matrix to G that reflects the decomposition
    AssignBasisFromComponents( ~G, dH, dK, GF( q ) : type := type );

    // Build the basis from the bases of the components
    bas := BuildBasisOmega( G, bas1, bas2, tbas : type := type, 
                typeh := type, typek := type );
    tr := GL( dimg, q )!bas; //[ Eltseq( x ) : x in bas ];

    /* Finally we have a complete basis. However, the vectors 
       eij that were returned by the tensor recognition  
       are only determined up to a scalar c, while the vectors eij 
       in the second sym square are also determined up to squares. 
       We solve this as follows. 
       We write a  random element <test> of G in the present basis. 
       Then the scalar c and the possible non-square factor z0 can be 
       picked up by considering the value of
       test[1,dH+1]*test[1,dH+2]*(2*test[1,1]*test[1,z])^-1. 
       where z is the position of e_{dH+1,dH+2} in our basis. This value should be c^2*z0. */

    z0 := PrimitiveElement( GF( q ));
    
    pos := funcpos_symsquare( dim, dH div 2+1, dH div 2+2 );
    repeat 
        test := Random( G )^(tr^-1);
    until test[1,1] ne 0 and test[1,pos] ne 0;

    assert test[1,dH div 2+1] ne 0 and test[1,dH div 2+2] ne 0;
    
    lambdasq := test[1,dH div 2+1]*test[1,dH div 2+2]*(2*test[1,1]*test[1,pos])^-1;

    // set up the index sets that correspond to the subspaces H and K
    rangeH := [1..dH div 2] cat [dim-dH div 2+1..dim];
    rangeK := [dH div 2+1..dim-dH div 2];
 
    try 
      lambda := Sqrt( lambdasq ); 
      for i in rangeH do
          for j in rangeK do
              pos := funcpos_symsquare( dim, i, j );
              // multiply eij by lambda
              bas[pos] := lambda*bas[pos];
          end for;
      end for;
    catch e 
      lambda := Sqrt( z0*lambdasq ); 
      for i in rangeH do
          for j in rangeK do
              pos := funcpos_symsquare( dim, i, j );
              // multiply eij by lambda
              bas[pos] := lambda*bas[pos];
          end for;
      end for;
    
      for i in rangeH do
          for j in rangeH do
              if j lt i then continue; end if;
              pos := funcpos_symsquare( dim, i, j );
              // multiply eij by z0
              bas[pos] := z0*bas[pos];
          end for;
      end for;
    end try;

    tr := GL( dimg, q )!bas;//[ Eltseq( x ) : x in bas ];

    // construct the maps between GL(dim,q) and G

    // Standardise the classical form preserved by G
    if not IsRecursiveCall and type in { "Sp", "Omega+", "Omega-", "Omega" } then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcSymSquareToSLdq( x^(tr^-1)) : x in GeneratorsSequence( G )] >)`bilinearForm;
        tr_form := TransformForm( form, case< type | 
                                            "Sp": "symplectic", 
                                            "Omega+": "orthogonalplus", 
                                            "Omega-": "orthogonalminus", 
                                            "Omega": "orthogonalcircle", 
                                            default: false  >);        
    elif not IsRecursiveCall and type eq "SU" then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcSymSquareToSLdq( x^(tr^-1)) : x in GeneratorsSequence( G )] >)`sesquilinearForm;
        tr_form := TransformForm( form, "unitary" );
    else 
        tr_form := One( GL( dim, q ));
    end if;

    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToSymSquare( x^(tr_form^-1) )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> (GL( dim, q )!__funcSymSquareToSLdq( x^(tr^-1)))^tr_form >;


    vprint SymSquareVerbose: "# Recog SymSquare dim", dim, "took ", 
      Cputime()-cputm;
        
    return true, a, b, tr;
end function;

    
intrinsic RecogniseSymSquare( G::GrpMat : type := "SL", 
                                          CheckResult := true ) 
          -> BoolElt, Map, Map, GrpMatElt
                                                         
 {G should be matrix group conjugate to the symmetric square representation
  of SL( d, q ). Returns true/false, a map from SL( d, q ) to G, a map from 
  G to SL( d, q ), and a matrix whose rows form a basis that exhibits the 
  sym square structure. Supply CheckResult := true to check the final result.}                     

    dimg := Dimension( G );
    dim := SolveSymSquareDimEq( dimg : type := type );
    q := #CoefficientRing( G );     

    if not IsValidParameterSetForSymSquare( type, dim, q ) then 
        error( "not valid paramenters for symmetric square recognition" );
    end if;

    v, a, b, tr := RecogniseSymSquareFunc( G : type := type );
    assert v;

    // Standardise the classical form preserved by G
    if type in { "Sp", "Omega+", "Omega-", "Omega" } then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcSymSquareToSLdq( x^(tr^-1) : type := type ) : 
                            x in GeneratorsSequence( G )] >)`bilinearForm;
        tr_form := TransformForm( form, case< type | 
                                            "Sp": "symplectic", 
                                            "Omega+": "orthogonalplus", 
                                            "Omega-": "orthogonalminus", 
                                            "Omega": "orthogonalcircle", 
                                            default: false  >);        
    elif type eq "SU" then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcSymSquareToSLdq( x^(tr^-1) : type := type ) : 
                            x in GeneratorsSequence( G )] >)`sesquilinearForm;
        tr_form := TransformForm( form, "unitary" );
    else 
        tr_form := One( GL( dim, q ));
    end if;

    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToSymSquare( x^(tr_form^-1) : type := type )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> (GL( dim, q )!__funcSymSquareToSLdq( x^(tr^-1) : type := type ))^tr_form >;

    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        try
            gens := [ x@b : x in GeneratorsSequence( G )];
        catch e 
            f := Open( "debugfile", "w" );
            WriteObject( f, G ); print( "G written to file" );
            delete f;
            error( "Failed to apply map from G to classical group in dim "*IntegerToString( dim ));
        end try;
        M1 := GModule( sub< GL( dimg, q ) | 
                      [ __funcSLdqToSymSquare( MatrixAlgebra( GF( q ), dim )!(x^(tr_form^-1)) : type := type ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
	return false, _, _, _;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;
    
    return true, a, b, _;    
end intrinsic;

