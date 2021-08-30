// interface to RecogniseSmallDegree

import "smalldimreps.m": __funcSLdqToAltSquare, __funcAltSquareToSLdq, 
        SolveAltSquareDimEq, __funcSLdqToSymSquare, __funcSymSquareToSLdq, 
        SolveSymSquareDimEq;
import "auxfunctions.m":TransformToForm;

RecogniseAltSquareWithSmallDegree := function( G : type := "SL" )

    dimg := Dimension( G );
    q := #CoefficientRing( G );
    if type eq "SU" then 
        _, q0 := IsSquare( q );
    else    
        q0 := q;
    end if;

    d := SolveAltSquareDimEq( Dimension( G ) : type := type );

    v, g0 := RecogniseSmallDegree( G, type, d, q0 );
    if not v then print type, d, q0; error( 1111 ); return false, _, _; end if;

    if type ne "SL" then
        tr := TransformForm( g0 );
    else 
        tr := g0.1^0;
    end if;

    gens := [ __funcSLdqToAltSquare( x^tr : type := type ) : 
                x in GeneratorsSequence( g0 )];
    v, con := IsIsomorphic( GModule( G ), GModule( sub< GL( dimg, q ) | gens >));
    con := GL( dimg, q )!con;

    if not v then 
        error( "Module isomorphism failed." );
    end if;
        
    a := pmap< GL( d, q ) -> GL( dimg, q ) | 
         x :-> con*__funcSLdqToAltSquare( x : type := type )*con^-1 >;

    // construct the function G -> SL( 2, q )

    b := map< GL( dimg, q ) -> GL( d, q ) | 
         x :-> (GL(d,q)!__funcAltSquareToSLdq( x^con : type := type )) >;

    return true, a, b, con;
end function;

RecogniseSymSquareWithSmallDegree := function( G : type := "SL" )

    dimg := Dimension( G );
    q := #CoefficientRing( G );
    d := SolveSymSquareDimEq( Dimension( G ) : type := type );


    v, g0 := RecogniseSmallDegree( G, type, d, q );
    if not v then return false, _, _; end if;

    if type ne "SL" then
        tr := TransformToForm( g0 );
    else 
        tr := g0.1^0;
    end if;

    gens := [ __funcSLdqToSymSquare( x^tr : type := type ) : 
                x in GeneratorsSequence( g0 )];
    v, con := IsIsomorphic( GModule( G ), GModule( sub< GL( dimg, q ) | gens >));
    con := GL( dimg, q )!con;

    if not v then 
        error( "Module isomorphism failed." );
    end if;

    // construct the function G -> SL( 2, q )
    
    a := pmap< GL( d, q ) -> GL( dimg, q ) | 
         x :-> con*__funcSLdqToSymSquare( x : type := type )*con^-1 >;

    b := map< GL( dimg, q ) -> GL( d, q ) | 
         x :-> (GL(d,q)!__funcSymSquareToSLdq( x^con : type := type )) >;

    return true, a, b, con;
end function;