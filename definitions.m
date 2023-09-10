// 
import "smalldimreps.m":__funcSLdqToSymSquare, __funcSymSquareToSLdq;

AddAttribute( GrpMat, "AltSymSquareInfo" );
altsymsquareinforf := recformat< Type: MonStgElt, 
                                    NatDim: RngIntElt,
                                    NatField: RngIntElt,
                                    phi_map: Map, 
                                    tau_map: Map,
                                    tr_matrix_inner: GrpMatElt,
                                    tr_matrix_outer: GrpMatElt >;



AltSymImage := function( G, x )
    
    if not assigned G`AltSymSquareInfo then 
        Error( "RecongiseAltSquare of RecogniseSymSquare must be performed on G before calling this function." );
    end if;

    n0 := G`AltSymSquareInfo`NatDim;
    F0 := G`AltSymSquareInfo`NatField;
    tr_inner := G`AltSymSquareInfo`tr_matrix_inner;
    tr_outer := G`AltSymSquareInfo`tr_matrix_outer;

    grp_nat := case< G`AltSymSquareInfo`Type | 
                     "SL": SL( n0, F0 ), 
                     "Sp": Sp( n0, F0 ),
                     "SU": SU( n0, F0 ),
                     "Omega+": OmegaPlus( n0, F0 ),
                     "Omega-": OmegaMinus( n0, F0 ),
                     "Omega": Omega( n0, F0 ), 
                     default: false >;
    
    assert not Type( grp_nat ) eq BoolElt;

    if not x in grp_nat then 
        return false;
    end if; 

    y := __funcSLdqToSymSquare( x^(tr_inner^-1) )^tr_outer;
    if Type( y ) eq BoolElt then 
        return false;
    end if; 
    
    return y;
end function;


AltSymPreimage := function( G, x )
    
    if not assigned G`AltSymSquareInfo then 
        Error( "RecongiseAltSquare of RecogniseSymSquare must be performed on G before calling this function." );
    end if;

    n0 := G`AltSymSquareInfo`NatDim;
    F0 := G`AltSymSquareInfo`NatField;
    tr_inner := G`AltSymSquareInfo`tr_matrix_inner;
    tr_outer := G`AltSymSquareInfo`tr_matrix_outer;

    grp_nat := case< G`AltSymSquareInfo`Type | 
                     "SL": SL( n0, F0 ), 
                     "Sp": Sp( n0, F0 ),
                     "SU": SU( n0, F0 ),
                     "Omega+": OmegaPlus( n0, F0 ),
                     "Omega-": OmegaMinus( n0, F0 ),
                     "Omega": Omega( n0, F0 ), 
                     default: false >;
    
    assert not Type( grp_nat ) eq BoolElt;

    y := __funcSymSquareToSLdq( x^(tr_outer^-1) );
    if Type( y ) eq BoolElt then 
        return false;
    end if;

    y := GL( n0, CoefficientRing( y ))!y^tr_inner;

    if not y in grp_nat then 
        return false;
    end if; 
    
    return y;
end function;
