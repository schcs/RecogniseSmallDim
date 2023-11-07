import "smalldimreps.m":__funcSLdqToSymSquare, __funcSymSquareToSLdq, 
                        __funcSLdqToAltSquare, __funcAltSquareToSLdq;

declare attributes GrpMat: AltSymSquareInfo;

altsymsquareinforf := recformat<    Type: MonStgElt, 
                                    RepType: MonStgElt,
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
    rep_type := G`AltSymSquareInfo`RepType;
    type := G`AltSymSquareInfo`Type;

    grp_nat := case< type | 
                     "SL": SL( n0, F0 ), 
                     "Sp": Sp( n0, F0 ),
                     "SU": SU( n0, F0 ),
                     "Omega+": OmegaPlus( n0, F0 ),
                     "Omega-": OmegaMinus( n0, F0 ),
                     "Omega": Omega( n0, F0 ), 
                     default: false >;
    
    assert not Type( grp_nat ) eq BoolElt;

    if not x in grp_nat then 
        return false, _;
    end if; 

    rep_func := case< rep_type | "SymSquare": __funcSLdqToSymSquare, "AltSquare": __funcSLdqToAltSquare, 
                                 default: false >;

    y := rep_func( x^(tr_inner^-1) : type := type );
    if Type( y ) eq BoolElt then 
        return false, _;
    end if; 
    
    y := (GL( NumberOfRows( y ), CoefficientRing( y ))!y)^tr_outer;
    
    return true, y;
end function;


AltSymPreimage := function( G, x )
    
    if not assigned G`AltSymSquareInfo then 
        Error( "RecongiseAltSquare of RecogniseSymSquare must be performed on G before calling this function." );
    end if;

    n0 := G`AltSymSquareInfo`NatDim;
    F0 := G`AltSymSquareInfo`NatField;
    tr_inner := G`AltSymSquareInfo`tr_matrix_inner;
    tr_outer := G`AltSymSquareInfo`tr_matrix_outer;
    rep_type := G`AltSymSquareInfo`RepType;
    type := G`AltSymSquareInfo`Type;

    grp_nat := case< type | 
                     "SL": SL( n0, F0 ), 
                     "Sp": Sp( n0, F0 ),
                     "SU": SU( n0, F0 ),
                     "Omega+": OmegaPlus( n0, F0 ),
                     "Omega-": OmegaMinus( n0, F0 ),
                     "Omega": Omega( n0, F0 ), 
                     default: false >;
    
    assert not Type( grp_nat ) eq BoolElt;

    rep_func := case< rep_type | "SymSquare": __funcSymSquareToSLdq, "AltSquare": __funcAltSquareToSLdq, 
                                 default: false >;
    
    y := rep_func( x^(tr_outer^-1) : type := type );
    
    if Type( y ) eq BoolElt then 
        return false, _;
    end if;
    
    if Determinant( y ) eq 0 then return false, _; end if;
    y := GL( n0, CoefficientRing( y ))!y^tr_inner;
    
    // check if y is in the natural group
    // in the case of Omega groups, y may not have the right spinor norm, 
    // in this case, -y is the right element    
    if y in grp_nat then 
        return true, y;
    elif -y in grp_nat then 
        return true, GL( n0, CoefficientRing( y ))!(-y);
    end if; 

    return false, _;
end function;

/* the following returns true/false depending on whether the methods in the package are applicable for 
   the particular problem.

   reptype: "Alt" or "Sym"
   type: "SL", "Sp", "SU", "Omega", "Omega+", or "Omega-"
   dim: integer
   q: prime-power

   */

 IsNewCodeApplicable := function( reptype, type, dim, q )

    _, p := IsPrimePower( q );
    if p eq 2 then return false; end if;

    if reptype eq "Sym" then 
        
        if type in {"SL","Sp","SU" } and dim lt 2 then return false;
        elif <type,dim,q> eq <"Omega+",10,3> then return false; 
        elif <type,dim,q> eq <"Omega-",10,3> then return false; 
        elif type eq "Omega+" and dim lt 10 then return false; 
        elif <type,dim,p> eq <"Omega+",10,3> then return false;
        elif type eq "Omega-" and dim lt 8 then return false;
        elif <type,dim,p> eq <"Omega-",10,3> then return false; 
        elif type eq "Omega" and dim lt 9 then return false;
        elif <type,dim,p> eq <"Omega",9,5> then return false; end if;

    elif reptype eq "Alt" then 
    
        if type eq "SL" and dim in {5,6} then return false;
        elif type eq "SU" and dim in {5,6} then return false;
        elif type eq "Sp" and dim lt 8 then return false;
        elif <type,dim,p> eq <"Sp",10,3> then return false;
        elif type eq "Omega+" and dim lt 12 then return false;  
        elif type eq "Omega-" and dim lt 12 then return false; 
        elif type eq "Omega" and dim lt 9 then return false; 
        elif <type,dim,q> eq <"Omega",9,3> then return false; end if; 
    
    end if; 

    return true;
end function;