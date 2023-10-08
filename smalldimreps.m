import "greenhill.m":__funcAltSquareToSLdq_func;

// aux functions for small dim recognition
// solve the equation m = d(d+1)/2
  
SolveSymSquareDimEq := function( m : type := "SL" )

    if type in { "Omega+", "Omega-", "Omega" } then
        m := m+1;
    end if;
  
    sol := (-1+Sqrt( 1+8*m ))/2;
    
    if sol ne Round( sol ) and type in {"Omega+", "Omega-", "Omega"} then
        m := m+1;
        sol := (-1+Sqrt( 1+8*m ))/2;
    end  if;
    
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if;
    
end function;
    
// solve the equation m = d(d-1)/2
  
SolveAltSquareDimEq := function( m : type := "SL"  )

    if type eq "Sp" then
        m := m+1;
    end if;
      
    sol := (1+Sqrt( 1+8*m ))/2;
    
    if sol ne Round( sol ) and type eq "Sp" then
        m := m+1;
        sol := (1+Sqrt( 1+8*m ))/2;
    end  if;
    
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if;
    
end function;

    
/* position of basis element eij in the standard basis of the 
   sym square module. */
  
funcpos_symsquare := function( dim, i, j : type := "SL" )

    if i gt j then 
        tmp := i; i := j; j := tmp;
    end if;

    pos := Round( (i-1)*dim-i*(i-3)/2 )+j-i;
    
    if type eq "SL" then return pos, true; end if;

    if type eq "Omega+" then
        if i eq dim/2 and j eq dim/2+1 then
            return 0, false;
        elif i ge dim/2 and j ge dim/2+1 then
            return pos-1, false;
        elif i + j eq dim +1 then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            

    if type eq "Omega-" then
        if i eq dim/2+1 and j eq dim/2+1 then
            return 0, false;
        elif i ge dim/2+1 and j ge dim/2+1 then
            return pos-1, false;
        elif (i lt dim/2 and i + j eq dim +1) or (i eq dim/2 and j eq dim/2) then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            
    
    if type eq "Omega" then
        if i eq (dim+1)/2 and j eq (dim+1)/2 then
            return 0, false;
        elif i ge (dim+1)/2 and j ge (dim+1)/2 then
            return pos-1, false;
        elif (i lt (dim+1)/2 and i + j eq dim +1) then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            
     
end function;

// the inverse of the last function

funcposinv_symsquare := function( dim, i : type := "SL" )
    
    if type eq "Omega+" then
        i0 := funcpos_symsquare( dim, dim/2, dim/2+1 );
        if i ge i0 then
            i := i+1;
        end if;
    elif type eq "Omega-" then
        i0 := funcpos_symsquare( dim, dim/2+1, dim/2+1 );
        if i ge i0 then
            i := i+1;
        end if;
    end if;
    
    k := 0;        
    while k*(2*dim-k+1)/2 lt i do
        k := k+1;
        if k gt dim*(dim+1)/2 then
            return false;
        end if;
    end while;

    flag := false;    
    if type eq "Omega+" and k+i-(k-1)*(2*dim-k)/2 eq dim+1 then
        flag := true;
    elif type eq "Omega-" and (k lt dim/2 and (k+i-(k-1)*(2*dim-k)/2) eq dim+1) or 
                            (k eq dim/2 and i-(k-1)*(2*dim-k)/2 eq dim/2) then
        flag := true;
    end if;

    return <k,i-(k-1)*(2*dim-k) div 2>, flag;
end function;

/* position of basis element eij in the standard basis of the 
   alt square module. */
  
funcpos_altsquare := function( dim, i, j : type := "SL" )
    
    if i lt j then
        pos := Round( Round((2*dim-i)*(i-1)/2)+j-i);
    elif j lt i then
        pos := Round( Round((2*dim-j)*(j-1)/2)+i-j);
    else
        pos := 0;
    end if;
    
    // in the case of SL the position is calculated
    
    if type eq "SL" then return pos; end if;
    
    /* in the case of Sp the position needs modifying
       in this case we also return two values to indicate when
       a standard basis element is of the form <i,j> - <d/2,d/2+1>
       also remember that <d/2,d/2+1> does not occur in the standard 
       basis and so after this element the positions need shifting.
       */                            
    
    if type eq "Sp" then
        if i eq dim/2 and j eq dim/2+1 then
            return 0, false;
        elif i ge dim/2 and j gt dim/2+1 then
            return pos-1, false;
        elif i + j eq dim +1 then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            
    
end function;

// the inverse of the last function

funcposinv_altsquare := function( dim, i : type := "SL" )
    
    k := 0;
    
    if type eq "Sp" then
        i0 := funcpos_altsquare( dim, dim/2, dim/2+1 );
        if i ge i0 then
            i := i+1;
        end if;
    end if;
        
    while k*(dim-(k+1)/2) lt i do
        k := k+1;
        if k gt dim*(dim-1)/2 then
            return false;
        end if;
    end while;
    
    if type eq "SL" then
        return <k,k+i-(k-1)*(dim-(k)/2)>;
    elif type eq "Sp" and k+k+i-(k-1)*(dim-(k)/2) eq dim+1 then
        return <k,k+i-(k-1)*(dim-(k)/2)>, true;
    elif type eq "Sp" and k+k+i-(k-1)*(dim-(k)/2) ne dim+1 then
        return <k,k+i-(k-1)*(dim-(k)/2)>, false;
    end if;
    
end function;

forward __funcSLdqToSymSquare;

GetValueOmegaMinus := function( q )

    gamma := -Nonsquare( GF( q ));
    return -1/gamma, 1/2*gamma^-1;
end function;

// tha basis transform matrix for sym square of Omega+

BasisMatrixForSymSquareOmegaPlus := function( d, F )    
    
    d1 := (d*(d+1)) div 2;
    bas := IdentityMatrix( F, d1 );
        
    for i in [1..d/2-1] do  
        bas[funcpos_symsquare( d, i, d-i+1 ), 
            funcpos_symsquare( d, d div 2,d div 2+1 )] := -1;
    end for;
    
    for i in [1..d/2-1] do
        bas[funcpos_symsquare( d, d div 2,d div 2+1 ),
            funcpos_symsquare( d, i, d-i+1 )] := 1;
    end for;

    if d mod Characteristic( F ) eq 0 then 
        bas[funcpos_symsquare( d, d div 2-1,d div 2+2 ), 
            funcpos_symsquare( d, d div 2,d div 2+1 )] := 0;
    end if;
        
    // reorder the basis
      
    if d mod Characteristic( F ) ne 0 then
        list := [1..funcpos_symsquare( d, d div 2,d div 2+1 )-1] cat 
                [funcpos_symsquare( d, d div 2,d div 2+1 )+1..d1] cat 
                [funcpos_symsquare( d, d div 2,d div 2+1 )];
    else
        list := [1..funcpos_symsquare( d,d div 2-1,d div 2+1)] cat 
                [funcpos_symsquare( d,d div 2-1,d div 2+3)
                 ..funcpos_symsquare( d, d div 2,d div 2+1 )-1] cat 
                [funcpos_symsquare( d, d div 2,d div 2+1 )+1..d1] cat 
                [funcpos_symsquare( d, d div 2,d div 2+1 )] cat
                [funcpos_symsquare( d, d div 2-1,d div 2+2 )];
    end if;

    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;

// basis transform matrix for SymSquare Omega-

BasisMatrixForSymSquareOmegaMinus := function( d, F )    
    
    d1 := (d*(d+1)) div 2;
    bas := IdentityMatrix( F, d1 );
    
    z1, z2 := GetValueOmegaMinus( #F );
    for i in [1..d/2-1] do  
        bas[funcpos_symsquare( d, i, d-i+1 ), 
            funcpos_symsquare( d, d div 2+1,d div 2+1 )] := z1;
    end for;
    
    bas[funcpos_symsquare( d, d div 2, d div 2 ), 
            funcpos_symsquare( d, d div 2+1,d div 2+1 )] := z1;
    

    for i in [1..d/2-1] do
        bas[funcpos_symsquare( d, d div 2+1,d div 2+1 ),
            funcpos_symsquare( d, i, d-i+1 )] := 1;
    end for;

    bas[funcpos_symsquare( d, d div 2+1,d div 2+1 ),
            funcpos_symsquare( d, d div 2, d div 2 )] := 1/2;

    if d mod Characteristic( F ) eq 0 then 
        bas[funcpos_symsquare( d, d div 2+1,d div 2+1 ),
                funcpos_symsquare( d, d div 2+1, d div 2+1 )] := (d div 2-1+1/2)*z1;
    else 
        bas[funcpos_symsquare( d, d div 2+1,d div 2+1 ),
                funcpos_symsquare( d, d div 2+1, d div 2+1 )] := z2;
    end if;

    if d mod Characteristic( F ) eq 0 then  
        bas[funcpos_symsquare( d, d div 2,d div 2 ), 
            funcpos_symsquare( d, d div 2+1,d div 2+1 )] := 0;
    end if;

    // reorder the basis

    if d mod Characteristic( F ) ne 0 then  
        list := [1..funcpos_symsquare( d, d div 2+1,d div 2+1 )-1] cat 
                    [funcpos_symsquare( d, d div 2+1,d div 2+1 )+1..d1] cat 
                    [funcpos_symsquare( d, d div 2+1,d div 2+1 )];
    else
        list := [1..funcpos_symsquare( d, d div 2,d div 2 )-1] cat
                [funcpos_symsquare( d, d div 2,d div 2 )+1..
                funcpos_symsquare( d, d div 2+1,d div 2+1 )-1] cat 
                    [funcpos_symsquare( d, d div 2+1,d div 2+1 )+1..d1] cat
                    [funcpos_symsquare( d, d div 2,d div 2 )] cat
                    [funcpos_symsquare( d, d div 2+1,d div 2+1 )];
    end if;
        
    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;

// basis matrix for Sym square of Omega

BasisMatrixForSymSquareOmegaCircle := function( d, F : ww := 1/2 );    
    
    a := F!(-1/ww); b := 1/(2*ww);
    d1 := (d*(d+1)) div 2;
    bas := IdentityMatrix( F, d1 );
        
    for i in [1..(d-1)/2] do  
        bas[funcpos_symsquare( d, i, d-i+1 ), 
            funcpos_symsquare( d, (d+1) div 2,(d+1) div 2 )] := a;
    end for;
    
    for i in [1..(d-1)/2] do
        bas[funcpos_symsquare( d, (d+1) div 2,(d+1) div 2 ),
            funcpos_symsquare( d, i, d-i+1 )] := 1;
    end for;

    bas[funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 ),
        funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 )] := b;

    if d mod Characteristic( F ) eq 0 then  
        bas[funcpos_symsquare( d, (d-1) div 2,(d-1) div 2 +2 ), 
            funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 )] := 0;
    end if;
        
    // reorder the basis
      
    if d mod Characteristic( F ) ne 0 then 
        list := [1..funcpos_symsquare( d, (d+1) div 2,(d+1) div 2 )-1] cat 
                    [funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 )+1..d1] cat 
                    [funcpos_symsquare( d, (d+1) div 2,(d+1) div 2 )];

    else 
        list := [1..funcpos_symsquare( d, (d-1) div 2,(d-1) div 2 +2 )-1] cat 
                [funcpos_symsquare( d, (d-1) div 2,(d-1) div 2 +2 )+1..
                funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 )-1] cat 
                [ funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 )+1..d1 ] cat 
                [ funcpos_symsquare( d, (d-1) div 2,(d-1) div 2 +2 ), 
                  funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 ) ];
    end if;
        
    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;

BasisMatrixForSymSquareOmega := function( type, d, F : ww := 1/2 )

    return case< type |
            "Omega+": BasisMatrixForSymSquareOmegaPlus( d, F ),
            "Omega-": BasisMatrixForSymSquareOmegaMinus( d, F ),
            "Omega": BasisMatrixForSymSquareOmegaCircle( d, F : ww := ww ),
            default: false >;
end function;    

// the image of a matrix in SL( d, q ) in the sym square module.
  
__funcSLdqToSymSquare := function( g : type := "SL", ww := 1/2 )
    
    d := NumberOfRows( g );
    F := CoefficientRing( g );
    msets := [ [i,j] : i, j in [1..d] | i le j ];
    d1 := #msets;
    newmat := [];
    
    for p1 in msets do
        newrow := [];
        for p2 in msets do
            if p2[1] eq p2[2] then
                newrow[#newrow+1] := g[p1[1],p2[1]]*g[p1[2],p2[2]];
            else
                newrow[#newrow+1] := g[p1[1],p2[1]]*g[p1[2],p2[2]] 
                                  + g[p1[1],p2[2]]*g[p1[2],p2[1]];
            end if;
        end for;
        newmat[#newmat+1] := newrow;
    end for;

    newmat := GL( d1, F )!newmat;

    if type in { "Omega+", "Omega-", "Omega" } then
        conj := BasisMatrixForSymSquareOmega( type, d, F : ww := ww );
        codim := case< d mod Characteristic( F ) | 0: 2, default: 1>;
        newmat := conj*newmat*conj^-1; 
        newmat := [ newmat[i,j] : i, j in [1..d1-codim]];
        newmat := GL( d1-codim, F )!newmat;
    end if;

    return newmat;
end function;

/* the preimage of a matrix acting in the sym square module in the natural
   basis in SL( d, q )  */
    
__funcSymSquareToSLdq := function( g : type := "SL", ww := 1/2 )
    
    F := CoefficientRing( g );
    q := #F;
    dimg := NumberOfRows( g );
    dim := SolveSymSquareDimEq( dimg : type := type );

    if type in { "Omega+", "Omega-", "Omega" } then 
        gg := [ [ g[i,j] : j in [1..dimg]] : i in [1..dimg]];
        for i in [1..dimg] do
            gg[i][dimg+1] := 0;
            if dim mod Characteristic( F ) eq 0 then 
                gg[i][dimg+2] := 0;
            end if;
        end for;
    
        gg[dimg+1] := [0 : i in [1..dimg]] cat [1];
       
        if dim mod Characteristic( F ) eq 0 then
            gg[dimg+1] := [0 : i in [1..dimg]] cat [1,0];
            gg[dimg+2] := [0 : i in [1..dimg+1]] cat [1];
        else 
            gg[dimg+1] := [0 : i in [1..dimg]] cat [1];
        end if;

        gg := GL( #gg, q )!gg;
        conj := BasisMatrixForSymSquareOmega( type, dim, GF( q ) : ww := ww );
        g := conj^-1*gg*conj;      
        dimg := NumberOfRows( g );
    end if;

    omegaflag := type in { "Omega+", "Omega-", "Omega" } and 
                dim mod Characteristic( F ) eq 0;

    listii := [ funcpos_symsquare( dim, i, i ) : i in [1..dim]];
   
    A := [[]];
    
    //recover the first row
    i0 := Position( [ g[1,x] ne 0 : x in listii ], true ); 
    if i0 eq 0 then return false; end if;
    for i in [1..i0-1] do
        A[1,i] := GF(q)!0;
    end for;
    
    if not IsSquare( g[1,listii[i0]] ) then return false; end if;
    A[1,i0] := Sqrt( g[1,listii[i0]] );
    
    for i in [1..dim-i0] do
        A[1,i0+i] := 1/2*g[1,listii[i0]+i]/A[1,i0];
    end for;

    if omegaflag then 
        v := exists(x){ x : x in [1..dim] | x ne i0 and A[1,x] ne 0 }; 
        if v then 
            A[1,dim-i0+1] := 1/2*g[1,funcpos_symsquare( dim, x, dim-i0+1 )]/A[1,x];
        else 
            A[1,dim-i0+1] := 0;
        end if;
    end if; 

    // get the other rows
    // solve a system of linear equations
        
    if omegaflag and type eq "Omega+" then
        fbdn := [ funcpos_symsquare( dim, i, dim-i+1 ) : i in [1..dim/2]];
    elif omegaflag and type eq "Omega-" then 
        fbdn := [ funcpos_symsquare( dim, i, dim-i+1 ) : i in [1..dim/2-1]] cat 
                [ funcpos_symsquare( dim, dim div 2, dim div 2 ),
                funcpos_symsquare( dim, dim div 2+1, dim div 2+1 )];
    elif omegaflag and type eq "Omega" then 
        fbdn := [ funcpos_symsquare( dim, i, dim-i+1 ) : i in [1..(dim-1) div 2]] cat
                [ funcpos_symsquare( dim, (dim+1) div 2, (dim+1) div 2 )];
    else 
        fbdn := [];
    end if;

    mat := ZeroMatrix( GF( q ), dimg-#fbdn, dim );
    indrow := 0;
    for i in [1..dimg] do
        if i in fbdn then continue; end if;
        indrow := indrow + 1;
        x := funcposinv_symsquare( dim, i );
        i0 := x[1]; j0 := x[2];
        if i0 eq j0 then
            mat[indrow,i0] := A[1,i0];
        else
            mat[indrow,i0] := A[1,j0];
            mat[indrow,j0] := A[1,i0];
        end if;
    end for;
        
    for i in [2..dim] do
        if omegaflag and i eq dim then break; end if;
        vec := Vector( GF( q ), dimg-#fbdn, [g[i,j] : j in [1..dimg] | not j in fbdn ] );
        try sol := Solution( Transpose( mat ), vec ); 
        catch e return false; end try;
        A[i] := Eltseq( sol );
    end for;
    
    if omegaflag then
        mat := ZeroMatrix( GF( q ), dimg-#fbdn, dim );
      
        indrow := 0;
        for i in [1..dimg] do
            if i in fbdn then continue; end if;
            indrow := indrow + 1;
            x := funcposinv_symsquare( dim, i );
            i0 := x[1]; j0 := x[2];
            if i0 eq j0 then
                mat[indrow,i0] := A[2,i0];
            else
                mat[indrow,i0] := A[2,j0];
                mat[indrow,j0] := A[2,i0];
            end if;
        end for;

        vec := Vector( GF( q ), dimg-#fbdn, [g[2*dim-1,j] : j in [1..dimg] | 
                                            not j in fbdn ] );
        sol := Solution( Transpose( mat ), vec ); 
        A[dim] := Eltseq( sol );
    end if;

    return Matrix( GF( q ), dim, dim, A );
end function;
    
/* the following function produces the basis of 
   the underyling vector space of Sp( d, q ) that reflects the
   direct decompisition into 1-dim and 1-codim components. */
    
BasisMatrixForAltSquareSp := function( d, F )    
    
    d1 := Binomial( d, 2 );
    bas := IdentityMatrix( F, d1 );
        
    for i in [1..d/2-1] do
        bas[funcpos_altsquare( d, i, d-i+1 ), 
            funcpos_altsquare( d, d/2,d/2+1 )] := -1;
    end for;
    
    for i in [1..d/2-1] do
        bas[funcpos_altsquare( d, d/2,d/2+1 ),
            funcpos_altsquare( d, i, d-i+1 )] := 1;
    end for;
    
    if d mod Characteristic( F ) eq 0 then 
        bas[funcpos_altsquare( d, d/2-1,d/2+2 ), 
            funcpos_altsquare( d, d/2,d/2+1 )] := 0;
    end if;
    
    // reorder the basis
      
    if d mod Characteristic( F ) ne 0 then     
        list := [1..funcpos_altsquare( d, d/2,d/2+1 )-1] cat 
                [funcpos_altsquare( d, d/2,d/2+1 )+1..d1] cat 
                [funcpos_altsquare( d, d/2,d/2+1 )];
    else 
        list := [1..funcpos_altsquare( d,d/2-1,d/2+1)]
                cat [funcpos_altsquare( d,d/2-1,d/2+3)
                     ..funcpos_altsquare( d, d/2,d/2+1 )-1] cat 
                [funcpos_altsquare( d, d/2,d/2+1 )+1..d1] cat 
                [funcpos_altsquare( d, d/2,d/2+1 )] cat
                [funcpos_altsquare( d, d/2-1,d/2+2 )];
    end if;
    
    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;
    
    
/* writes the exterior square of an element of SX(d,q)     
   the standard basis for this procedure is, in the case of SL,
   v1.v2,...,v1.vd,v2.v3,...,v[d-1].vd */
    
__funcSLdqToAltSquare := function( g : type := "SL" )
                         
    d := NumberOfRows( g );
    msets := [ [i,j] : i, j in [1..d] | i lt j ];
    d1 := #msets;
    F := CoefficientRing( g );
    
    newmat := [];
    
    for p1 in msets do
        newrow := [];
        for p2 in msets do
            newrow[#newrow+1] := g[p1[1],p2[1]]*g[p1[2],p2[2]] 
                    - g[p1[1],p2[2]]*g[p1[2],p2[1]];
        end for;
        newmat[#newmat+1] := newrow;
    end for;
        
    newmat := Matrix( F, d1, d1, newmat );    
    
    /* In the case of Sp, the exterior square module is not irreducible.
       It always has a 1-dimensional component. When char F does not 
       divide the original dimension, then there is also a component
       of codimension 1.
         
       The dimension-1 component is generated by v1.vd+v2.v[d-1]+...+vd.v[d+1].
       The codimension-1 component when exists is generated by 
       v1.v2...v1.v[d-1],v1.vd-v[d/2].v[d/2+1],
       v2.v3,...,v2.vd-v[d/2].v[d/2+1],  
       v[d/2-1].v[d/2],...,v[d/2-1].v[d]-v[d/2].v[d/2+1]
       v[d/2+1].v[d/2+2],v[d/2+1].v[d],
       ...
       v[d-1].v[d]. */;  
         
    
    if type eq "Sp" then
        codim := case< d mod Characteristic( F ) | 0: 2, default: 1>;
        conj := BasisMatrixForAltSquareSp( d, F );
        newmat := conj*newmat*conj^-1;
        newmat := Matrix( F, d1-codim, d1-codim, 
                  [[ newmat[i,j] : j in [1..d1-codim] ] : i in [1..d1-codim]]);
    end if; 
            
    return newmat;
end function;
    
/* wrapping function for Greenhill's algorithm */

__funcAltSquareToSLdq := function( Y : type := "SL" )
    
    // find the dimensions of Y and the original matrix X
    
    dimY := Nrows( Y );
    F := CoefficientRing( Y );
    dimX := SolveAltSquareDimEq( dimY : type := type );

    if dimX eq 0 then
        return false, _;
    end if;    
    codim := case< dimX mod Characteristic( F ) | 0: 2, default: 1 >;
    
    // if the type is Sp, then we recover the original Y from Y

    if type ne "Sp" then
        return __funcAltSquareToSLdq_func( Y );
    end if; 

    // type is Sp

    G0 := Sp( dimX, #F );
    X0 := One( G0 );
    Y0 := Y^0;
    nrtries := 0; 
    repeat 
        YY := Y*Y0;
        newYY := Matrix( F, dimY+1, dimY+1, 
                    [ Eltseq( YY[i] ) cat [ 0 ] : i in [1..dimY]] cat
                   [[ 0 : i in [1..dimY]] cat [1]] );
        if codim eq 2 then
            newYY := Matrix( F, dimY+2, dimY+2, 
                [ Eltseq( newYY[i] ) cat [ 0 ] : i in [1..dimY+1]] cat
                [[ 0 : i in [1..dimY+1]] cat [1]] );
        end if;
                         
        conj := BasisMatrixForAltSquareSp( dimX, F );
        YY0 := conj^-1*newYY*conj;
        try 
            X := __funcAltSquareToSLdq_func( YY0 : chardivdim := codim eq 2 );
        catch e
            X := false;
        end try;

        if codim eq 2 and Category( X ) ne BoolElt then 
            X := X*X0^-1;
            if __funcSLdqToAltSquare( X : type := "Sp" ) ne Y then
                X := false; 
            end if; 
        end if;

        if codim eq 2 and Category( X ) eq BoolElt then
            X0 := Random( G0 );
            Y0 := __funcSLdqToAltSquare( X0 : type := "Sp" );
        end if; 
        nrtries := nrtries + 1; 
    until codim eq 1 or Category( X ) ne BoolElt or nrtries ge 10; 
    
    return X;  
end function;
    
    
__funcAltSquareToSLdq_func_old := function( Y : type := "SL" )
    
        // find the dimensions of Y and the original matrix X
            
    dimY := Nrows( Y );
    F := CoefficientRing( Y );
    dimX := SolveAltSquareDimEq( dimY : type := type );
    codim := case< dimX mod Characteristic( F ) | 0: 2, default: 1 >;
    
    // if the type is Sp, then we recover the original Y from Y
      
    if type eq "Sp" then
       newY := Matrix( F, dimY+1, dimY+1, 
                       [ Eltseq( Y[i] ) cat [ 0 ] : i in [1..dimY]] cat
                       [[ 0 : i in [1..dimY]] cat [1]] );
       dimY := dimY+1;
       if codim eq 2 then
           newY := Matrix( F, dimY+1, dimY+1, 
                           [ Eltseq( newY[i] ) cat [ 0 ] : i in [1..dimY]] cat
                           [[ 0 : i in [1..dimY]] cat [1]] );
           dimY := dimY+1;
       end if;
                         
       conj := BasisMatrixForAltSquareSp( dimX, F );
       Y := conj^-1*newY*conj;
    end if;
    
    if dimX eq 0 then
        return false;
    end if;
        
   /* a function that returns the entry of Y that corresponds to 
       position ({a,b},{c,d}) */
      
    Y_ := function( a, b, c, d )
        return Y[funcpos_altsquare( dimX, a, b ),
                 funcpos_altsquare( dimX, c, d )];
    end function;        
    
    // find the leading entry of Y
      
    for i in [1..dimY] do
        if Y[1,i] ne 0 then
            y0 := i;
            break;
        end if;
    end for;    
            
    /* now the leading entry is Y[1,y0]. Compute the labels of the leading row
       and column. In this implementation, Y is invertible, and so the first
       row is always the leading row. */
      
    lr := <1,2>;
    lc := funcposinv_altsquare( dimX, y0 );

    // follow the notation of the paper
    p := lr[1]; q := lr[2];
    alpha := lc[1]; beta := lc[2];
    
    X := [ [] : x in [1..dimX]];
        
    if alpha ge 3 then
        for j in [1..dimX] do
            for k in [1..alpha-1] do
                for l in [k+1..alpha-1] do
                    if p ne j and Y_( p, j, k, l ) ne 0 then
                        return false;
                    end if;
                end for;
            end for;
        end for;
    end if;

    for l in [alpha..beta] do
        if l gt alpha and l ge 3 then
            for j in [p+1..dimX] do
                for k in [1..l-2] do
                    if Y_( p, j, k, l-1 ) ne 0 then
                        return false;
                    end if;
                end for;
            end for;
        end if;
        
        muset := { mu : mu in [1..dimX] | mu ne l and Y_( p, q, mu, l ) ne 0 };
        
        if #muset gt 0 then
            mu := Min( muset );
            eta := Y_( p, q, mu, l )^-1;
            rnuset := { <r,nu> : r in [q+1..dimX], nu in [1..dimX] | 
                    nu ne l and nu ne mu and Y_(p,r,nu,l) ne 
                         eta*Y_(p,r,l,mu)*Y_(p,q,nu,l)};
                                    
            if #rnuset gt 0 then
                rnu := Min( rnuset );
                r := rnu[1]; nu := rnu[2]; 
                delta := nu lt mu select 1 else -1;
                
                if mu lt l or l lt nu or Y_(p,r,nu,l) ne 0 then
                    theta := Y_(p,r,nu,l)-eta*Y_(p,r,l,mu)*Y_(p,q,nu,l);
                    sigma := Y_(q,r,l,mu);
                    psi := Y_(p,q,nu,mu);
                    x := theta^-1*(Y_(q,r,nu,l)-eta*sigma*Y_( p, q, nu, l ));
                    if mu lt l then 
                        y := 0;

                        if nu lt l then
                            z := -delta*eta*theta^-1*Y_(q,r,nu,mu);
                        elif l lt nu then
                            z := -eta*theta^-1*(Y_(q,r,nu,mu)-eta*sigma*psi);
                        else
                            error(0);
                        end if;
                    else
                        if nu lt l then 
                            y := Y_( p, r, nu, l )^-1*Y_(p,r,nu,mu);
                            z := eta*theta^-1*(Y_(q,r,nu,mu)-
                                         eta*sigma*Y_( p, q, nu, l )*y-
                                         theta*x*y);
                        else
                            tau := Y_(p,r,l,mu);
                            y := -delta*theta^-1*
                                 (Y_(p,r,nu,mu)-eta*tau*psi);
                            z := -delta*eta*theta^-1*(Y_(q,r,nu,mu)-
                                         eta*sigma*psi+delta*theta*x*y);
                        end if;
                        
                    end if;
                    if z eq 0 then return false, 1, l; end if;
                    
                    try w := Sqrt( z ); catch e return false, 2, l; end try;
                    
                    X[p,l] := w^-1;
                    X[q,l] := w^-1*x;
                    X[p,mu] := w^-1*y;

                    // equation (12)
                    for j in [p+1..dimX] do
                        if j ne q then
                            zeta := j lt q select 1 else -1;
                            X[j,l] := eta*(Y_(p,j,mu,l)*X[q,l]+
                                           zeta*Y_(q,j,mu,l)*X[p,l]);
                        end if;
                    end for;
                    
                    // fill first rows with zeros
                    for s in [1..l-1] do
                        X[p,s] := 0;
                    end for;
                    
                    // equation (13)
                    for s in [l+1..dimX] do;
                        if mu lt l then  
                            X[p,s] := eta*Y_(p,q,mu,s)*X[p,l];
                        elif l lt mu then 
                            delta := s lt mu select 1 else -1;
                            if mu ne s then
                                X[p,s] := eta*(Y_(p,q,l,s)*X[p,mu]+
                                               delta*Y_(p,q,mu,s)*X[p,l]);
                            end if;
                        end if;
                    end for;
                    
                    // equation (11)
                    for j in [p+1..dimX] do
                        for s in [1..l-1] do
                            X[j,s] := -X[p,l]^-1*Y_(p,j,s,l);
                        end for;
                        
                        for s in [l+1..dimX] do
                            X[j,s] := X[p,l]^-1*(Y_(p,j,l,s)+X[p,s]*X[j,l]);
                        end for;
                        
                    end for;
                    return MatrixAlgebra( F, dimX )!X;
                end if;
            end if;
        end if;
    end for;
end function;