/* 
    smalldimreps.m                                                          RecogniseSmallDim

    This file contains some practical functions to handle small-dimensional representations of 
    the classical groups for the RecogniseSmallDim package.
    Written by Csaba Schneider.
    Analysed in December, 2023
*/

import "greenhill.m":__funcAltSquareToSLdq_func;

// aux functions for small dim recognition
// solve the equation m = d(d+1)/2
  
SolveSymSquareDimEq := function( m : type := "SL" )

    // the dimension of the symmetric square of the natural modules for the Omega groups 
    // has dimension reduded by one or two
    // here we add one
    if type in { "Omega+", "Omega-", "Omega" } then
        m +:= 1;
    end if;

    // we have to solve the equation 2m = d^2+d for d
    // the positive solution is given by the following
    sol := (-1+Sqrt( 1+8*m ))/2;
    
    // if this solution is not an integer then 
    // we might be in the Omega situation when the characteristic divides the 
    // defining dimension. In this case the dimension of the module is reduced by two, 
    // so we add one more
    if sol ne Round( sol ) and type in {"Omega+", "Omega-", "Omega"} then
        m +:= 1;
        sol := (-1+Sqrt( 1+8*m ))/2;
    end  if;
    
    // we check if the result is OK. if not we return zero
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if; 
end function;
    
// solve the equation m = d(d-1)/2. This function does the same as the previous. 
// See the comments of the previous function
  
SolveAltSquareDimEq := function( m : type := "SL"  )

    if type eq "Sp" then
        m +:= 1;
    end if;
      
    sol := (1+Sqrt( 1+8*m ))/2;
    
    if sol ne Round( sol ) and type eq "Sp" then
        m +:= 1;
        sol := (1+Sqrt( 1+8*m ))/2;
    end  if;
    
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if;
end function;

    
/* position of basis element eij in the standard basis of the 
   sym square module. the basis of the sym square module is 
   e1.e1, e1.e2, e1.e3,...,e1.en,e2.e2,...,e2.en,...,en.en. 
   
   In the case of the Omega groups, there is a codimension one component whose basis is the following. 
   (We write ij for ei.ej.)
   
   Omega+
   ======
   d is n/2

   The codim-1 component is spanned by  
   11, 12, 23...... 1{n-1},        1n-d{d+1}, 
       22,...,      2{n-1}-d{d-1}, 2n
                    dd, d{d+2},...,dn,
                                   nn. 
   
   The one-dim component is generated by 1n + 2{n-1} + ... + d{d+1}. The one dim component lies in 
   the codim one component exactly when p | n. 
   
   Omega-
   ======
   d is (n-2)/2 and z0 := -Nonsquare( GF( q ));
   
   The Omega- group is supposed to preserve the form in which (w1,w1) = 1 and (w2,w2) = z0 = -Nonsquare( F ).
   This is in line with older versions of Magma (up to about 2.25). In newer versions, Omega- preserves another form.

   TODO: Update the Omega- functions for the newer form. 

   w1 and w2 are the basis elements indexed by d+1 and d+2.
   
   The codim one component is spanned by 
   11, 12, ..., 1n-z0^-1*{d+2}{d+2}
   22, 23, ..., 2{n-1}-z0^-1*{d+2}{d+2}
   ...
   dd-z0^-1{d+2}{d+2},d{d+1},...,dn,
   {d+1}{d+1}-z0^-1{d+2}{d+2}, {d+1}{d+2}, ..., {d+1}n
   {d+2}{d+3},...,{d+1}n
   ...
   nn

   The one-dim component is spanned by 
   1n+2{n-1}+...+dd+(1/2){d+1}{d+1}+(1/2)z_0^-1.

   The one-dim component is contained in the codim-one component if and only if p | n+1.


   OmegaCircle
   ===========
   
   Omega+
   ======
   d is (n-1)/2

   The codim-1 component is spanned by  
   11, 12, 23...... 1{n-1},                     1n-2{d+1}{d+1}, 
       22,...,      2{n-1}-2{d+1}{d+1},         2n
           dd, d{d+1}, d{d+2}-2{d+1}{d+1}, ..., dn
                    {d+1}{d+2},...,             {d+1}n,
                                                nn. 
   
   The one-dim component is generated by 1n + 2{n-1} + ... + d{d+2}+{d+1}{d+1}. The one dim component lies in 
   the codim one component exactly when p | n. 

   */

// returns the index of vi.vj in the basis of the large component of the symmetric square
// also indicates if the vi.vj element is "pure" or it is modified as the description above.
  
funcpos_symsquare := function( dim, i, j : type := "SL" )

    // we must have i <= j
    if i gt j then 
        tmp := i; i := j; j := tmp;
    end if;

    pos := (i-1)*dim-(i*(i-3)) div 2 + j - i;
    // if the group is not Omega, then return
    if type eq "SL" then return pos, true; end if;

    // this needs modifying when the group is one of the Omega groups

    d0 := case< type | "Omega+": dim div 2, "Omega-": dim div 2 + 1, "Omega": (dim +1) div 2, default: false >;
    
    if type eq "Omega+" then
        if i eq d0 and j eq d0+1 then
            return 0, false;
        elif i ge d0 and j ge d0+1 then
            return pos-1, false;
        elif i + j eq dim +1 then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            

    if type eq "Omega-" then
        if i eq d0 and j eq d0 then
            return 0, false;
        elif i ge d0 and j ge d0 then
            return pos-1, false;
        elif (i lt d0-1 and i + j eq dim +1) or (i eq d0-1 and j eq d0-1) then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            
    
    if type eq "Omega" then
        if i eq d0 and j eq d0 then
            return 0, false;
        elif i ge d0 and j ge d0 then
            return pos-1, false;
        elif (i lt d0 and i + j eq dim +1) then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            
     
end function;

// the inverse of the last function. returns the values k, l such that 
// the i-th basis element corresponds to vk.vl + modification.
// the second output indicates if there is modification

funcposinv_symsquare := function( dim, i : type := "SL" )
    
    d0 := dim div 2;

    // check if the index is >= then the index of the omitted basis element.
    if type eq "Omega+" then
        i0 := (d0-1)*dim-(d0*(d0-3)) div 2 + 1; //funcpos_symsquare( dim, d0, d0+1 );
        if i ge i0 then
            i +:= 1;
        end if;
    elif type eq "Omega-" then
        i0 := d0*dim-(d0*(d0-2)) div 2; //funcpos_symsquare( dim, d0+1, d0+1 );
        if i ge i0 then
            i +:= 1;
        end if;
    end if;

    // calculate the first component of the output
    delta := 4*dim^2+4*dim+1-8*i;
    k := Ceiling(((2*dim+1)-Sqrt(delta))/2);

    j := i-(k-1)*(2*dim-k) div 2;
    flag := false;    
    if type eq "Omega+" and k+j eq dim+1 then
        flag := true;
    elif type eq "Omega-" and (k lt dim div 2 and k+j eq dim+1) or 
                            (k eq dim div 2 and j eq dim div 2) then
        flag := true;
    end if;

    return <k,j>, flag;
end function;

/* Position of basis element eiej in the standard basis of the 
   alt square module. 
   
   The standard basis of the altsquare of the natural module is as follows. We write ij for eiej.
   
   12, 13, 14, 25,..., 1n
       23, 24, 25,..., 2n 
           34, 35,..., 3n
                   (n-1)n. 
                   
    #### In the case of symplectic spaces, the basis is going to be as follows 
    d being equal to n/2 = dim V/2.
    
    12, 13, 14, ..., 1(n-1),          1n-d(d+1)
        23, 24       2(n-1) - d(d+1), 1n
        ... 
            (d-1)d, (d-1)(d+1), [(d-1)(d+2)], ..., (d-1)n
             d(d+2), d(d+3),...,      dn
        ...
                                  (n-1)n. 
                                  
    In the case when p divides the dimension of V, the basis element (d-1)(d+2) is ignored. */
  
funcpos_altsquare := function( dim, i, j : type := "SL" )
    
    // i < j, if not, then we swap. We also calculate the natural index.
    if i gt j then
        temp := i; i := j; j := temp; 
    end if; 
    pos := (((2*dim-i)*(i-1)) div 2)+j-i;
    
    // in the case of SL the position is returned
    
    if type eq "SL" then return pos; end if;
    
    /* in the case of Sp the position needs modifying
       in this case we also return two values to indicate when
       a standard basis element is of the form <i,j> - <d,d+1>
       also remember that <d,d+1> does not occur in the standard 
       basis and so after this element the positions need shifting.
       */                            

    d := dim div 2;
    
    if type eq "Sp" then
        if i eq d and j eq d+1 then
            return 0, false;
        elif i ge d and j gt d+1 then
            return pos-1, false;
        elif i + j eq dim + 1 then
            return pos, true;
        else
            return pos, false;
        end if;
    end if;            
    
end function;

// the inverse of the last function. It converts the number i to <i1,i2> such that the i-th basis element is 
// ei1.ei2

funcposinv_altsquare := function( dim, i : type := "SL" )
    
    k := 0; d := dim div 2;
    
    // in the case of Sp, if the value of i is greater than the value 
    // that corresponds to ed.e(d+1), we need to increas i by one to account 
    // for the missing basis element ed.e(d+1)
    if type eq "Sp" then
        i0 :=  (((2*dim-d)*(d-1)) div 2)+1; // the value of funcpos_altsquare( dim, d, d+1 );
        if i ge i0 then
            i +:= 1;
        end if;
    end if;
        
    // we determine the first component of the output by finding the largest k such that 
    // equation k*(n-(k+1)/2) < i 
    // this is done by solving the quadratic equation k*(n-(k+1)/2) - i = 0
    // that is k^2 - (2dim-1)k+2i = 0 
    delta := 4*dim^2-4*dim+1-8*i;
    k := Ceiling(((2*dim-1)-Sqrt(delta))/2);

    // we compute the second component and modify the result   
    j := k+i-((k-1)*(2*dim-k)) div 2; 
    if type eq "SL" then
        return <k,j>, _;
    elif type eq "Sp" and k+j eq dim+1 then
        return <k,j>, true;
    elif type eq "Sp" and k+j ne dim+1 then
        return <k,j>, false;
    end if;  
end function;

// gets the values for the form preserved by Omega-
// They are used in the construction of the basis of Omega-. 
// See the comments above.

GetValueOmegaMinus := function( q )

    gamma := -Nonsquare( GF( q ));
    return -1/gamma, 1/2*gamma^-1;
end function;

// tha basis transform matrix for sym square of Omega+

BasisMatrixForSymSquareOmegaPlus := function( d, F )    
    
    d1 := (d*(d+1)) div 2;
    d0 := d div 2;
    bas := IdentityMatrix( F, d1 );
        
    for i in [1..d0-1] do  
        bas[funcpos_symsquare( d, i, d-i+1 ), 
            funcpos_symsquare( d, d0, d0+1 )] := -1;
    end for;
    
    for i in [1..d0-1] do
        bas[funcpos_symsquare( d, d0, d0+1 ),
            funcpos_symsquare( d, i, d-i+1 )] := 1;
    end for;

    if d mod Characteristic( F ) eq 0 then 
        bas[funcpos_symsquare( d, d0-1, d0+2 ), 
            funcpos_symsquare( d, d0, d0+1 )] := 0;
    end if;
        
    // reorder the basis
      
    if d mod Characteristic( F ) ne 0 then
        list := [1..funcpos_symsquare( d, d0, d0+1 )-1] cat 
                [funcpos_symsquare( d, d0, d0+1 )+1..d1] cat 
                [funcpos_symsquare( d, d0, d0+1 )];
    else
        list := [1..funcpos_symsquare( d, d0-1, d0+1)] cat 
                [funcpos_symsquare( d, d0-1, d0+3 )
                 ..funcpos_symsquare( d, d0, d0+1 )-1] cat 
                [funcpos_symsquare( d, d0, d0+1 )+1..d1] cat 
                [funcpos_symsquare( d, d0, d0+1 )] cat
                [funcpos_symsquare( d, d0-1, d0+2 )];
    end if;

    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;

// basis transform matrix for SymSquare Omega-

BasisMatrixForSymSquareOmegaMinus := function( d, F )    
    
    d1 := (d*(d+1)) div 2;
    d0 := d div 2 + 1;
    bas := IdentityMatrix( F, d1 );
    
    z1, z2 := GetValueOmegaMinus( #F );
    for i in [1..d0-2] do  
        bas[funcpos_symsquare( d, i, d-i+1 ), 
            funcpos_symsquare( d, d0, d0 )] := z1;
    end for;
    
    bas[funcpos_symsquare( d, d0-1, d0-1 ), 
            funcpos_symsquare( d, d0, d0 )] := z1;
    

    for i in [1..d0-2] do
        bas[funcpos_symsquare( d, d0, d0 ),
            funcpos_symsquare( d, i, d-i+1 )] := 1;
    end for;

    bas[funcpos_symsquare( d, d0, d0 ),
            funcpos_symsquare( d, d0-1, d0-1 )] := 1/2;

    if d mod Characteristic( F ) eq 0 then 
        bas[funcpos_symsquare( d, d0, d0 ),
                funcpos_symsquare( d, d0, d0 )] := (d0-2+1/2)*z1;
    else 
        bas[funcpos_symsquare( d, d0, d0 ),
                funcpos_symsquare( d, d0, d0 )] := z2;
    end if;

    if d mod Characteristic( F ) eq 0 then  
        bas[funcpos_symsquare( d, d0-1, d0-1 ), 
            funcpos_symsquare( d, d0, d0 )] := 0;
    end if;

    // reorder the basis

    if d mod Characteristic( F ) ne 0 then  
        list := [1..funcpos_symsquare( d, d0, d0 )-1] cat 
                    [funcpos_symsquare( d, d0, d0 )+1..d1] cat 
                    [funcpos_symsquare( d, d0, d0 )];
    else
        list := [1..funcpos_symsquare( d, d0-1,d0-1 )-1] cat
                [funcpos_symsquare( d, d0-1 , d0-1 )+1..
                funcpos_symsquare( d, d0, d0 )-1] cat 
                    [funcpos_symsquare( d, d0, d0 )+1..d1] cat
                    [funcpos_symsquare( d, d0-1, d0-1 )] cat
                    [funcpos_symsquare( d, d0, d0 )];
    end if;
        
    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;

// basis matrix for Sym square of Omega. The parameter controls the value of (w_1,w_1).
// sometimes we need to change this value from the Magma default.

BasisMatrixForSymSquareOmegaCircle := function( d, F : ww := 1/2 );    
    
    a := F!(-1/ww); b := 1/(2*ww);
    d1 := (d*(d+1)) div 2;
    d0 := (d+1) div 2;
    bas := IdentityMatrix( F, d1 );
        
    for i in [1..d0-1] do  
        bas[funcpos_symsquare( d, i, d-i+1 ), 
            funcpos_symsquare( d, d0, d0 )] := a;
    end for;
    
    for i in [1..d0-1] do
        bas[funcpos_symsquare( d, d0, d0 ),
            funcpos_symsquare( d, i, d-i+1 )] := 1;
    end for;

    bas[funcpos_symsquare( d, d0, d0 ),
        funcpos_symsquare( d, d0, d0 )] := b;

    if d mod Characteristic( F ) eq 0 then  
        bas[funcpos_symsquare( d, d0-1, d0+1 ), 
            funcpos_symsquare( d, d0, d0 )] := 0;
    end if;
        
    // reorder the basis
      
    if d mod Characteristic( F ) ne 0 then 
        list := [1..funcpos_symsquare( d, d0, d0 )-1] cat 
                    [funcpos_symsquare( d, d0, d0 )+1..d1] cat 
                    [funcpos_symsquare( d, d0, d0 )];

    else 
        list := [1..funcpos_symsquare( d, d0-1, d0+1 )-1] cat 
                [funcpos_symsquare( d, d0-1, d0+1 )+1..
                funcpos_symsquare( d, d0, d0 )-1] cat 
                [ funcpos_symsquare( d, d0, d0 )+1..d1 ] cat 
                [ funcpos_symsquare( d, d0-1, d0+1 ), 
                  funcpos_symsquare( d, d0, d0 ) ];
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
    //msets := [ [i,j] : i, j in [1..d] | i le j ];
    d1 := (d*(d+1) div 2);
    newmat := ZeroMatrix( F, d1 );

    rowcount := 0;
    
    for p1 in [1..d], p2 in [p1..d] do
        rowcount +:= 1; colcount := 0;
        for q1 in [1..d], q2 in [q1..d] do
            colcount +:= 1;
            if q1 eq q2 then
                newmat[rowcount,colcount] := g[p1,q1]*g[p2,q2];
            else
                newmat[rowcount,colcount] := g[p1,q1]*g[p2,q2] 
                                  + g[p1,q2]*g[p2,q1];
            end if;
        end for;
    end for;

    if type in { "Omega+", "Omega-", "Omega" } then
        conj := BasisMatrixForSymSquareOmega( type, d, F : ww := ww );
        codim := case< d mod Characteristic( F ) | 0: 2, default: 1>;
        newmat := conj*newmat*conj^-1; 
        newmat := Submatrix( newmat, 1, 1, d1-codim, d1-codim ); 
    end if;

    return newmat;
end function;

// gets a nonzero entry of a matrix with index i, j that satisfy a condition
// cond must be a function cond( i, j ) that returns true or false
get_nonzero_entry := function( mat, cond )

    n := Nrows( mat );
    i := 1; j := 1;
    repeat 
        if cond( i, j ) and mat[i,j] ne 0 then return mat[i,j], i, j; end if;
        j +:= 1; 
        if j eq n+1 then 
            j := 1;
            i +:= 1;
        end if;
        if i eq n+1 then 
            error( "Did not find nonzero entry with these conditions." );
            end if;
    until false;
end function;

// returns the first number n between start and stop such that cond(n) eq true

first_number := function( start, stop, cond )

    n := start;
    repeat 
        if cond( n ) then return n; end if; 
        n +:= 1;
        if n gt stop then 
            error( "no number found with condition." );
        end if;
    until false;
end function;


/* 
   the preimage of a matrix acting in the sym square module in the natural
   basis in SL( d, q )  

   Anna Sucker's version of the symmetric square root function.
   the input is the symmetric square of a determinant one matrix. The output is its symmetric square root.
   The basic procedure is relatively simple, there is complication when the type is orthogonal and 
   the characteristic divides the dimension.

   For more datails, see Anna's MSc Thesis "Computing the Representations of Classical
   Groups on the Symmetric Square".

*/
    
__funcSymSquareToSLdq := function( g : type := "SL", ww := 1/2, new_alg := false )
    

    // extract data
    F := CoefficientRing( g );
    q := #F;
    dimg := NumberOfRows( g );

    // the dimension of the output matrix
    dim := SolveSymSquareDimEq( dimg : type := type );

    // in the orthogonal cases, we insert a [1] or a [[1,0],[0,1]] block to the 
    // right bottom corner. The second of these options will result in a matrix with some 
    // incorrect entries. This will be addressed after ***.
    if type in { "Omega+", "Omega-", "Omega" } then 
        if dim mod Characteristic( F ) eq 0 then 
            g := DiagonalJoin( g, Matrix( F, 2, 2, [1, 0, 0, 1 ]));
        else
            g := DiagonalJoin( g, Matrix( F, 1, 1, [1] ));
        end if; 

        conj := BasisMatrixForSymSquareOmega( type, dim, GF( q ) : ww := ww );
        g := conj^-1*g*conj;      
        dimg := NumberOfRows( g );
    end if;

    // we check if we are in the problematic case; that is when 
    // the type is orthogonal and the characteristic divides the dimension
    orthogonal_p_divides_dim := type in { "Omega+", "Omega-", "Omega" } and 
                                dim mod Characteristic( F ) eq 0;

    // this will hold the output matrix
    X := ZeroMatrix( F, dim );  

    // find smallest b0 such that X[1,b0] ne 0
    b0 := 0;
    for b in [1..dim] do 
        posbb := funcpos_symsquare( dim, b, b ); 
        if g[1,posbb] ne 0 then 
            v, z := IsSquare( g[1,posbb] );
            if not v then return false; end if;  
            X[1,b] := z;
            b0 := b;
            break;
        end if;    
    end for;

    X1b0_inv := X[1,b0]^-1; // we'll need this several times
    
    // the column with index dim - b0 + 1 needs to treated differently
    // in the orthogonal cases when p | dim
    col_omitted := dim - b0 + 1;

    // fill in the first row
    for i in [1..dim] do
        if i eq b0 then continue; end if; // skip i eq b0 
        X[1,i] := (1/2)*X1b0_inv*g[1,funcpos_symsquare( dim, b0, i )];
    end for;

    // fill in the b0th column
    pos_b0b0 := funcpos_symsquare( dim, b0, b0 );
    for i in [2..dim] do 
        X[i,b0] := X1b0_inv*g[i,pos_b0b0];
    end for;

    // fill in the lower left half-matrix
    for i in [2..dim], j in [1..b0-1] do
        // in the orthogonal p | dim case, the last row and the 
        // col_omitted column will be filled in later.
        if orthogonal_p_divides_dim and ( i eq dim or j eq col_omitted ) then continue; end if; 
        X[i,j] :=X1b0_inv*(g[i,funcpos_symsquare( dim, j, b0 )] - X[1,j]*X[i,b0]);
    end for; 

    // fill in the lower right half-matrix 
    for i in [2..dim], j in [b0+1..dim] do 
        // col_omitted column will be filled in later.
        if orthogonal_p_divides_dim and ( i eq dim or j eq col_omitted ) then continue; end if; 
        X[i,j] := X1b0_inv*(g[i,funcpos_symsquare( dim, b0, j )] - X[1,j]*X[i,b0] );
    end for;

    // we are done if the classical type is not orthogonal
    if not orthogonal_p_divides_dim then return X; end if;

    /*

        *** HERE STARTS THE COMPLICATED PART                    ***
        *** THE TYPE IS ORTHOGONAL AND P DIVIDES THE DIMENSION  ***
    
    */

    // find c0 such that X[2,c0] is nonzero and c0 is not b0 or col_omitted

    cond := case< type | 
            "Omega+": func< x, y | x ge 2 and y ne b0 and y ne col_omitted >,
            "Omega": func< x, y | x ge 2 and y ne b0 and y ne col_omitted  and 2*y ne dim + 1 >,
            "Omega-": func< x, y | x ge 2 and y ne b0 and y ne col_omitted  and y ne dim/2 and y ne dim/2 + 1 >, 
            default: false >;

    X2c0, r0, c0 := get_nonzero_entry( X, cond );
    // we will deal with the (dim,dim-c0+1) position
    m0 := dim-c0+1;

    // fill in the last row
    // first the element in the c0 position
    Xr0c0inv := X2c0^-1;
    X[dim,c0] := Xr0c0inv*g[funcpos_symsquare( dim, r0, dim ),funcpos_symsquare( dim, c0, c0 )];
    // then the rest of the last row
    pos_r0_dim := funcpos_symsquare( dim, r0, dim );
    for j in [1..dim] do 
        if j eq c0 then continue; end if; 
        X[dim,j] := Xr0c0inv*(g[pos_r0_dim, funcpos_symsquare( dim, j, c0 )] - X[r0,j]*X[dim,c0]); 
    end for;

    // fill in the column with index 1-b0+1
    // find nonzero element in column different from b0

    cond := case< type | 
                    "Omega+": func< n | n ne b0 and n ne m0 and n ne col_omitted >,
                    "Omega" : func< n | n ne b0 and n ne m0 and n ne col_omitted and n ne (dim+1)/2 >,
                    "Omega-": func< n | n ne b0 and n ne m0 and n ne col_omitted and 
                            not { z : z in [1..dim] | X[z,n] ne 0 } subset { dim div 2, dim div 2 + 1 } >,
                    default: false >;

    col_ind := first_number( 1, dim, cond );

    cond := case< type | 
                "Omega+":  func< x, y | y eq col_ind >,
                "Omega" :  func< x, y | y eq col_ind and x ne (dim + 1)/2 >, 
                "Omega-":  func< x, y | y eq col_ind and x ne dim/2 and x ne dim/2 + 1 >,
                default: false >;
    Xdci, d0, _ := get_nonzero_entry( X, cond );
    
    // first, the element in d0 position
    Xd0_colind_inv := Xdci^-1;
    X[d0,col_omitted] := (1/2)*Xd0_colind_inv*g[funcpos_symsquare( dim, d0, d0 ), funcpos_symsquare( dim, col_ind, col_omitted )];
    pos_ci_co := funcpos_symsquare( dim, col_ind, col_omitted );
    // the rest of the column
    for i in [1..dim] do
        if i eq d0 then continue; end if;  
        X[i,col_omitted] := Xd0_colind_inv*(g[funcpos_symsquare( dim, i, d0 ), pos_ci_co ]-X[i,col_ind]*X[d0,col_omitted]);
    end for;

    // at this point the matrix is almost ready. we need to put in the entries in the (dim,dim-c0+1)
    // and (dim-d0+1,col_omitted) positions.
    
    // get a suitable non-zero entry
    Xk1l1, k1, l1 := get_nonzero_entry( X, func< x, y | x ne 1 and x ne dim and x ne m0 and 
                                    y ne m0 and y ne c0 and y ne col_omitted > );
    // compute the (dim,n0) entry
    X[dim,m0] := Xk1l1^-1*(g[funcpos_symsquare( dim, dim, k1 ), funcpos_symsquare( dim, m0, l1 )]-X[dim,l1]*X[k1,m0]);
    //error( 3333 );

    // now the (dim-d0+1,col_omitted)-entry
    row := dim-d0+1;
    Xk2l2, k2, l2 := get_nonzero_entry( X, func< x, y | x ne d0 and x ne row and y ne b0 and y ne col_omitted >);
    X[row,col_omitted] := Xk2l2^-1*(g[funcpos_symsquare( dim, row, k2 ), funcpos_symsquare( dim, col_omitted, l2 )] - 
                          X[row,l2]*X[k2,col_omitted]);
    
    return X;
end function;
    
/* the following function produces the basis of 
   the underyling vector space of Sp( d, q ) that reflects the
   direct decompisition into 1-dim and 1-codim components. 
   
   See the comment at #### for a description of this basis.*/
    
BasisMatrixForAltSquareSp := function( d, F )    
    
    // the dimension of the matrix and d/2
    d1 := (d*(d-1)) div 2;
    d0 := d div 2;

    // start with the identity matrix
    bas := IdentityMatrix( F, d1 );
    
    // insert -1 in the row of i.(d-i+1 ) and in the column d0.(d0+1)
    for i in [1..d0-1] do
        bas[funcpos_altsquare( d, i, d-i+1 ), 
            funcpos_altsquare( d, d0, d0+1 )] := -1;
    end for;
    
    // put 1.d + 2.(d-1) + ... + d0.(d0+1) into the row of d0.(d0+1)
    for i in [1..d0-1] do
        bas[funcpos_altsquare( d, d0, d0+1 ),
            funcpos_altsquare( d, i, d-i+1 )] := 1;
    end for;
    
    // if p divides the characteristic make the entry at row (d0-1).(d0+2) and col d0.(d0+1) zero
    if d mod Characteristic( F ) eq 0 then 
        bas[funcpos_altsquare( d, d0-1, d0+2 ), 
            funcpos_altsquare( d, d0, d0+1 )] := 0;
    end if;
    
    // reorder the basis so that it comes in the order at ####
      
    if d mod Characteristic( F ) ne 0 then     
        list := [1..funcpos_altsquare( d, d0, d0+1 )-1] cat 
                [funcpos_altsquare( d, d0, d0+1 )+1..d1] cat 
                [funcpos_altsquare( d, d0, d0+1 )];
    else 
        list := [1..funcpos_altsquare( d,d0-1, d0+1)] cat 
                [funcpos_altsquare( d,d0-1, d0+3)..funcpos_altsquare( d, d0, d0+1 )-1] cat 
                [funcpos_altsquare( d, d0, d0+1 )+1..d1] cat 
                [funcpos_altsquare( d, d0, d0+1 )] cat
                [funcpos_altsquare( d, d0-1,d0+2 )];
    end if;
    
    sw := PermutationMatrix( F, Sym( d1 )!list );
    bas := sw*bas;
    
    return bas;
end function;
    
    
/* writes the exterior square of an element of SX(d,q)     
   the standard basis for this procedure is, in the case of SL,
   v1.v2,...,v1.vd,v2.v3,...,v[d-1].vd */
    
__funcSLdqToAltSquare := function( g : type := "SL" )
                         
    // extract info from input
    d := NumberOfRows( g );
    d1 := (d*(d-1)) div 2; 
    F := CoefficientRing( g );

    // the matrix to hold the result
    newmat := ZeroMatrix( F, d1 );
    
    rowcount := 0; // counts the rows of newmat
    for p1 in [1..d], p2 in [p1+1..d] do // 1 <= p1 < p2 <= d
        rowcount +:= 1;
        colcount := 0;  // counts the columns of newmat
        for q1 in [1..d], q2 in [q1+1..d] do // 1 <= q1 < q2 <= d
            colcount +:= 1;
            newmat[rowcount,colcount] := g[p1,q1]*g[p2,q2] 
                    - g[p1,q2]*g[p2,q1];
        end for;
    end for; 
    
    /* In the case of Sp, the exterior square module is not irreducible.
       It always has a 1-dimensional component. When char F does not 
       divide the original dimension, then there is also a component
       of codimension 1. 
       
       For bases of these components, see the comment at #### 
       
       We extract the matrix of the action on the codim 1 or codim 2 component. */;  
    
    if type eq "Sp" then
        codim := case< d mod Characteristic( F ) | 0: 2, default: 1>;
        conj := BasisMatrixForAltSquareSp( d, F );
        newmat := Submatrix( conj*newmat*conj^-1, 1, 1, d1-codim, d1-codim ); 
    end if; 
            
    return newmat;
end function;
    
/* wrapping function for Greenhill's algorithm. In the case of Sp, the procedure is random and nr_tries 
   controls the number of random trials before giving up. */

__funcAltSquareToSLdq := function( Y : type := "SL", Check := true, nr_tries := 10 )
    
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
        return __funcAltSquareToSLdq_func( Y : Check := Check );
    end if; 

    // type is Sp. The method used here is a bit ad-hoc and one needs to see in the future 
    // if there is a better way.
    //
    // TODO: Try to make this more deterministic

    G0 := Sp( dimX, #F );
    X0 := One( G0 );
    Y0 := Y^0;
    nrtries := 0; 
    
    repeat 
        // right multiply Y with Y0. Initually this does nothing.
        YY := Y*Y0;

        // expand YY with either [[1]] or [[1,0],[0,1]] in the bottom right corner.
        if codim eq 1 then 
            newYY := DiagonalJoin( YY, Matrix( F, 1, 1, [1] )); 
        else 
            newYY := DiagonalJoin( YY, Matrix( F, 2, 2, [1, 0, 0, 1 ]));
        end if; 
                         
        // conjugate it into the right form
        conj := BasisMatrixForAltSquareSp( dimX, F );
        YY0 := conj^-1*newYY*conj;

        // try to get its exterior square root using Greenhill.
        try 
            X := __funcAltSquareToSLdq_func( YY0 : chardivdim := codim eq 2, Check := false );
        catch e
            X := false;
        end try;

        // in the codim 2 case, this last operation may fail. If it did not, then check if result is correct
        if codim eq 2 and Category( X ) ne BoolElt then 
            X := X*X0^-1;
            if __funcSLdqToAltSquare( X : type := "Sp" ) ne Y then
                X := false; 
            end if; 
        end if;

        // if the call to Greenhill failed, then choose another X0, Y0
        if codim eq 2 and Category( X ) eq BoolElt then
            X0 := Random( G0 );
            Y0 := __funcSLdqToAltSquare( X0 : type := "Sp" );
        end if; 
        nrtries +:= 1; 
    until codim eq 1 or Category( X ) ne BoolElt or nrtries ge nr_tries; 
    
    return X;  
end function;