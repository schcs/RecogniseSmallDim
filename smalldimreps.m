// aux functions for small dim recognition

// solve the equation m = d(d+1)/2
  
SolveSymSquareDimEq := function( m : type := "SL" )
    
    if type eq "Omega+" then
        m := m+1;
    end if;
  
    sol := (-1+Sqrt( 1+8*m ))/2;
    
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if;
    
end function;
    
// solve the equation m = d(d-1)/2
  
SolveAltSquareDimEq := function( m )
    
    sol := (1+Sqrt( 1+8*m ))/2;
    
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if;
    
end function;

    
/* position of basis element eij in the standard basis of the 
   sym square module. */
  
funcpos_symsquare := function( dim, i, j )
    return Round( (i-1)*dim-i*(i-3)/2 )+j-i; 
end function;
    
/* position of basis element eij in the standard basis of the 
   alt square module. */
  
funcpos_altsquare := function( dim, i, j )
    
    if i lt j then
        return Round( Round((2*dim-i)*(i-1)/2)+j-i);
    elif j lt i then
        return Round( Round((2*dim-j)*(j-1)/2)+i-j);
    else
        return 0;
    end if;
end function;

// the inverse of the last function

funcposinv_altsquare := function( dim, i )
    
    k := 0;
    
    while k*(dim-(k+1)/2) lt i do
        k := k+1;
        if k gt dim*(dim-1)/2 then
            return false;
        end if;
    end while;
    
    return <k,k+i-(k-1)*(dim-(k)/2)>;
end function;


// the image of a matrix in SL( d, q ) in the sym square module.
  
__funcSLdqToSymSquare := function( g )
    
    d := NumberOfRows( g );
    msets := [ [i,j] : i, j in [1..d] | i le j ];
    
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
    
    return newmat;
end function;
    
/* the preimage of a matrix acting in the sym square module in the natural
   basis in SL( d, q )  */
    
__funcSymSquareToSLdq := function( g )
    
    q := #CoefficientRing( g );
    
    //recover the first row
      
    dimg := NumberOfRows( g );
    dim := SolveSymSquareDimEq( dimg );
    
    listii := [ Round( (i-1)*dim-i*(i-3)/2 ) : i in [1..dim]];
   
    funcel := function( k )
        i := Maximum( [ x  : x in [1..dim] | listii[x] le k ] );
        return i, k-listii[i]+i;
    end function;

    A := [ [] ];
    
    i0 := Position( [ g[1,x] ne 0 : x in listii ], true );
    for i in [1..i0-1] do
        A[1,i] := GF(q)!0;
    end for;
    
    A[1,i0] := Sqrt( g[1,listii[i0]] );
    
    for i in [1..dim-i0] do
        A[1,i0+i] := 1/2*g[1,listii[i0]+i]/A[1,i0];
    end for;
    
    // get the other rows
    // solve a system of linear equations
        
    mat := ZeroMatrix( GF( q ), dimg, dim );
      
    for i in [1..dimg] do
        i0, j0 := funcel( i );
        if i0 eq j0 then
            mat[i,i0] := A[1,i0];
        else
            mat[i,i0] := A[1,j0];
            mat[i,j0] := A[1,i0];
        end if;
    end for;
    
    
    for i in [2..dim] do
        vec := Vector( GF( q ), dimg, [g[i,j] : j in [1..dimg]] );
        try sol := Solution( Transpose( mat ), vec ); 
        catch e return false; end try;
        A[i] := Eltseq( sol );
    end for;
    
    return A;
end function;

__funcSLdqToAltSquare := function( g )
                         
    d := NumberOfRows( g );
    msets := [ [i,j] : i, j in [1..d] | i lt j ];
    
    newmat := [];
    
    for p1 in msets do
        newrow := [];
        for p2 in msets do
            newrow[#newrow+1] := g[p1[1],p2[1]]*g[p1[2],p2[2]] 
                    - g[p1[1],p2[2]]*g[p1[2],p2[1]];
        end for;
        newmat[#newmat+1] := newrow;
    end for;
    
    return Matrix( CoefficientRing( g ), #newmat, #newmat,  newmat );
end function;


/* 
   The following function is an implementation of Greenhill's algorithm
   to recognize if a matrix is the alternating square of another matrix.
   
   The algorithm is described in C Greenhill, "An algorithm for recognising 
   the exterior square of a matrix", Linear and Multilinear Algebra, 1999.
   
   The function assumes that the input is a *non-singular* matrix that is a 
   member of AltSquare( SL( d, q )) in the basis 
   e_12, e_13,...,e_1d,...,e_{d-1}d.
 
   Greenhill's paper describes the algorithm for non-singular matrices, but
   this case is not implemented and such cases may lead to error!
*/


__funcAltSquareToSLdq := function( Y )
    
    // find the dimensions of Y and the original matrix X
      
    dimY := Nrows( Y );
    F := CoefficientRing( Y );
    dimX := SolveAltSquareDimEq( dimY );
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
                    return GL( dimX, F )!X;
                end if;
            end if;
        end if;
    end for;
    
end function;
