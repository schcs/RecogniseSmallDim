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


import "smalldimreps.m":SolveAltSquareDimEq, funcpos_altsquare, 
                        funcposinv_altsquare;
                   
__funcAltSquareToSLdq_findpivot := function( Y )
    
    // find the dimensions of Y and the original matrix X
            
    dimY := Nrows( Y );
    F := CoefficientRing( Y );
    dimX := SolveAltSquareDimEq( dimY );
    codim := case< dimX mod Characteristic( F ) | 0: 2, default: 1 >;
    
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
                        return false, 1;
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
                        return false, 2;
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
                    return p, q, l, mu, x, y, w;
                end if;
            end if;
        end if;
    end for;
end function;
    
__funcAltSquareToSLdq_func := function( Y : chardivdim := false )
     
    // get the dimensions and the coeff ring
    
    n := NumberOfRows( Y );
    m := SolveAltSquareDimEq( n );
    F := CoefficientRing( Y );

    /* the algorithm needs a pivot in X and in Y; that is, non-zero
       elements in these matrices. The pivot of Y is Y_(p,q,mu,l) and 
       the pivot in X is X[p,l]. */
      
    p, q, l, mu, x, y, w := __funcAltSquareToSLdq_findpivot( Y );

    // start setting up the output matrix Z
    Z := ZeroMatrix( F, m );
    Z[p,l] := w^-1;
    Z[q,l] := w^-1*x;
    Z[p,mu] := w^-1*y;
    
    // the result matrix R shows which elements have been computed already
      
    R := [[ false : x in [1..m]] : x in [1..m]];
    R[p,l] := true; R[q,l] := true; R[p,mu] := true;
    
    // function delta to compare s and mu        
    delta := function( s, mu )
        return case< s lt mu | true: 1, default: -1 >;
    end function;
        
    /* the following returns the entry in the (a,b)-(c,d) position in 
       of Y with sign corrected */       
    Y_ := function( a, b, c, d )
        v := Y[funcpos_altsquare( m, a, b ),
               funcpos_altsquare( m, c, d )];
        
        return delta( a, b )*delta( c, d )*v;
    end function;
        
    /* equation (13) of Greenhill's paper. 
       Suppose that the mu- and l-entries of the p-th row are known. 
       Then the s-entry of the same row can be determined provided 
       Y_(p,q,mu,l) is non-zero. 
         
       Input: row p, known entries l, p, unknown entry s, aux variable q */ 
          
    Eq13 := function( Z, p, q, mu, l, s )
        
        return Y_(p,q,mu,l)^-1*(-Y_(p,q,l,s)*Z[p,mu]+Y_(p,q,mu,s)*Z[p,l] );
    end function;
        
    /* equation (12) of Greenhill's paper. 
       Suppose that the p- and q-entries of the l-th column are known. 
       Then the j-entry of the same column can be determined provided 
       Y_(p,q,mu,l) is non-zero. 
         
       Input: col l, known entries p, q, unknown entry j, aux variable mu */ 
        
    Eq12 := function( Z, p, q, mu, l, j )
        
        return Y_(p,q,mu,l)^-1*(Y_(p,j,mu,l)*Z[q,l]-Y_(q,j,mu,l)*Z[p,l] );
    end function;
        
    /* Equation (11) of Greenhill's paper.  Suppose that the three entries    
       in positions (p,l), (p,s), (j,l) are known. These positions form a 
       triangle in the matrix X. The antipode position is (j,s) and this
       entry can also be determined provided X[p,l] is not zero */
        
    Eq11 := function( Z, p, l, j, s )    
        
        return Z[p,l]^-1*(Y_(p,j,l,s)+Z[p,s]*Z[j,l]);
    end function;
                
    /* we want to aviod using some rows and columns of Y that may contain
       incorrect entries. We list the forbidden rows and columns in forb */
    
    forb := case< chardivdim | true: {{i,m+1-i} : i in [1..m div 2]}, default: {}>;  

    /* condrow is the condition for the triple l, s, q, mu to be used in the  
       algorithm that determines the entries in row p */
      
    condrow := function( R, Y, s, l, mu, q )
        
        //print p, s, R[p,s];
        
        return R[p,l] and R[p,mu] and not R[p,s] and 
               p ne q and 
               mu ne l and 
               l ne s and
               p ne q and 
               mu ne s and 
               Y_(p,q,mu,l) ne 0 and
               not {p,q} in forb and
               not {mu,l} in forb and
               not {l,s} in forb and 
               not {mu,s} in forb;
    end function;
        
    // we fill in the p-th row 
        
    for s in [1..m] do
        if s eq l or s eq mu then continue; end if;
        v := exists(u){ <l1,mu1,q1> : l1, mu1, q1 in [1..m] | 
                     condrow( R, Y, s, l1, mu1, q1 )};
        if not v then continue; end if;
        l1 := u[1]; mu1 := u[2]; q1 := u[3];
        Z[p,s] := Eq13( Z, p, q1, mu1, l1, s );
        R[p,s] := true;
    end for;
    
    condcol := function( R, Y, j, p, mu, q )
        
        //print p, s, R[p,s];
        
        return R[q,l] and R[p,l] and not R[j,l] and 
               p ne q and 
               mu ne l and 
               p ne j and
               q ne j and
               Y_(p,q,mu,l) ne 0 and
               not {p,q} in forb and
               not {mu,l} in forb and
               not {p,j} in forb and 
               not {q,j} in forb;
    end function;
            
    // we fill in the l-th column
          
    for j in [1..m] do
        if j eq p or j eq q then continue; end if;
        v := exists(u){ <p1,mu1,q1> : p1, mu1, q1 in [1..m] | 
                     condcol( R, Y, j, p1, mu1, q1 )};
        if not v then continue; end if;
        p1 := u[1]; mu1 := u[2]; q1 := u[3];
        Z[j,l] := Eq12( Z, p1, q1, mu1, l, j );
        R[j,l] := true;
    end for;
    
    condgen := function( R, Z, p, l, j, s )
        
        return R[p,l] and R[p,s] and R[j,l] and
               p ne j and 
               l ne s and 
               Z[p,l] ne 0 and
               not {p,j} in forb and
               not {l,s} in forb;
    end function;
    
    // we fill in the rest
      
    for j in [1..m] do
        for s in [1..m] do
            if j eq p or s eq l then continue; end if;
            v := exists(u){ <p1,l1> : p1, l1 in [1..m] | 
                         condgen( R, Z, p1, l1, j, s )};
            if not v then continue; end if;
            p1 := u[1]; l1 := u[2];  
            Z[j,s] := Eq11( Z, p1, l1, j, s );
            R[j,s] := true;
        end for;
    end for;
                          
    return Z, R;
end function;