
SolveAltSquareDimEq := function( m )
    
    sol := (1+Sqrt( 1+8*m ))/2;
    
    if sol ne Round( sol ) then
        return 0;
    else
        return Round( sol );
    end if;
    
end function;
    
    
funcpos_altsquare := function( dim, i, j )
    
    if i lt j then
        return Round( Round((2*dim-i)*(i-1)/2)+j-i);
    elif j lt i then
        return Round( Round((2*dim-j)*(j-1)/2)+i-j);
    else
        return 0;
    end if;
end function;
    
    
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
        
    
ExteriorSquareRoot := function( Y )
    
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
    
    
                    
                          
                          
                              
                              
            
        
    
        
                 
                
              
                    
    
      
    
      
    
