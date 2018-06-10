// aux functions for sym square recognition

// solve the equation m = d(d+1)/2
  
SolveSymSquareDimEq := function( m )
    
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
    return Round( Round((2*dim-i)*(i-1)/2)+j-i);
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
    
__funcAltSquareToSLdq := function( g )
    
    dimg := NumberOfRows( g );
    dim := SolveAltSquareDimEq( dimg );
    q := #CoefficientRing( g );
    
    mat := [ [] : i in [1..dim]];
    checkmat := [ [ false : i in [1..dim]] : j in [1..dim]];
    
    for i in [1..dim] do
        for j in [i+1..dim] do
            for k in [j+1..dim] do
                
                pij := funcpos_altsquare( dim, i, j );
                pik := funcpos_altsquare( dim, i, k );
                pjk := funcpos_altsquare( dim, j, k );
                
                m := Matrix( GF( q ), 3, 3, 
                             [g[pij,pij], g[pij,pik], g[pij,pjk],
                              g[pik,pij], g[pik,pik], g[pik,pjk],
                              g[pjk,pij], g[pjk,pik], g[pjk,pjk]]);
               
                det := Determinant( m ); 
                if det eq 0 then
                    continue;
                end if;
                
                d := Sqrt( det )^-1;
                
                poss := [i,j,k];  pos1 := [[1,2],[1,3],[2,3]];
                                                                 
                ex := exists(t){ [u,v] : u, v in {1,2,3} | 
                            checkmat[poss[u],poss[v]] and
                            mat[poss[u],poss[v]] ne 0};
                
                if ex and mat[poss[t[1]],poss[t[2]]] ne 
                   d*(m[pos1[t[1],1],pos1[t[2],1]]*
                      m[pos1[t[1],2],pos1[t[2],2]]-
                      m[pos1[t[1],2],pos1[t[2],1]]*
                      m[pos1[t[1],1],pos1[t[2],2]]) then
                    d := -d;
                    /* assert mat[poss[t[1]],poss[t[2]]] ne 
                   d*(m[pos1[t[1],1],pos1[t[2],1]]*
                      m[pos1[t[1],2],pos1[t[2],2]]-
                      m[pos1[t[1],2],pos1[t[2],1]]*
                      m[pos1[t[1],1],pos1[t[2],2]]); */
                end if;
                                
                if not checkmat[i,i] then
                    mat[i,i] := d*(m[1,1]*m[2,2]-m[1,2]*m[2,1]);
                    checkmat[i,i] := true;
                end if;
                
                if not checkmat[i,j] then
                    mat[i,j] := d*(m[1,1]*m[2,3]-m[1,3]*m[2,1]);
                    checkmat[i,j] := true;
                end if;
                
                if not checkmat[i,k] then
                    mat[i,k] := d*(m[1,2]*m[2,3]-m[1,3]*m[2,2]);
                    checkmat[i,k] := true;
                end if;
                
                if not checkmat[j,i] then
                    mat[j,i] := d*(m[1,1]*m[3,2]-m[1,2]*m[3,1]);
                    checkmat[j,i] := true;
                end if;
                
                if not checkmat[j,j] then
                    mat[j,j] := d*(m[1,1]*m[3,3]-m[1,3]*m[3,1]);
                    checkmat[j,j] := true;
                end if;
                
                if not checkmat[j,k] then
                    mat[j,k] := d*(m[1,2]*m[3,3]-m[1,3]*m[3,2]);
                    checkmat[j,k] := true;
                end if;
                
                if not checkmat[k,i] then
                    mat[k,i] := d*(m[2,1]*m[3,2]-m[2,2]*m[3,1]);
                    checkmat[k,i] := true;
                end if;
                
                if not checkmat[k,j] then
                    mat[k,j] := d*(m[2,1]*m[3,3]-m[2,3]*m[3,1]);
                    checkmat[k,j] := true;
                end if;
                
                if not checkmat[k,k] then
                    mat[k,k] := d*(m[2,2]*m[3,3]-m[2,3]*m[3,2]);
                    checkmat[k,k] := true;
                end if;
                
            end for;
        end for;
    end for;
    
    return Matrix( GF( q ), dim, dim, mat );
              
end function;
