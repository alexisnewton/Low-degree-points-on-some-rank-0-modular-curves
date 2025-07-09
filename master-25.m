
//////////////////////////////////////////////////////////////////////////////////////////
//  This is a complete determination of the quartic points on X1(26)
//////////////////////////////////////////////////////////////////////////////////////////
 
/****************************************************************************** 
 Here is a summary of the argument.
 
 X_1(25) has genus 12, and rank 0.
 The torsion subgroup is [ 227555 ].
 
 There are 10 rational cusps and 0 quadratic or cubic cusps, 2 quartic cusps and 1 degree 10.

 Working mod 3, we note that
 there are 10 F_3 points, 0 F_9 points, and 0 F_27 points, 12 F_81 points. 

 We compute that the images of the 12 F_81 points under Abel--Jacobi
 do not meet the reduction of the global torsion. 

 
******************************************************************************/

  N := 25; 

  
  //////////////////////////////////////////////////////////////////////////////////////////
  // Input the homebrewed functions 
  //////////////////////////////////////////////////////////////////////////////////////////
  
  load "functions.m";

  
  //////////////////////////////////////////////////////////////////////////////////////////
  // Equations for X1(25), from Sutherland
  //////////////////////////////////////////////////////////////////////////////////////////
  

F := Rationals();   
A2<u,v> := AffineSpace(F,2);
X := Curve(A2,u*v^5 + (u^4 - 2*u^3 - u^2 + 2*u + 1)*v^4 - (2*u^6 - 2*u^4 + 4*u^3 + 2*u^2 - 2)*v^3 + (u^8 + u^7 - 2*u^6 + u^5 - u^4 - u^3 - 2*u^2 - u + 1)*v^2 + (u^8 + u^7 + 2*u^6 + u^5 - 2*u^4 + u^3 - u^2)*v + u^6);

  //////////////////////////////////////////////////////////////////////
  // Get the canonical model.
  //////////////////////////////////////////////////////////////////////
  
    phi := CanonicalMap(ProjectiveClosure(X));
    Xsm := CanonicalImage(Domain(phi),phi); 
     P<[T]> := AmbientSpace(Xsm);

  
  //////////////////////////////////////////////////////////////////////
  // Compute the local torsion bound
  //////////////////////////////////////////////////////////////////////   

//  for p in [q : q in PrimesUpTo(40) | not q in PrimeDivisors(2*N) ] do
  torsData := {@@};
  for p in [3,7,11 ] do     
      invs := Invariants(ClassGroup(Curve(Reduction(Xsm,p))));
      torsData := torsData join {@invs@};
      <p,invs>;
  end for;

  /*
<3, [ 2503105, 0 ]>
<7, [ 2, 2, 710, 5006210, 0 ]>
<11, [ 5, 5, 5, 5, 3205, 2503105, 0 ]>                                     
    
  */       
  
    "The rational torsion subgroup is a subgroup of", torsBound(torsData);  // 

    //The rational torsion subgroup is a subgroup of [ 2503105 ]

  //HOWEVER, sage code of M. Derickx gives a better bound:
//sage: N=25                                                                      
//sage: rational_cuspidal_classgroup(Gamma1(N)).invariants()                      
//(227555,)

function rationalPoints(D : Bound := 1)
    return {@D![t :t in tup]
              : tup in CartesianPower([-Bound..Bound], Dimension(AmbientSpace(D))+1)
              | not {i : i in tup} eq {0}
                and {Evaluate(eqns,[t : t in tup]) : eqns in DefiningEquations(D)} eq {0}
            @};
end function;


 rationalPoints(Xsm: Bound:=2); 

pts:=[ [2 , 1 , 0 , 1 , 1 , 0 , 0 , 0 , 1 , 0 , 0 , 0], 
    [1 , 0 , 0 , 0 , 0 , 0 , 0 ,0 , 0 , 0 , 0 , 0], 
    [0 , 1 , 0 , 0 , 1 , 0 , 0 , 0 , 1 , 0 , 0 , 0], 
    [0 , -1 , 2, -1 , -1 , 0 , -1 , 1 , -1 , 1 , 0 , 1], 
    [0 , 0 , 1 , 0 , 0 , 0 , 0 , 0 , 0 , 0, 0 , 0]];


basePt := [0 , 0 , 1 , 0 , 0 , 0 , 0 , 0 , 0 , 0, 0 , 0]; 



// Verify that these generate the torsion  
  p := 3;
  Cp<[T]> := Curve(Reduction(Xsm,p));
    pic,mPic := ClassGroup(Cp);    
  basePt := &+Places(Cp![0 , 0 , 1 , 0 , 0 , 0 , 0 , 0 , 0 , 0, 0 , 0]);
  divs := {@
         &+Places(Cp!pt) - Degree(&+Places(Cp!pt))*basePt
         : pt in pts @} ;  
  
  global, mGlobal := 
     sub<pic | [(Inverse(mPic))(divs[i]) : i in [1..#divs]]>;  
  Invariants(global); // [ 227555 ]
  

  "There are", [#Places(Cp,i) : i in [1..4]], "places of degree 1, 2, 3, and 4 over F_3";   
   
//There are [ 10, 0, 0, 12 ] places of degree 1, 2, 3, and 4 over F_3
   // the 10 degree 1 points lift to Q so we compute with the 12 quartic points


    
  validQuarticImages := {@@};
  for pl in Places(Cp,4) do
      D := Divisor(pl) - Degree(pl)*basePt;
      if Inverse(mPic)(D) in global then
        validQuarticImages := 
        validQuarticImages join {@Inverse(mPic)(D)@};
      end if;
  end for;
  "The rational places all lift to Q, and",  #validQuarticImages, "of the other places (coming from a quartic point) are in the image of Abel--Jacobi"; 
//2
//and there are 2 valid quartic cusps (which matches what we expect) 


