###
##  This code for GAP ( version ⩾ 4.15.1 of 2025-10-18 ) accompanies the papers
## "Simple groups with narrow prime spectrum: Extended list" and 
## "Finite simple groups with narrow prime spectrum"
##  by Andrei V. Zavarnitsine
##
##  Date: April 23, 2026


## Given a set of primes pi, the function <SimpleGroupsPi> defined below in Section 2
## returns ( the codes of ) all non-abelian simple groups  G  with  π(G) ⊆ pi.
##
## Example of usage:
##
## gap> List( SimpleGroupsPi( [ 2, 3, 5 ] ), NameByCode );
## [ "A5", "A6", "S4(3)" ]
## 
## More examples can be found below in Section 4.
  
  
## The "code" of a non-abelian FSG is a quadruple [ t, n, p, k ], where 
## 
## t = 1..18  encodes the following 18 families of FSGs
## 
##   t    Family      Parameters
## -----------------------------------
##   1    Sporadic    n = 1..26, p = *, k = *   ( * = any number, usually 0. Value ignored )
##   2    Alt n       p = *, k = *
##   3    L n (q)     q = p^k
##   4    S 2n (q)    q = p^k
##   5    O 2n+1 (q)  q = p^k
##   6    O+ 2n (q)   q = p^k
##   7    U n (q)     q = p^k
##   8    O- 2n (q)   q = p^k
##   9    G2 (q)      q = p^k, n = *
##  10    F4 (q)      q = p^k, n = *
##  11    E6 (q)      q = p^k, n = *
##  12    E7 (q)      q = p^k, n = *
##  13    E8 (q)      q = p^k, n = *
##  14    3D4 (q)     q = p^k, n = *
##  15    2E6 (q)     q = p^k, n = *
##  16    Sz (q)      q = 2^k, n = *, p = * 
##  17    2G2 (q)     q = 3^k, n = *, p = * 
##  18    2F4 (q)     q = 2^k, n = *, p = * 

#################################################
##
##   Section 1. Preliminary lists and functions 
  
FamilyNames :=                              ##  name strings for the 18 families
  ["Sporadic", "Alt",  "L",    "S",  "O", 
   "O+",  "U",  "O-",  "G2",  "F4",
   "E6", "E7",  "E8", "3D4", "2E6",
                "Sz", "2G2", "2F4"];

SporadicNames:=                              ##  name strings of sporadic groups as used in GAP
[ "M11",  "M12",  "J1", "M22",  "J2", 
  "M23",   "HS",  "J3", "M24", "McL", 
   "He",   "Ru", "Suz",  "ON", "Co3", 
  "Co2", "Fi22",  "HN",  "Ly",  "Th", 
 "Fi23",  "Co1",  "J4", "F3+",   "B", "M" ];;


IsAdmissibleCode := function(y)              ## checks if y = [ t, n, p, k ] is an admissible code for a FSG
local t,n,p,k;
  t:=y[1]; n:=y[2]; p:=y[3]; k:=y[4];
return
  ( t =  1 and n in [1..26] ) or                                ## Sporadic
  ( t =  2 and n>=5)    or                                      ## Alternating
  ( t =  3 and ( (n>=5) or                                      ## Ln(q)         ( L2(4) and L2(5) are encoded as A5 )
                 (n in [3,4] and p^k>2) or                      ##               ( L2(9) is encoded as A6 )
                 (n=2 and p^k>5 and p^k<>9) ) ) or              ##               ( L3(2) is encoded as L2(7) )  
  ( t =  4 and ( (n>=3) or (n=2 and p^k>2) ) ) or               ## S2n(q)        ( S2(q) is encoded as L2(q) )
  ( t =  5 and ( (n>=3) and (p<>2) ) ) or                       ## O{2n+1}(q) 
  ( t =  6 and n>=4 )   or                                      ## O{2n}^+(q)
  ( t =  7 and ( (n>=5) or (n in [3,4] and p^k>2) ) ) or        ## Un(q)        ( U4(2) is encoded as S4(3) )  
  ( t =  8 and n>=4  )  or                                      ## O{2n}-(q)
  ( t =  9 and p^k>2 )  or                                      ## G2(q)
  ( t = 10 and true  )  or                                      ## F4(q)
  ( t = 11 and true  )  or                                      ## E6(q)
  ( t = 12 and true  )  or                                      ## E7(q)
  ( t = 13 and true  )  or                                      ## E8(q)
  ( t = 14 and true  )  or                                      ## 3D4(q)
  ( t = 15 and true  )  or                                      ## 2E6(q)
  ( t = 16 and k mod 2 = 1 and k>1 ) or                         ## Sz(q)
  ( t = 17 and k mod 2 = 1 and k>1 ) or                         ## 2G2(q)
  ( t = 18 and k mod 2 = 1 );                                   ## 2F4(q)       ( k = 1 encodes the Tits group 2F4(2)' )
end;

####################################################################

IsPiNumber := function(pi,n)         ## checks if all prime divisors of n are in pi
local p;
  for p in pi do
    while n mod p = 0 
      do n:=n/p; 
      od;
  od;
return n=1;
end;

OrderModTwisted := function(t,m)      ## analogue of OrderMod for unitary groups 
local l;
  l:=OrderMod(t,m);
  if l mod 2=1 then l:=l*2; 
   elif l mod 4=2 then l:=l/2;
  fi;
return l;
end;

########################### Alt_n ###############################

PiContainsAltn := function(n,pi)        ## checks if pi( Alt_n ) is in pi
local t,i;
  t:=true;
  i:=3;
  while t and i<=n 
    do t := IsPiNumber(pi,i); i:=i+1; 
    od;
return t;
end;

######################## Ln(q) #############################

PiContainsLn := function(p,k,n,pi)        ## checks if pi( Ln(p^k) ) is in pi
local i,t;
  t:=p in pi;
  i:=2;
  while t and i<=n 
    do t := IsPiNumber(pi,p^(k*i)-1); i:=i+1; 
    od;
return t;
end;

######################## S{2n}(q) #############################

PiContainsS2n := function(p,k,n,pi)        ## checks if pi( S{2n}(p^k) ) is in pi
local t,i;
  t:=p in pi;
  i:=2;
  while t and i<=2*n 
    do t:= IsPiNumber(pi,p^(k*i)-1); i:=i+2; 
    od;
return t;
end;


####################### O{2n+1}(q) #############################

PiContainsO2n1 := function(p,k,n,pi)        ## checks if pi( O{2n+1}(p^k) )  is in pi
local t,i;
  t:=p in pi;
  i:=2;
  while t and i<=2*n 
    do t:= IsPiNumber(pi,p^(k*i)-1); i:=i+2; 
    od;
return t;
end;

####################### O{2n}^+(q) #############################

PiContainsO2nPlus := function(p,k,n,pi)        ## checks if pi( O{2n}^+(p^k) ) is in pi
local t,i;
  t:=p in pi;
  i:=2;
  while t and i<=2*n-2 
    do t:=IsPiNumber(pi,p^(k*i)-1); i:=i+2; 
    od;
  t:=t and IsPiNumber(pi,p^(k*n)-1);
return t;
end;

####################### Un(q) #############################

PiContainsUn := function(p,k,n,pi)             ## checks if pi( Un(p^k) ) is in pi
local t,i;
  t:=p in pi;
  i:=2;
  while t and i<=n 
    do t:=IsPiNumber(pi,p^(k*i)-(-1)^i); i:=i+1; 
    od;
return t;
end;

##################### O{2n}-(q) #############################

PiContainsO2nMinus := function(p,k,n,pi)        ## checks if pi( O{2n}-(p^k) ) is in pi
local t,i;
  t:=p in pi;
  i:=2;
  while t and i<=2*n-2 
    do t:=IsPiNumber(pi,p^(k*i)-1); i:=i+2; 
    od;
  t:= t and IsPiNumber(pi,p^(k*n)+1);
return t;
end;

######################## G2(q) ##############################

PiContainsG2 := function(p,k,pi)                ## checks if pi( G2(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(6*k)-1);
return t;
end;

####################### F4(q) #############################

PiContainsF4 := function(p,k,pi)                ## checks if pi( F4(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(12*k)-1);
  t:=t and IsPiNumber(pi,p^(4*k)+1);
return t;
end;

####################### E6(q) #############################

PiContainsE6 := function(p,k,pi)                ## checks if pi( E6(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(12*k)-1);
  t:=t and IsPiNumber(pi,p^(9*k)-1);
  t:=t and IsPiNumber(pi,p^(4*k)+1);
  t:=t and IsPiNumber(pi,p^(5*k)-1);
return t;
end;

##################### E7(q) #############################

PiContainsE7 := function(p,k,pi)                 ## checks if pi( E7(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(18*k)-1);
  t:=t and IsPiNumber(pi,p^(14*k)-1);
  t:=t and IsPiNumber(pi,p^(6*k)+1);
  t:=t and IsPiNumber(pi,p^(10*k)-1);
  t:=t and IsPiNumber(pi,p^(4*k)+1);
return t;
end;

##################### E8(q) #############################

PiContainsE8 := function(p,k,pi)                  ## checks if pi( E8(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(30*k)-1);
  t:=t and IsPiNumber(pi,p^(24*k)-1);
  t:=t and IsPiNumber(pi,p^(10*k)+1);
  t:=t and IsPiNumber(pi,p^(18*k)-1);
  t:=t and IsPiNumber(pi,p^(14*k)-1);
return t;
end;

####################### 3D4(q) #############################

PiContains3D4 := function(p,k,pi)                  ## checks if pi( 3D4(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(8*k)+p^(4*k)+1);
  t:=t and IsPiNumber(pi,p^(6*k)-1);
return t;
end;

####################### 2E6(q) #############################

PiContains2E6 := function(p,k,pi)                   ## checks if pi( 2E6(p^k) ) is in pi
local t;
  t:=p in pi;
  t:=t and IsPiNumber(pi,p^(12*k)-1);
  t:=t and IsPiNumber(pi,p^(9*k)+1);
  t:=t and IsPiNumber(pi,p^(4*k)+1);
  t:=t and IsPiNumber(pi,p^(5*k)+1);
return t;
end;

####################### Sz(q) #############################

PiContainsSz := function(k,pi)                       ## checks if pi( Sz(2^k) ) is in pi
local t;
  t:=2 in pi;
  t:=t and IsPiNumber(pi,2^(2*k)+1);
  t:=t and IsPiNumber(pi,2^k-1);
return t;
end;

####################### 2G2(q) #############################

PiContains2G2 := function(k,pi)                       ## checks if pi( 2G2(3^k) ) is in pi
local t;
  t:=3 in pi;
  t:=t and IsPiNumber(pi,3^(3*k)+1);
  t:=t and IsPiNumber(pi,3^k-1);
return t;
end;

####################### 2F4(q) #############################

PiContains2F4 := function(k,pi)                       ## checks if pi( 2F4(2^k) ) is in pi
local t;
  t:=2 in pi;
  t:=t and IsPiNumber(pi,2^(6*k)+1);
  t:=t and IsPiNumber(pi,4^k-1);
  t:=t and IsPiNumber(pi,2^(3*k)+1);
return t;
end;

InfoPiSimple := NewInfoClass("InfoPiSimple");;        ## InfoClass

## Use SetInfoLevel(InfoPiSimple,1); 
## if the calculations are slow  
## ( i.e. when either the size of <pi> or the largest prime in <pi> is large ).
##
## Use SetInfoLevel(InfoPiSimple,2); 
## for an even more verbose output


#############################
##
##   Section 2. Main function 

## Given a set of primes pi, the function <SimpleGroupsPi> returns  
## the codes of  all non-abelian  simple groups G  with pi(G) ⊆ pi

SimpleGroupsPi := function(pi)  
local result, smallestNonPiPrime, cont, code, p, pi0, n0, l, k, t;
  if not ForAll(pi,IsPrime) then Error("Argument must be a set of primes "); 
  fi;
  result:=[];
  ########################### Alt_n ###############################
  smallestNonPiPrime:=1; cont:=true;
  while cont do
    smallestNonPiPrime := NextPrimeInt(smallestNonPiPrime);
    cont := smallestNonPiPrime in pi;
  od;  
  for l in [5..smallestNonPiPrime-1] do 
    Add(result,[2,l,0,0]);
  od;
  if Size(pi)>2 then 
    for p in pi do
      Info(InfoPiSimple,1,"p = ",p);
      pi0:=Difference(pi,[p]);
      n0:=Maximum(List(pi0,t->OrderMod(p,t)));
      if n0<6 and p=2 then n0:=6; fi;           ## checking if (p,n0+1)=(2,<=6)
      if n0=1 and Size(PrimePowersInt(p+1))=2   ## checking if (p,n0+1)=(2^t-1,2)
      then n0:=2; fi;
      ##################### Ln(q) #############################
      Info( InfoPiSimple, 1, "  Case Ln(q)" );
      for l in [2..n0] do               ## l=n*k
      Info( InfoPiSimple, 2, "     l = ",l,"  n0 = ",n0,"  p = ",p);
       for k in DivisorsInt(l) do
         code:=[3,l/k,p,k];
         if IsAdmissibleCode(code) and PiContainsLn(p,k,l/k,pi) then Add(result,code);
         fi;
       od;
      od;
      ##################### S{2n}(q) #############################
      Info(InfoPiSimple,1,"  Case S2n(q)");
      for l in [4,6..(n0-(n0 mod 2))] do ## l=2*n*k
       for k in DivisorsInt(l/2) do
         code:=[4,l/2/k,p,k];
         if IsAdmissibleCode(code) and PiContainsS2n(p,k,l/2/k,pi) then Add(result,code);
         fi;
       od;
      od;
      ##################### O{2n+1}(q) #############################
      Info(InfoPiSimple,1,"  Case O{2n+1}(q)");
      for l in [6,8..(n0-(n0 mod 2))] do ## l=2*n*k
       for k in DivisorsInt(l/2) do
        code:=[5,l/2/k,p,k];
        if IsAdmissibleCode(code) and PiContainsO2n1(p,k,l/2/k,pi) then Add(result,code);
        fi;
       od;
      od;
      ##################### O{2n}^+(q) #############################
      Info(InfoPiSimple,1,"  Case O{2n}+(q)");
      for l in [6,8..(n0-(n0 mod 2))] do ## l=(2*n-2)*k
       for k in DivisorsInt(l/2) do
        code:=[6,l/2/k+1,p,k];
        if IsAdmissibleCode(code) and PiContainsO2nPlus(p,k,l/2/k+1,pi) then Add(result,code);
        fi;
       od;
      od;  
      ##################### O{2n}-(q) #############################
      Info(InfoPiSimple,1,"  Case O{2n}-(q)");
      for l in [6,8..(n0-(n0 mod 2))] do ## l=(2*n-2)*k
       for k in DivisorsInt(l/2) do
        code:=[8,l/2/k+1,p,k];
        if IsAdmissibleCode(code) and PiContainsO2nMinus(p,k,l/2/k+1,pi) then Add(result,code);
        fi;
       od;
      od;
      ##################### G2(q) ############################# 
      Info(InfoPiSimple,1,"  Case G2(q)"); 
      for l in [6,12..(n0-(n0 mod 6))] do ## l=6*k
        code:=[9,0,p,l/6];
        if IsAdmissibleCode(code)and PiContainsG2(p,l/6,pi) then Add(result,code);
        fi;
      od;
      ##################### F4(q) #############################  
      Info(InfoPiSimple,1,"  Case F4(q)"); 
      for l in [12,24..(n0-(n0 mod 12))] do ## l=12*k
        code:=[10,0,p,l/12];
        if IsAdmissibleCode(code) and PiContainsF4(p,l/12,pi) then Add(result,code);
        fi;
      od;
      ##################### E6(q) #############################  
      Info(InfoPiSimple,1,"  Case E6(q)"); 
      for l in [12,24..(n0-(n0 mod 12))] do ## l=12*k
        code:=[11,0,p,l/12];
        if IsAdmissibleCode(code) and PiContainsE6(p,l/12,pi) then Add(result,code);
        fi;
      od;
      ##################### E7(q) #############################  
      Info(InfoPiSimple,1,"  Case E7(q)"); 
      for l in [18,36..(n0-(n0 mod 18))] do ## l=18*k
        code:=[12,0,p,l/18];
        if IsAdmissibleCode(code) and PiContainsE7(p,l/18,pi) then Add(result,code);
        fi;
      od;
      ##################### E8(q) ############################# 
      Info(InfoPiSimple,1,"  Case E8(q)");  
      for l in [30,60..(n0-(n0 mod 30))] do ## l=30*k
        code:=[13,0,p,l/30];
        if IsAdmissibleCode(code) and PiContainsE8(p,l/30,pi) then Add(result,code);
        fi;
      od;
      ##################### 3D4(q) #############################  
      Info(InfoPiSimple,1,"  Case 3D4(q)"); 
      for l in [12,24..(n0-(n0 mod 12))] do ## l=12*k
        code:=[14,0,p,l/12];
        if IsAdmissibleCode(code) and PiContains3D4(p,l/12,pi) then Add(result,code);
        fi;
      od;
      ##################### 2E6(q) #############################  
      Info(InfoPiSimple,1,"  Case 2E6(q)"); 
      for l in [18,36..(n0-(n0 mod 18))] do ## l=18*k
        code:=[15,0,p,l/18];
        if IsAdmissibleCode(code) and PiContains2E6(p,l/18,pi) then Add(result,code);
        fi;
      od;
      ##################### Un(q) #############################
      Info(InfoPiSimple,1,"  Case Un(q)"); 
        n0:=Maximum(List(pi0,t->OrderModTwisted(p,t)));
      if n0<3 and p=2 then n0:=3; fi;           ## checking if (p,n0+1)=(2,<=3)
      if n0=1 and Size(PrimePowersInt(p-1))=2   ## checking if (p,n0+1)=(2^t+1,2) 
      then n0:=2; fi;
      for l in [2..n0] do     ## l=n*k
        Info(InfoPiSimple,2,"     l = ",l,"  n0 = ",n0,"  p = ",p);
        for k in DivisorsInt(l) do
          code:=[7,l/k,p,k];
          if IsAdmissibleCode(code) and PiContainsUn(p,k,l/k,pi) then Add(result,code);
          fi;
        od;
      od;  
    od; 
   
    if 2 in pi then 
      n0:=Maximum(List(Difference(pi,[2]),t->OrderMod(2,t) ));
      if n0<6 then n0:=6;      ## checking if (2,n0+1)=(2,<=6) 
      fi;           
      ##################### Sz(q) #############################
      Info(InfoPiSimple,1,"  Case Sz(q)"); 
      for l in [4,8..(n0-(n0 mod 4))] do ## l=4*k
        code:=[16,0,0,l/4];
        if IsAdmissibleCode(code) and PiContainsSz(l/4,pi) then Add(result,code);
        fi;
      od;
      ##################### 2F4(q) ###########################
      Info(InfoPiSimple,1,"  Case 2F4(q)"); 
      for l in [12,24..(n0-(n0 mod 12))] do ## l=12*k
        code:=[18,0,0,l/12];
        if IsAdmissibleCode(code) and PiContains2F4(l/12,pi) then Add(result,code);
        fi;
      od; 
    fi;
    ##################### 2G2(q) #############################
    if 3 in pi then 
     Info(InfoPiSimple,1,"  Case 2G2(q)"); 
      n0:=Maximum(List(Difference(pi,[3]),t->OrderMod(3,t) ));    
      if n0=1 then n0:=2;  ## checking if (p,n0+1)=(2^t-1,2)
      fi;   
      for l in [6,12..(n0-(n0 mod 6))] do ## l=6*k
        code:=[17,0,0,l/6];
        if IsAdmissibleCode(code) and PiContains2G2(l/6,pi) then Add(result,code);
        fi;
      od;
    fi;
    ##################### Sporadic #############################
    Info(InfoPiSimple,1,"  Case Sporadic"); 
     for l in [1..26] do 
      if IsPiNumber(pi, Size(CharacterTable(SporadicNames[l]))) then 
      Add(result,[1,l,0,0]);   fi;
     od;
   
  fi;
return result;
end;


###########################
##
##   Section 3. Auxiliaries 

OrderByCode := function(t) ## returns the order of a FSG with code t
local y,n,p,k,q;
  y:=t[1]; n:=t[2]; p:=t[3]; k:=t[4]; q:=p^k;
  if not IsAdmissibleCode(t) then Print("Sorry, ", t," is not an admissible code for a FSG ...\n"); return fail;
    elif y=1  then return Size(CharacterTable(SporadicNames[t[2]]));
    elif y=2  then return Factorial(n)/2;                                                    ## Alt_n
    elif y=3  then return q^(n*(n-1)/2)*Product([2..n], i->(q^i-1))/Gcd(n,q-1);              ## Ln(p^k)
    elif y=4  then return q^(n^2)*Product([1..n], i->(q^(2*i)-1))/Gcd(2,q-1);                ## S{2n}(p^k)
    elif y=5  then return q^(n^2)*Product([1..n], i->(q^(2*i)-1))/Gcd(2,q-1);                ## O{2n+1}(p^k)
    elif y=6  then return q^(n*(n-1))*(q^n-1)*Product([1..n-1],i->(q^(2*i)-1))/Gcd(4,q^n-1); ## O{2n}^+(p^k)
    elif y=7  then return q^(n*(n-1)/2)*Product([2..n],i->(q^i-(-1)^i))/Gcd(n,q+1);          ## Un(p^k)
    elif y=8  then return q^(n*(n-1))*(q^n+1)*Product([1..n-1],i->(q^(2*i)-1))/Gcd(4,q^n+1); ## O{2n}^-(p^k)
    elif y=9  then return q^6*Product([6,2],i->(q^i-1));                                     ## G2(p^k)
    elif y=10 then return q^24*Product([12,8,6,2],i->(q^i-1));                               ## F4(p^k)
    elif y=11 then return q^36*Product([12,9,8,6,5,2],i->(q^i-1))/Gcd(3,q-1);                ## E6(p^k)
    elif y=12 then return q^63*Product([18,14,12,10,8,6,2],i->(q^i-1))/Gcd(2,q-1);           ## E7(p^k)
    elif y=13 then return q^120*Product([30,24,20,18,14,12,8,2],i->(q^i-1));                 ## E8(p^k)
    elif y=14 then return q^12*Product([6,2],i->(q^i-1))*(q^8+q^4+1);                        ## 3D4(p^k)
    elif y=15 then return q^36*Product([12,9,8,6,5,2],i->(q^i-(-1)^i))/Gcd(3,q+1);           ## 2E6(p^k)
    elif y=16 then q:=2^k; return q^2*(q^2+1)*(q-1);                                         ## Sz(2^k)
    elif y=17 then q:=3^k; return q^3*(q^3+1)*(q-1);                                         ## 2G2(3^k)
    elif y=18 then q:=2^k; if k>1 then return q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1);            ## 2F4(2^k), k>1
                                  else return q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1)/2;          ## 2F4(2)'   
                           fi;
    else return fail;
  fi;
end;

PiByCode := function(t) ## returns the prime spectrum of a FSG with code t
  return List( Collected( Factors( OrderByCode( t ) ) ) , d -> d[1] );
end;

NameByCode:=function(t) ## returns a human-readable form of a group with code t
local s,q,qstr,mq;
mq:=100; ## powers q=p^k > mq are not evaluated
if t[3]^t[4]>mq and t[4]>1  then qstr:=Concatenation(String(t[3]),"^",String(t[4]));
                            else qstr:=String(t[3]^t[4]);
fi;
if not IsAdmissibleCode(t) then Error("Code ",t," is not admissible for a FSG ..."); 
fi;
if t[1]=1 then return SporadicNames[t[2]];
  elif t[1]=2 then return Concatenation("A",String(t[2]));
  elif t[1] in [16,18] then 
    if 2^t[4]>mq then qstr:=Concatenation("2^",String(t[4]));
                 else qstr:=String(2^t[4]);
    fi; 
    s:=Concatenation(FamilyNames[t[1]],"(",qstr,")");                                          ## Sz, 2F4
    if t[1]=18 and t[4]=1 then s:=Concatenation(s,"'"); fi;  
    return s;
  elif t[1]=17 then  
    if 3^t[4]>mq then qstr:=Concatenation("3^",String(t[4]));
                 else qstr:=String(3^t[4]);
    fi; 
    return Concatenation(FamilyNames[t[1]],"(",qstr,")");                                      ## 2G2
  elif t[1] in [9..15] then return Concatenation(FamilyNames[t[1]],"(",qstr,")");              ## G2, F4, E6, E7, E8, 3D4, 2E6
  elif t[1]=4          then return Concatenation("S",String(2*t[2]),"(",qstr,")");             ## S
  elif t[1]=6          then return Concatenation("O",String(2*t[2]),"+(",qstr,")");            ## O+
  elif t[1]=8          then return Concatenation("O",String(2*t[2]),"-(",qstr,")");            ## O-
  elif t[1]=5          then return Concatenation("O",String(2*t[2]+1),"(",qstr,")");           ## O
  elif t[1] in [3,7]   then return Concatenation(FamilyNames[t[1]],String(t[2]),"(",qstr,")"); ## L, U
  else return fail;
fi;
end;


########################
##
##   Section 4. Examples 
##
## Finding all non-abelian finite simple groups with prime spectrum a subset of a given set <pi>

##
##  First, paste into GAP all the lists and functions from the above three sections:
##  "Preliminary lists and functions", "Main function", and "Auxiliaries"
##
##  The output of a command is given after a single '#' 
##  A comment is given after a double '#' 


#### Example 1 ####

pi := [ 2, 3, 5, 11, 37, 61, 13421 ];   ##  =  pi( U5(11) ),   ( U5(11) has the largest prime divisor of its order among all group in the Atlas table on pp. 239--242 )

codes := SimpleGroupsPi(pi);;           ## codes of found groups 
time;          # 3369                   ## time may vary for distinct runs/systems/etc.
Size(codes);   #  13

List( codes, NameByCode );           ## names of found groups 
# [ "A5", "A6", "U5(2)", "L2(3^5)", "S4(3)", "L2(11)", "L2(11^2)", "S4(11)", "U3(11)", "U4(11)", "U5(11)", "M11", "M12" ]

List( codes, PiByCode );   ## prime spectra of found groups 
# [ [ 2, 3, 5 ],                     ##  "A5"            
#   [ 2, 3, 5 ],                     ##  "A6"             
#   [ 2, 3, 5, 11 ],                 ##  "U5(2)"              
#   [ 2, 3, 11, 61 ],                ##  "L2(3^5)"             
#   [ 2, 3, 5 ],                     ##  "S4(3)"          
#   [ 2, 3, 5, 11 ],                 ##  "L2(11)"            
#   [ 2, 3, 5, 11, 61 ],             ##  "L2(11^2)"               
#   [ 2, 3, 5, 11, 61 ],             ##  "S4(11)"                
#   [ 2, 3, 5, 11, 37 ],             ##  "U3(11)"                
#   [ 2, 3, 5, 11, 37, 61 ],         ##  "U4(11)"                    
#   [ 2, 3, 5, 11, 37, 61, 13421 ],  ##  "U5(11)"                           
#   [ 2, 3, 5, 11 ],                 ##  "M11"                
#   [ 2, 3, 5, 11 ] ]                ##  "M12"                



#### Example 2 ####

SetInfoLevel(InfoPiSimple,1);                         ## to keep track of calculations
codesSimpleGroups1000 := SimpleGroupsPi(Primes);;     ## codes for all FSGs with prime divisors of their orders at most 1000

#I  p = 2
#I    Case Ln(q)
#I    Case S2n(q)
#
#  ..... Verbose output omitted .....
#
#I    Case 2F4(q)
#I    Case 2G2(q)
#I    Case Sporadic
 
Size(codesSimpleGroups1000);   #  1972                ##  => There are 1972 non-abelian FSGs with prime divisors of their orders at most 1000


#### Example 3 ####

## Obs. Larger lists of primes ( than those available in GAP by default ) 
##      can be downloaded from various online sources, e.g., from t5k.org

## Assuming <Primes4> is a list of all 1229 primes not exceeding 10000

codesSimpleGroups10000 := SimpleGroupsPi( Primes4 );;    ## codes for all FSGs with prime divisors of their orders at most 10000
time; # 90685445                                         ##  ~ 25 hours ( time may vary for distinct runs/systems/etc. )

Size(codesSimpleGroups10000); # 15072                    ##  => There are 15072 non-abelian FSGs with prime divisors of their orders at most 10000
                                                         ##     as claimed in the paper

## Sorting <codesSimpleGroups10000> by largest prime factor :

## The result of the following soritng procedure is a list <sortedCodesSimpleGroups10000> of pairs [ p, list_p ], where 
## 
## p                is a prime (up to 10000)
## list_p           is a list of tuples [ name, generic, primeSpectrum, collectedFactors, code ]
##                     one for each group G whose maximal prime divisor of its orders is <p>
## name             is the name string of G
## generic          is true of false according as G is generic or not
## primeSpectrum    is pi(G) (omitted for large alternating groups)
## collectedFactors is the factorisation of the order (omitted for large alternating groups)
## code             is the code of G 

sortedCodesSimpleGroups10000 := List(Primes4,p->[p,[]]);;  
for code in codesSimpleGroups10000 do
  name := NameByCode(code);
  if code[1]=2 and code[2]>=23 then  
    if IsPrime(code[2]) then maxPrime := code[2]; else
                             maxPrime := PrevPrimeInt( code[2] );
    fi;
    pos := Position(Primes4,maxPrime);
    Add(sortedCodesSimpleGroups10000[pos][2],[name,true,code]);
  else
    order := OrderByCode(code);
    collectedFactors := Collected( Factors(order) );
    primeSpectrum := List( collectedFactors, r -> r[1] );
    maxPrime := primeSpectrum[Size(primeSpectrum)];
    pos := Position(Primes4,maxPrime);
    generic := code[1]=2 or code=[3,2,maxPrime,1];  ## generic marker
    Add(sortedCodesSimpleGroups10000[pos][2],[name,generic,primeSpectrum,collectedFactors,code]);
  fi;
od;

time; #  11695                       ## may vary for distinct runs/systems/etc.

sortedCodesSimpleGroups10000;        ## result

# [ [ 2, [  ] ], 
#   [ 3, [  ] ], 
#   [ 5, [  [ "A5", true, [ 2, 3, 5 ], [ [ 2, 2 ], [ 3, 1 ], [ 5, 1 ] ], [ 2, 5, 0, 0 ] ], 
#           [ "A6", true, [ 2, 3, 5 ], [ [ 2, 3 ], [ 3, 2 ], [ 5, 1 ] ], [ 2, 6, 0, 0 ] ], 
#           [ "S4(3)", false, [ 2, 3, 5 ], [ [ 2, 6 ], [ 3, 4 ], [ 5, 1 ] ], [ 4, 2, 3, 1 ] ] ] ], 
#   [ 7, [  [ "A7", true, [ 2, 3, 5, 7 ], [ [ 2, 3 ], [ 3, 2 ], [ 5, 1 ], [ 7, 1 ] ], [ 2, 7, 0, 0 ] ], 
#           [ "A8", true, [ 2, 3, 5, 7 ], [ [ 2, 6 ], [ 3, 2 ], [ 5, 1 ], [ 7, 1 ] ], [ 2, 8, 0, 0 ] ], 
#           [ "A9", true, [ 2, 3, 5, 7 ], [ [ 2, 6 ], [ 3, 4 ], [ 5, 1 ], [ 7, 1 ] ], [ 2, 9, 0, 0 ] ], 
#           [ "A10", true, [ 2, 3, 5, 7 ], [ [ 2, 7 ], [ 3, 4 ], [ 5, 2 ], [ 7, 1 ] ], [ 2, 10, 0, 0 ] ], 
#           [ "L3(4)", false, [ 2, 3, 5, 7 ], [ [ 2, 6 ], [ 3, 2 ], [ 5, 1 ], [ 7, 1 ] ], [ 3, 3, 2, 2 ] ], 
#           [ "L2(8)", false, [ 2, 3, 7 ], [ [ 2, 3 ], [ 3, 2 ], [ 7, 1 ] ], [ 3, 2, 2, 3 ] ], 
#           [ "S6(2)", false, [ 2, 3, 5, 7 ], [ [ 2, 9 ], [ 3, 4 ], [ 5, 1 ], [ 7, 1 ] ], [ 4, 3, 2, 1 ] ], 
#           [ "O8+(2)", false, [ 2, 3, 5, 7 ], [ [ 2, 12 ], [ 3, 5 ], [ 5, 2 ], [ 7, 1 ] ], [ 6, 4, 2, 1 ] ], 
#           [ "U3(3)", false, [ 2, 3, 7 ], [ [ 2, 5 ], [ 3, 3 ], [ 7, 1 ] ], [ 7, 3, 3, 1 ] ], 
#           [ "U4(3)", false, [ 2, 3, 5, 7 ], [ [ 2, 7 ], [ 3, 6 ], [ 5, 1 ], [ 7, 1 ] ], [ 7, 4, 3, 1 ] ], 
#           [ "U3(5)", false, [ 2, 3, 5, 7 ], [ [ 2, 4 ], [ 3, 2 ], [ 5, 3 ], [ 7, 1 ] ], [ 7, 3, 5, 1 ] ], 
#           [ "L2(7)", true, [ 2, 3, 7 ], [ [ 2, 3 ], [ 3, 1 ], [ 7, 1 ] ], [ 3, 2, 7, 1 ] ], 
#           [ "L2(49)", false, [ 2, 3, 5, 7 ], [ [ 2, 4 ], [ 3, 1 ], [ 5, 2 ], [ 7, 2 ] ], [ 3, 2, 7, 2 ] ], 
#           [ "S4(7)", false, [ 2, 3, 5, 7 ], [ [ 2, 8 ], [ 3, 2 ], [ 5, 2 ], [ 7, 4 ] ], [ 4, 2, 7, 1 ] ], 
#           [ "J2", false, [ 2, 3, 5, 7 ], [ [ 2, 7 ], [ 3, 3 ], [ 5, 2 ], [ 7, 1 ] ], [ 1, 5, 0, 0 ] ] ] ], 
# 
#    ......  output omitted for primes 11 through 9949  ......
# 
#   [ 9967, [ [ "A9967", true, [ 2, 9967, 0, 0 ] ], 
#             [ "A9968", true, [ 2, 9968, 0, 0 ] ], 
#             [ "A9969", true, [ 2, 9969, 0, 0 ] ], 
#             [ "A9970", true, [ 2, 9970, 0, 0 ] ], 
#             [ "A9971", true, [ 2, 9971, 0, 0 ] ], 
#             [ "A9972", true, [ 2, 9972, 0, 0 ] ], 
#             [ "L3(457)", false, [ 2, 3, 7, 19, 229, 457, 9967 ], [ [ 2, 7 ], [ 3, 2 ], [ 7, 1 ], [ 19, 2 ], [ 229, 1 ], [ 457, 3 ], [ 9967, 1 ] ], [ 3, 3, 457, 1 ] ], 
#             [ "L4(457)", false, [ 2, 3, 5, 7, 19, 229, 457, 4177, 9967 ], [ [ 2, 10 ], [ 3, 4 ], [ 5, 2 ], [ 7, 1 ], [ 19, 3 ], [ 229, 2 ], [ 457, 6 ], [ 4177, 1 ], [ 9967, 1 ] ], [ 3, 4, 457, 1 ] ], 
#             [ "L2(9967)", true, [ 2, 3, 7, 11, 89, 151, 9967 ], [ [ 2, 4 ], [ 3, 1 ], [ 7, 1 ], [ 11, 1 ], [ 89, 1 ], [ 151, 1 ], [ 9967, 1 ] ], [ 3, 2, 9967, 1 ] ] ] ], 
#   [ 9973, [ [ "A9973", true, [ 2, 9973, 0, 0 ] ], 
#             [ "A9974", true, [ 2, 9974, 0, 0 ] ], 
#             [ "A9975", true, [ 2, 9975, 0, 0 ] ], 
#             [ "A9976", true, [ 2, 9976, 0, 0 ] ], 
#             [ "A9977", true, [ 2, 9977, 0, 0 ] ], 
#             [ "A9978", true, [ 2, 9978, 0, 0 ] ], 
#             [ "A9979", true, [ 2, 9979, 0, 0 ] ], 
#             [ "A9980", true, [ 2, 9980, 0, 0 ] ], 
#             [ "A9981", true, [ 2, 9981, 0, 0 ] ], 
#             [ "A9982", true, [ 2, 9982, 0, 0 ] ], 
#             [ "A9983", true, [ 2, 9983, 0, 0 ] ], 
#             [ "A9984", true, [ 2, 9984, 0, 0 ] ], 
#             [ "A9985", true, [ 2, 9985, 0, 0 ] ], 
#             [ "A9986", true, [ 2, 9986, 0, 0 ] ], 
#             [ "A9987", true, [ 2, 9987, 0, 0 ] ], 
#             [ "A9988", true, [ 2, 9988, 0, 0 ] ], 
#             [ "A9989", true, [ 2, 9989, 0, 0 ] ], 
#             [ "A9990", true, [ 2, 9990, 0, 0 ] ], 
#             [ "A9991", true, [ 2, 9991, 0, 0 ] ], 
#             [ "A9992", true, [ 2, 9992, 0, 0 ] ], 
#             [ "A9993", true, [ 2, 9993, 0, 0 ] ], 
#             [ "A9994", true, [ 2, 9994, 0, 0 ] ], 
#             [ "A9995", true, [ 2, 9995, 0, 0 ] ], 
#             [ "A9996", true, [ 2, 9996, 0, 0 ] ], 
#             [ "A9997", true, [ 2, 9997, 0, 0 ] ], 
#             [ "A9998", true, [ 2, 9998, 0, 0 ] ], 
#             [ "A9999", true, [ 2, 9999, 0, 0 ] ], 
#             [ "A10000", true, [ 2, 10000, 0, 0 ] ],
#             [ "A10001", true, [ 2, 10001, 0, 0 ] ], 
#             [ "A10002", true, [ 2, 10002, 0, 0 ] ], 
#             [ "A10003", true, [ 2, 10003, 0, 0 ] ], 
#             [ "A10004", true, [ 2, 10004, 0, 0 ] ], 
#             [ "A10005", true, [ 2, 10005, 0, 0 ] ], 
#             [ "A10006", true, [ 2, 10006, 0, 0 ] ], 
#             [ "L2(9973)", true, [ 2, 3, 277, 4987, 9973 ], [ [ 2, 2 ], [ 3, 2 ], [ 277, 1 ], [ 4987, 1 ], [ 9973, 1 ] ], [ 3, 2, 9973, 1 ] ] ] ] ]

## Theorem 1 and the Tables follow from the above outputs

  
#### Example 4 ####
##
## Sorting the groups from Theorem 1 by the size of their prime spectrum
##
## In other words, we find all n-primary nonabelian finite simple groups G for n >= 3 
## with max( pi(G) ) < 10000

## We assume that <codesSimpleGroups10000> is as calculated in Example 3 above

## First, let us filter out the non-alternating groups,
##   because finding the prime spectra of large alternating groups is
##   straightforward theoretically, but time-consuming computationally

codesSimpleNonAltGroups10000 := 
  Filtered(codesSimpleGroups10000, code -> not code[1]=2 );;         ## codes of non-alternating groups with prime divisors less than 10000
Size(codesSimpleNonAltGroups10000); # 5070

piSizesNonAlt := Set( codesSimpleNonAltGroups10000 , code -> 
                    Size(Collected(Factors(OrderByCode(code)))) );   ## Possible sizes of prime spectra of non-alternating groups

# [ 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24 ]                            

## Conclusion: The largest size of prime spectrum for non-alternating groups is 24 as claimed in the paper

## Finding all non-alternating groups for every fixed possible size of prime spectrum :

## The result of the following procedure is a list <piSizeSortedNonAlt> of pairs [ size, codes_size ], where 
##    size        is one of possible sizes 3..24 of prime spectrum
##    codes_size  is the set of codes of all n-primary non-alternating groups with n = <size>

piSizeSortedNonAlt := List( piSizesNonAlt, n -> [ n, [] ] );;   ## initialising the resulting list
piSize := 0;;                                                   ## this suppresses the "Unbound global variable" warning

for code in codesSimpleNonAltGroups10000 do
  piSize := Size(PiByCode(code));                               ## size of prime spectrum
  rcd := First( piSizeSortedNonAlt, r -> r[1] = piSize );
  AddSet( rcd[2], code );
od;

List( piSizeSortedNonAlt, r -> [r[1],Size(r[2])] );             ## numbers of n-primary NON-ALTERNATING groups for n = 3..24

# [ [  3,   6 ], [  4,  61 ], [ 5,  347 ], [ 6, 711 ], [  7, 593 ], [  8, 624 ], [  9, 822 ], [ 10, 639 ], [ 11, 392 ], 
#   [ 12, 305 ], [ 13, 236 ], [ 14, 115 ], [ 15, 81 ], [ 16,  56 ], [ 17,  30 ], [ 18,   6 ], [ 19,  14 ], [ 20,   5 ], 
#   [ 21,  10 ], [ 22,  11 ], [ 23,   2 ], [ 24,  4 ] ]

### Adding the codes of n-primary alternating groups ( up to n = 24 ) :

##  Obs. The number of n-primary alternating groups equals p{n+1} - p{n} where p{n} is the n-th prime.

## The result of the following procedure is a list <piSizeSorted> of pairs [ size, codes_size ], where 
##    size        is in [3..24]
##    codes_size  is the set of codes of all n-primary groups with n = <size> including alternating groups

piSizeSorted := ShallowCopy( piSizeSortedNonAlt );;       
for rcd in piSizeSorted do
  for p in [Primes[rcd[1]]..Primes[rcd[1]+1]-1] do
    AddSet(rcd[2], [2,p,0,0]);
  od;
od;

List( piSizeSorted, r -> [r[1],Size(r[2])] );                    ## numbers of ALL n-primary groups  for n = 3..24

# [ [ 3, 8 ], [ 4, 65 ], [ 5, 349 ], [ 6, 715 ], [ 7, 595 ], [ 8, 628 ], [ 9, 828 ], [ 10, 641 ], [ 11, 398 ], 
#   [ 12, 309 ], [ 13, 238 ], [ 14, 119 ], [ 15, 87 ], [ 16, 62 ], [ 17, 32 ], [ 18, 12 ], [ 19, 18 ], 
#   [ 20, 7 ], [ 21, 16 ], [ 22, 15 ], [ 23, 8 ], [ 24, 12 ] ]

## This justifies the list of |Kn| for n = 3..24 given in the paper

## Printing all simple n-primary groups G (for n <= 24) with max( pi(G) ) < 10000 :

for rcd in piSizeSorted do
  Print(" Groups with prime spectrum of size ",rcd[1]," (",Size(rcd[2])," groups) :\n");
  for code in rcd[2] do 
    Print(NameByCode(code)," ");
  od;
  Print("\n\n");
od;

#  Groups with prime spectrum of size 3 (8 groups) :
# A5 A6 L2(8) L2(7) L2(17) L3(3) S4(3) U3(3) 

#  Groups with prime spectrum of size 4 (65 groups) :
# M11 M12 J2 A7 A8 A9 A10 L2(16) L2(32) L2(2^7) L2(2^13) L2(27) L2(81) L2(3^5) L2(3^7) L2(25) L2(49) L2(11) L2(13) L2(19) L2(23) L2(31) L2(37) L2(47) L2(53) L2(73) L2(97) L2(107) L2(127) L2(163) L2(193) L2(257) L2(383) L2(487) L2(577) L2(863) L2(1153) L2(2593) L2(2917) L2(4373) L2(8747) L3(4) L3(8) L3(5) L3(7) L3(17) L4(3) S4(4) S4(9) S4(5) S4(7) S6(2) O8+(2) U3(4) U3(8) U3(9) U3(5) U3(7) U4(3) U5(2) G2(3) 3D4(2) Sz(8) Sz(32) 2F4(2)' 

#  Groups with prime spectrum of size 5 (349 groups) :
# M22 HS J3 McL He A11 A12 L2(64) L2(2^8) L2(2^9) L2(2^11) L2(5^3) L2(5^4) L2(7^3) L2(7^4) L2(11^2) L2(17^2) L2(19^2) L2(29) L2(41) L2(43) L2(59) L2(61) L2(67) L2(71) L2(79) L2(83) L2(89) L2(101) L2(103) L2(109) L2(113) L2(137) L2(149) L2(151) L2(157) L2(167) L2(173) L2(179) L2(191) L2(197) L2(199) L2(223) L2(227) L2(233) L2(241) L2(251) L2(263) L2(269) L2(271) L2(277) L2(283) L2(293) L2(313) L2(317) L2(337) L2(347) L2(353) L2(359) L2(367) L2(397) L2(401) L2(431) L2(433) L2(449) L2(457) L2(467) L2(479) L2(499) L2(503) L2(523) L2(541) L2(557) L2(563) L2(587) L2(593) L2(607) L2(613) L2(641) L2(647) L2(653) L2(673) L2(677) L2(719) L2(733) L2(751) L2(757) L2(773) L2(787) L2(809) L2(823) L2(877) L2(887) L2(907) L2(971) L2(977) L2(983) L2(997) L2(1087) L2(1097) L2(1151) L2(1187) L2(1193) L2(1201) L2(1213) L2(1237) L2(1249) L2(1279) L2(1283) L2(1297) L2(1307) L2(1367) L2(1373) L2(1423) L2(1433) L2(1439) L2(1447) L2(1453) L2(1459) L2(1487) L2(1493) L2(1523) L2(1543) L2(1567) L2(1601) L2(1619) L2(1621) L2(1657) L2(1663) L2(1697) L2(1733) L2(1753) L2(1783) L2(1823) L2(1867) L2(1873) L2(1907) L2(1993) L2(1997) L2(1999) L2(2017) L2(2027) L2(2063) L2(2083) L2(2137) L2(2153) L2(2207) L2(2251) L2(2273) L2(2383) L2(2447) L2(2467) L2(2473) L2(2503) L2(2557) L2(2647) L2(2657) L2(2663) L2(2693) L2(2753) L2(2767) L2(2777) L2(2797) L2(2803) L2(2879) L2(2903) L2(2999) L2(3023) L2(3137) L2(3167) L2(3187) L2(3203) L2(3217) L2(3253) L2(3313) L2(3413) L2(3463) L2(3467) L2(3517) L2(3547) L2(3583) L2(3593) L2(3617) L2(3623) L2(3643) L2(3677) L2(3727) L2(3733) L2(3803) L2(3833) L2(3889) L2(3967) L2(4007) L2(4051) L2(4057) L2(4127) L2(4177) L2(4253) L2(4273) L2(4337) L2(4357) L2(4363) L2(4457) L2(4517) L2(4547) L2(4567) L2(4703) L2(4723) L2(4799) L2(4801) L2(4933) L2(4937) L2(5023) L2(5077) L2(5087) L2(5113) L2(5119) L2(5233) L2(5273) L2(5297) L2(5323) L2(5387) L2(5399) L2(5437) L2(5443) L2(5483) L2(5507) L2(5527) L2(5647) L2(5717) L2(5807) L2(6037) L2(6047) L2(6113) L2(6143) L2(6173) L2(6197) L2(6317) L2(6337) L2(6353) L2(6367) L2(6373) L2(6547) L2(6653) L2(6703) L2(6737) L2(6823) L2(6827) L2(6857) L2(6911) L2(6977) L2(6983) L2(7057) L2(7187) L2(7213) L2(7247) L2(7417) L2(7507) L2(7537) L2(7577) L2(7607) L2(7703) L2(7793) L2(7817) L2(7823) L2(7927) L2(7933) L2(7937) L2(8101) L2(8167) L2(8263) L2(8353) L2(8423) L2(8543) L2(8563) L2(8573) L2(8677) L2(8713) L2(8753) L2(8783) L2(8837) L2(8963) L2(9013) L2(9067) L2(9133) L2(9137) L2(9187) L2(9277) L2(9343) L2(9377) L2(9403) L2(9467) L2(9473) L2(9497) L2(9601) L2(9643) L2(9721) L2(9817) L2(9887) L2(9973) L3(9) L3(27) L3(13) L3(19) L3(31) L3(73) L3(97) L3(127) L4(4) L4(5) L4(7) L5(2) L5(3) L6(2) S4(8) S4(16) S4(25) S4(49) S4(11) S4(17) S4(19) S6(3) S8(2) O7(3) O8+(3) U3(16) U3(32) U3(2^7) U3(81) U3(25) U3(11) U3(13) U3(17) U3(19) U3(23) U3(53) U4(4) U4(9) U4(5) U4(7) U5(3) U6(2) O8-(2) G2(4) G2(8) G2(5) G2(7) 3D4(3) Sz(2^7) 

#  Groups with prime spectrum of size 6 (715 groups) :
# J1 M23 M24 Ru Suz Co3 Co2 Fi22 HN A13 A14 A15 A16 L2(2^10) L2(3^6) L2(3^8) L2(3^10) L2(3^11) L2(5^5) L2(7^5) L2(11^4) L2(13^2) L2(13^3) L2(17^3) L2(19^3) L2(23^2) L2(29^2) L2(31^2) L2(37^2) L2(41^2) L2(53^2) L2(59^2) L2(61^2) L2(71^2) L2(79^2) L2(97^2) L2(101^2) L2(107^2) L2(127^2) L2(131) L2(139) L2(163^2) L2(181) L2(193^2) L2(211) L2(229) L2(239) L2(257^2) L2(281) L2(307) L2(311) L2(331) L2(349) L2(373) L2(379) L2(389) L2(409) L2(421) L2(439) L2(443) L2(463) L2(491) L2(509) L2(521) L2(547) L2(569) L2(599) L2(601) L2(617) L2(619) L2(631) L2(643) L2(661) L2(683) L2(691) L2(701) L2(709) L2(727) L2(739) L2(743) L2(761) L2(769) L2(797) L2(811) L2(821) L2(827) L2(829) L2(839) L2(853) L2(857) L2(881) L2(883) L2(919) L2(929) L2(937) L2(941) L2(947) L2(953) L2(967) L2(991) L2(1009) L2(1013) L2(1019) L2(1031) L2(1033) L2(1039) L2(1049) L2(1051) L2(1061) L2(1063) L2(1069) L2(1093) L2(1103) L2(1109) L2(1117) L2(1123) L2(1129) L2(1163) L2(1171) L2(1181) L2(1217) L2(1223) L2(1229) L2(1277) L2(1303) L2(1319) L2(1321) L2(1327) L2(1361) L2(1381) L2(1399) L2(1409) L2(1451) L2(1471) L2(1489) L2(1499) L2(1511) L2(1531) L2(1549) L2(1553) L2(1571) L2(1579) L2(1583) L2(1607) L2(1613) L2(1627) L2(1637) L2(1667) L2(1669) L2(1693) L2(1699) L2(1723) L2(1747) L2(1759) L2(1777) L2(1787) L2(1789) L2(1801) L2(1811) L2(1831) L2(1877) L2(1879) L2(1889) L2(1901) L2(1913) L2(1933) L2(1949) L2(1951) L2(1987) L2(2011) L2(2039) L2(2053) L2(2081) L2(2087) L2(2099) L2(2111) L2(2113) L2(2143) L2(2161) L2(2179) L2(2203) L2(2213) L2(2237) L2(2239) L2(2267) L2(2269) L2(2287) L2(2293) L2(2297) L2(2333) L2(2341) L2(2347) L2(2351) L2(2357) L2(2371) L2(2377) L2(2389) L2(2399) L2(2411) L2(2417) L2(2423) L2(2459) L2(2477) L2(2539) L2(2543) L2(2579) L2(2591) L2(2609) L2(2633) L2(2671) L2(2677) L2(2683) L2(2687) L2(2689) L2(2699) L2(2707) L2(2711) L2(2713) L2(2719) L2(2741) L2(2749) L2(2791) L2(2801) L2(2819) L2(2833) L2(2837) L2(2843) L2(2857) L2(2887) L2(2897) L2(2909) L2(2953) L2(2957) L2(2963) L2(2971) L2(3001) L2(3019) L2(3041) L2(3049) L2(3061) L2(3083) L2(3089) L2(3119) L2(3169) L2(3209) L2(3251) L2(3257) L2(3259) L2(3271) L2(3307) L2(3323) L2(3329) L2(3343) L2(3347) L2(3361) L2(3371) L2(3373) L2(3391) L2(3407) L2(3449) L2(3457) L2(3461) L2(3469) L2(3491) L2(3511) L2(3527) L2(3529) L2(3533) L2(3557) L2(3559) L2(3581) L2(3607) L2(3631) L2(3637) L2(3671) L2(3673) L2(3697) L2(3701) L2(3767) L2(3779) L2(3793) L2(3797) L2(3823) L2(3847) L2(3853) L2(3863) L2(3881) L2(3907) L2(3917) L2(3919) L2(3923) L2(3929) L2(3931) L2(3943) L2(3947) L2(4001) L2(4013) L2(4021) L2(4049) L2(4073) L2(4079) L2(4099) L2(4111) L2(4133) L2(4139) L2(4153) L2(4157) L2(4211) L2(4231) L2(4243) L2(4259) L2(4261) L2(4283) L2(4297) L2(4327) L2(4349) L2(4391) L2(4397) L2(4441) L2(4447) L2(4463) L2(4481) L2(4483) L2(4493) L2(4507) L2(4513) L2(4519) L2(4561) L2(4583) L2(4597) L2(4603) L2(4637) L2(4639) L2(4643) L2(4651) L2(4657) L2(4673) L2(4679) L2(4721) L2(4733) L2(4751) L2(4783) L2(4787) L2(4793) L2(4813) L2(4877) L2(4903) L2(4909) L2(4919) L2(4943) L2(4951) L2(4967) L2(4973) L2(4987) L2(4993) L2(4999) L2(5003) L2(5009) L2(5021) L2(5051) L2(5099) L2(5101) L2(5107) L2(5153) L2(5189) L2(5197) L2(5227) L2(5231) L2(5261) L2(5309) L2(5347) L2(5351) L2(5393) L2(5407) L2(5413) L2(5417) L2(5441) L2(5449) L2(5471) L2(5477) L2(5503) L2(5557) L2(5563) L2(5569) L2(5573) L2(5581) L2(5623) L2(5639) L2(5651) L2(5653) L2(5683) L2(5689) L2(5693) L2(5701) L2(5737) L2(5743) L2(5749) L2(5779) L2(5783) L2(5791) L2(5801) L2(5813) L2(5827) L2(5843) L2(5857) L2(5861) L2(5867) L2(5869) L2(5879) L2(5897) L2(5903) L2(5923) L2(5927) L2(5939) L2(5953) L2(5987) L2(6011) L2(6043) L2(6053) L2(6067) L2(6073) L2(6079) L2(6101) L2(6121) L2(6133) L2(6151) L2(6199) L2(6211) L2(6217) L2(6247) L2(6263) L2(6277) L2(6287) L2(6311) L2(6361) L2(6389) L2(6427) L2(6451) L2(6473) L2(6481) L2(6521) L2(6529) L2(6563) L2(6569) L2(6599) L2(6607) L2(6619) L2(6637) L2(6659) L2(6661) L2(6673) L2(6701) L2(6719) L2(6779) L2(6781) L2(6793) L2(6803) L2(6829) L2(6871) L2(6883) L2(6899) L2(6907) L2(6947) L2(6949) L2(6961) L2(6967) L2(6997) L2(7001) L2(7013) L2(7027) L2(7043) L2(7079) L2(7103) L2(7109) L2(7121) L2(7127) L2(7159) L2(7207) L2(7219) L2(7243) L2(7283) L2(7297) L2(7351) L2(7393) L2(7433) L2(7451) L2(7457) L2(7477) L2(7487) L2(7499) L2(7517) L2(7523) L2(7529) L2(7559) L2(7573) L2(7583) L2(7603) L2(7643) L2(7649) L2(7673) L2(7681) L2(7687) L2(7691) L2(7717) L2(7723) L2(7727) L2(7753) L2(7757) L2(7759) L2(7841) L2(7873) L2(7883) L2(7901) L2(7907) L2(7949) L2(7963) L2(7993) L2(8011) L2(8017) L2(8039) L2(8053) L2(8069) L2(8081) L2(8087) L2(8089) L2(8111) L2(8117) L2(8123) L2(8147) L2(8191) L2(8209) L2(8221) L2(8231) L2(8233) L2(8237) L2(8243) L2(8287) L2(8291) L2(8297) L2(8311) L2(8317) L2(8369) L2(8377) L2(8387) L2(8389) L2(8443) L2(8447) L2(8461) L2(8521) L2(8537) L2(8597) L2(8599) L2(8623) L2(8627) L2(8629) L2(8641) L2(8663) L2(8699) L2(8707) L2(8719) L2(8803) L2(8819) L2(8831) L2(8863) L2(8887) L2(8893) L2(8923) L2(8951) L2(8999) L2(9001) L2(9007) L2(9091) L2(9103) L2(9127) L2(9161) L2(9173) L2(9181) L2(9209) L2(9227) L2(9257) L2(9293) L2(9319) L2(9341) L2(9391) L2(9397) L2(9413) L2(9433) L2(9533) L2(9551) L2(9587) L2(9623) L2(9649) L2(9677) L2(9679) L2(9697) L2(9719) L2(9733) L2(9739) L2(9743) L2(9749) L2(9787) L2(9833) L2(9839) L2(9851) L2(9883) L2(9901) L2(9907) L2(9923) L2(9949) L3(16) L3(32) L3(2^7) L3(3^5) L3(25) L3(49) L3(11) L3(23) L3(37) L3(41) L3(43) L3(47) L3(53) L3(59) L3(71) L3(89) L3(103) L3(157) L3(193) L3(257) L3(313) L3(577) L4(8) L4(9) L4(17) L4(19) L5(7) L6(3) L7(2) S4(32) S4(27) S4(81) S4(3^5) S4(11^2) S4(13) S4(23) S4(29) S4(31) S4(37) S4(41) S4(53) S4(59) S4(61) S4(71) S4(79) S4(97) S4(101) S4(107) S4(127) S4(163) S4(193) S4(257) S6(4) S6(5) S6(7) S8(3) O7(5) O7(7) O9(3) O8+(4) O8+(5) O8+(7) O10+(2) U3(27) U3(5^3) U3(49) U3(29) U3(31) U3(37) U3(41) U3(47) U3(67) U3(71) U3(73) U3(79) U3(83) U3(97) U3(107) U3(113) U3(127) U3(137) U3(149) U3(167) U3(383) U4(8) U4(16) U4(25) U4(11) U4(19) U5(4) U5(9) U5(5) U6(3) U7(2) O8-(3) O10-(2) G2(9) G2(13) G2(17) G2(19) F4(2) 3D4(4) 3D4(5) Sz(2^11) Sz(2^13) 2G2(27) 

#  Groups with prime spectrum of size 7 (595 groups) :
# ON Th Co1 A17 A18 L2(2^12) L2(2^14) L2(2^15) L2(2^21) L2(3^9) L2(5^6) L2(7^7) L2(11^3) L2(19^4) L2(23^3) L2(31^3) L2(41^3) L2(43^2) L2(47^2) L2(53^3) L2(67^2) L2(71^3) L2(73^2) L2(73^3) L2(89^2) L2(97^3) L2(103^2) L2(109^2) L2(113^2) L2(127^3) L2(131^2) L2(137^2) L2(139^2) L2(149^2) L2(151^2) L2(167^2) L2(179^2) L2(197^2) L2(223^2) L2(227^2) L2(239^2) L2(241^2) L2(251^2) L2(263^2) L2(269^2) L2(277^2) L2(283^2) L2(359^2) L2(419) L2(431^2) L2(457^2) L2(461) L2(479^2) L2(487^2) L2(571) L2(577^2) L2(607^2) L2(659) L2(719^2) L2(809^2) L2(859) L2(911) L2(971^2) L2(1021) L2(1091) L2(1153^2) L2(1193^2) L2(1231) L2(1259) L2(1289) L2(1291) L2(1301) L2(1307^2) L2(1427) L2(1481) L2(1483) L2(1559) L2(1597) L2(1601^2) L2(1609) L2(1621^2) L2(1709) L2(1721) L2(1741) L2(1847) L2(1861) L2(1871) L2(1931) L2(1973) L2(1979) L2(1999^2) L2(2003) L2(2029) L2(2069) L2(2089) L2(2129) L2(2131) L2(2141) L2(2221) L2(2243) L2(2281) L2(2309) L2(2311) L2(2339) L2(2381) L2(2393) L2(2437) L2(2441) L2(2521) L2(2531) L2(2549) L2(2551) L2(2593^2) L2(2617) L2(2621) L2(2659) L2(2731) L2(2789) L2(2851) L2(2861) L2(2927) L2(2939) L2(2969) L2(3011) L2(3037) L2(3067) L2(3079) L2(3109) L2(3121) L2(3163) L2(3181) L2(3221) L2(3229) L2(3299) L2(3301) L2(3319) L2(3331) L2(3359) L2(3389) L2(3433) L2(3499) L2(3539) L2(3613) L2(3659) L2(3691) L2(3709) L2(3719) L2(3761) L2(3769) L2(3821) L2(3851) L2(3877) L2(3911) L2(3989) L2(4019) L2(4027) L2(4091) L2(4093) L2(4129) L2(4159) L2(4201) L2(4217) L2(4219) L2(4229) L2(4241) L2(4271) L2(4289) L2(4339) L2(4409) L2(4423) L2(4451) L2(4549) L2(4591) L2(4621) L2(4649) L2(4663) L2(4729) L2(4789) L2(4817) L2(4831) L2(4861) L2(4871) L2(4889) L2(4931) L2(4957) L2(4969) L2(5011) L2(5039) L2(5059) L2(5081) L2(5147) L2(5167) L2(5171) L2(5179) L2(5209) L2(5237) L2(5281) L2(5303) L2(5333) L2(5381) L2(5419) L2(5431) L2(5479) L2(5501) L2(5519) L2(5521) L2(5531) L2(5591) L2(5657) L2(5659) L2(5669) L2(5711) L2(5821) L2(5839) L2(5849) L2(5881) L2(5981) L2(6007) L2(6029) L2(6089) L2(6091) L2(6131) L2(6163) L2(6203) L2(6221) L2(6229) L2(6257) L2(6269) L2(6271) L2(6299) L2(6301) L2(6323) L2(6329) L2(6343) L2(6359) L2(6379) L2(6397) L2(6421) L2(6449) L2(6469) L2(6491) L2(6551) L2(6553) L2(6571) L2(6577) L2(6581) L2(6679) L2(6689) L2(6691) L2(6761) L2(6763) L2(6791) L2(6833) L2(6841) L2(6863) L2(6869) L2(6917) L2(6959) L2(6991) L2(7019) L2(7039) L2(7129) L2(7151) L2(7177) L2(7193) L2(7211) L2(7229) L2(7237) L2(7253) L2(7307) L2(7321) L2(7331) L2(7333) L2(7349) L2(7369) L2(7459) L2(7489) L2(7541) L2(7547) L2(7549) L2(7561) L2(7621) L2(7639) L2(7669) L2(7699) L2(7741) L2(7829) L2(7867) L2(7877) L2(7879) L2(7919) L2(7951) L2(8093) L2(8171) L2(8179) L2(8219) L2(8269) L2(8273) L2(8293) L2(8329) L2(8363) L2(8419) L2(8429) L2(8431) L2(8467) L2(8501) L2(8513) L2(8527) L2(8539) L2(8609) L2(8647) L2(8669) L2(8681) L2(8689) L2(8693) L2(8731) L2(8737) L2(8761) L2(8807) L2(8821) L2(8839) L2(8849) L2(8861) L2(8867) L2(8929) L2(8933) L2(8941) L2(8971) L2(9011) L2(9041) L2(9049) L2(9059) L2(9109) L2(9151) L2(9157) L2(9199) L2(9203) L2(9221) L2(9241) L2(9311) L2(9323) L2(9337) L2(9371) L2(9419) L2(9421) L2(9431) L2(9437) L2(9439) L2(9463) L2(9479) L2(9511) L2(9521) L2(9539) L2(9613) L2(9629) L2(9631) L2(9661) L2(9767) L2(9769) L2(9781) L2(9791) L2(9803) L2(9811) L2(9829) L2(9857) L2(9871) L2(9929) L2(9931) L2(9941) L2(9967) L3(64) L3(81) L3(5^3) L3(7^3) L3(19^2) L3(29) L3(61) L3(67) L3(79) L3(83) L3(107) L3(109) L3(113) L3(151) L3(163) L3(179) L3(197) L3(227) L3(233) L3(251) L3(283) L3(337) L3(353) L3(367) L3(397) L3(433) L3(449) L3(457) L3(479) L3(499) L3(523) L3(557) L3(587) L3(593) L3(607) L3(647) L3(719) L3(733) L3(787) L3(983) L3(1151) L3(1153) L3(1237) L3(1249) L3(1279) L3(1567) L3(1733) L3(1783) L3(1867) L3(2017) L3(2467) L3(2903) L3(6037) L4(16) L4(27) L4(25) L4(49) L4(11) L4(13) L4(31) L4(41) L4(59) L4(71) L4(97) L4(127) L5(4) L5(5) L6(7) L7(3) L8(2) S4(64) S4(2^7) S4(5^3) S4(19^2) S4(43) S4(47) S4(67) S4(73) S4(89) S4(103) S4(109) S4(113) S4(131) S4(137) S4(139) S4(149) S4(151) S4(167) S4(179) S4(197) S4(223) S4(227) S4(239) S4(241) S4(251) S4(263) S4(269) S4(277) S4(283) S4(359) S4(431) S4(457) S4(479) S4(487) S4(577) S4(607) S4(719) S4(809) S4(971) S4(1153) S4(1193) S4(1307) S4(1601) S4(1621) S4(1999) S4(2593) S6(8) S6(9) S6(19) S8(4) S8(5) S8(7) S10(2) O7(9) O7(19) O9(5) O9(7) O8+(8) O8+(9) O8+(19) O10+(3) O12+(2) U3(64) U3(2^8) U3(3^5) U3(3^7) U3(11^2) U3(19^2) U3(43) U3(59) U3(61) U3(89) U3(109) U3(157) U3(197) U3(223) U3(227) U3(233) U3(241) U3(251) U3(257) U3(263) U3(269) U3(277) U3(293) U3(313) U3(347) U3(401) U3(431) U3(449) U3(499) U3(503) U3(577) U3(607) U3(653) U3(757) U3(809) U3(823) U3(863) U3(877) U3(1097) U3(1153) U3(1283) U3(1367) U3(1619) U3(1663) U3(1697) U3(2153) U3(2251) U3(2917) U3(3217) U3(3623) U3(4373) U3(8101) U4(32) U4(81) U4(49) U4(13) U4(17) U4(23) U4(29) U4(41) U4(53) U4(71) U4(79) U5(7) U6(4) U6(5) U7(3) U8(2) O8-(4) O8-(5) O8-(7) O10-(3) G2(16) G2(32) G2(2^7) G2(27) G2(25) G2(11) G2(23) G2(31) G2(41) G2(53) G2(71) G2(73) G2(97) G2(127) F4(3) 3D4(8) 3D4(9) 3D4(7) Sz(2^9) 2G2(3^5) 2G2(3^7) 

#  Groups with prime spectrum of size 8 (628 groups) :
# Ly Fi23 A19 A20 A21 A22 L2(2^22) L2(2^25) L2(2^26) L2(3^12) L2(5^9) L2(7^6) L2(19^5) L2(29^3) L2(31^4) L2(37^3) L2(43^3) L2(47^3) L2(59^3) L2(67^3) L2(79^3) L2(83^2) L2(83^3) L2(89^3) L2(113^3) L2(157^2) L2(157^3) L2(173^2) L2(191^2) L2(211^2) L2(229^2) L2(233^2) L2(281^2) L2(293^2) L2(311^2) L2(313^2) L2(313^3) L2(317^2) L2(331^2) L2(337^2) L2(353^2) L2(389^2) L2(401^2) L2(439^2) L2(443^2) L2(467^2) L2(491^2) L2(499^2) L2(509^2) L2(523^2) L2(557^2) L2(563^2) L2(593^2) L2(601^2) L2(613^2) L2(643^2) L2(647^2) L2(691^2) L2(709^2) L2(733^2) L2(757^2) L2(787^2) L2(839^2) L2(863^2) L2(887^2) L2(977^2) L2(983^2) L2(1049^2) L2(1097^2) L2(1201^2) L2(1229^2) L2(1237^2) L2(1279^2) L2(1283^2) L2(1297^2) L2(1319^2) L2(1429) L2(1451^2) L2(1453^2) L2(1471^2) L2(1493^2) L2(1523^2) L2(1543^2) L2(1571^2) L2(1657^2) L2(1693^2) L2(1697^2) L2(1733^2) L2(1759^2) L2(1783^2) L2(1801^2) L2(1879^2) L2(1889^2) L2(1993^2) L2(2017^2) L2(2039^2) L2(2063^2) L2(2099^2) L2(2207^2) L2(2383^2) L2(2447^2) L2(2689^2) L2(2729) L2(2749^2) L2(2753^2) L2(2803^2) L2(2909^2) L2(3137^2) L2(3191) L2(3217^2) L2(3253^2) L2(3313^2) L2(3449^2) L2(3469^2) L2(3511^2) L2(3541) L2(3547^2) L2(3571) L2(3643^2) L2(3739) L2(4003) L2(4007^2) L2(4357^2) L2(4373^2) L2(4421) L2(4481^2) L2(4523) L2(4547^2) L2(4567^2) L2(4691) L2(4759) L2(4933^2) L2(5099^2) L2(5119^2) L2(5233^2) L2(5279) L2(5443^2) L2(5641) L2(5741) L2(5807^2) L2(5851) L2(6143^2) L2(6197^2) L2(6529^2) L2(6659^2) L2(6709) L2(6733) L2(6911^2) L2(6971) L2(7069) L2(7309) L2(7411) L2(7481) L2(7589) L2(7591) L2(7607^2) L2(7703^2) L2(7789) L2(7841^2) L2(7853) L2(7927^2) L2(8009) L2(8059) L2(8161) L2(8389^2) L2(8423^2) L2(8581) L2(8741) L2(8779) L2(8969) L2(9029) L2(9043) L2(9067^2) L2(9239) L2(9281) L2(9283) L2(9349) L2(9461) L2(9467^2) L2(9491) L2(9547) L2(9619) L2(9689) L2(9739^2) L2(9859) L2(9887^2) L3(2^8) L3(5^4) L3(11^2) L3(13^2) L3(17^2) L3(41^2) L3(71^2) L3(137) L3(139) L3(149) L3(181) L3(191) L3(229) L3(239) L3(263) L3(269) L3(277) L3(281) L3(307) L3(311) L3(331) L3(347) L3(349) L3(359) L3(379) L3(431) L3(439) L3(463) L3(491) L3(509) L3(521) L3(547) L3(569) L3(601) L3(617) L3(619) L3(631) L3(643) L3(653) L3(691) L3(769) L3(797) L3(823) L3(829) L3(853) L3(877) L3(929) L3(941) L3(953) L3(967) L3(971) L3(997) L3(1009) L3(1087) L3(1123) L3(1367) L3(1399) L3(1439) L3(1453) L3(1459) L3(1471) L3(1543) L3(1553) L3(1601) L3(1621) L3(1663) L3(1873) L3(1999) L3(2027) L3(2153) L3(2207) L3(2269) L3(2351) L3(2503) L3(2689) L3(2749) L3(2819) L3(2999) L3(3253) L3(3313) L3(3323) L3(3631) L3(3767) L3(3793) L3(3797) L3(4231) L3(4253) L3(4327) L3(4457) L3(4493) L3(4723) L3(4933) L3(4937) L3(5077) L3(5273) L3(5437) L3(5527) L3(6079) L3(6287) L3(6317) L3(6637) L3(6703) L3(6793) L3(6911) L3(7027) L3(7187) L3(7537) L3(7577) L3(7703) L3(8573) L3(8629) L3(9067) L3(9277) L3(9403) L3(9601) L3(9721) L4(32) L4(3^5) L4(23) L4(29) L4(37) L4(43) L4(53) L4(61) L4(73) L4(79) L4(89) L4(103) L4(193) L4(257) L5(8) L5(9) L5(11) L5(19) L6(4) L6(5) L8(3) L9(2) S4(2^11) S4(2^13) S4(3^6) S4(7^3) S4(31^2) S4(83) S4(157) S4(173) S4(191) S4(211) S4(229) S4(233) S4(281) S4(293) S4(311) S4(313) S4(317) S4(331) S4(337) S4(353) S4(389) S4(401) S4(439) S4(443) S4(467) S4(491) S4(499) S4(509) S4(523) S4(557) S4(563) S4(593) S4(601) S4(613) S4(643) S4(647) S4(691) S4(709) S4(733) S4(757) S4(787) S4(839) S4(863) S4(887) S4(977) S4(983) S4(1049) S4(1097) S4(1201) S4(1229) S4(1237) S4(1279) S4(1283) S4(1297) S4(1319) S4(1451) S4(1453) S4(1471) S4(1493) S4(1523) S4(1543) S4(1571) S4(1657) S4(1693) S4(1697) S4(1733) S4(1759) S4(1783) S4(1801) S4(1879) S4(1889) S4(1993) S4(2017) S4(2039) S4(2063) S4(2099) S4(2207) S4(2383) S4(2447) S4(2689) S4(2749) S4(2753) S4(2803) S4(2909) S4(3137) S4(3217) S4(3253) S4(3313) S4(3449) S4(3469) S4(3511) S4(3547) S4(3643) S4(4007) S4(4357) S4(4373) S4(4481) S4(4547) S4(4567) S4(4933) S4(5099) S4(5119) S4(5233) S4(5443) S4(5807) S4(6143) S4(6197) S4(6529) S4(6659) S4(6911) S4(7607) S4(7703) S4(7841) S4(7927) S4(8389) S4(8423) S4(9067) S4(9467) S4(9739) S4(9887) S6(16) S6(25) S6(11) S6(13) S6(17) S6(41) S6(71) S10(3) S12(2) O7(25) O7(11) O7(13) O7(17) O7(41) O7(71) O11(3) O8+(16) O8+(25) O8+(11) O8+(13) O8+(17) O8+(41) O8+(71) O10+(7) O12+(3) U3(7^4) U3(17^3) U3(23^2) U3(53^2) U3(101) U3(103) U3(131) U3(173) U3(179) U3(181) U3(199) U3(211) U3(229) U3(239) U3(283) U3(307) U3(311) U3(331) U3(353) U3(367) U3(397) U3(421) U3(463) U3(467) U3(509) U3(523) U3(547) U3(569) U3(593) U3(599) U3(631) U3(641) U3(647) U3(673) U3(709) U3(743) U3(751) U3(773) U3(787) U3(821) U3(827) U3(853) U3(883) U3(937) U3(983) U3(997) U3(1009) U3(1033) U3(1087) U3(1103) U3(1163) U3(1193) U3(1229) U3(1409) U3(1487) U3(1543) U3(1553) U3(1601) U3(1637) U3(1723) U3(1753) U3(1777) U3(1783) U3(1823) U3(1831) U3(1907) U3(1913) U3(1999) U3(2039) U3(2207) U3(2213) U3(2273) U3(2333) U3(2417) U3(2459) U3(2663) U3(2693) U3(2741) U3(2777) U3(3259) U3(3373) U3(3463) U3(3467) U3(3469) U3(3931) U3(3947) U3(3967) U3(4253) U3(4357) U3(4363) U3(4783) U3(4993) U3(5051) U3(5077) U3(5153) U3(5189) U3(5323) U3(5441) U3(5483) U3(5507) U3(5987) U3(6113) U3(6547) U3(6737) U3(6823) U3(6983) U3(6997) U3(7013) U3(7507) U3(7607) U3(9403) U3(9587) U4(2^7) U4(27) U4(5^3) U4(11^2) U4(31) U4(37) U4(59) U4(61) U4(67) U4(97) U4(107) U4(113) U4(127) U4(137) U4(149) U4(167) U5(8) U5(25) U5(19) U6(9) U6(7) U8(3) U9(2) O10-(4) O10-(5) O12-(2) G2(81) G2(5^3) G2(49) G2(29) G2(37) G2(43) G2(47) G2(59) G2(67) G2(79) G2(83) G2(89) G2(113) G2(157) G2(313) F4(4) F4(5) E6(2) 3D4(19) 2E6(2) 2F4(8) 

#  Groups with prime spectrum of size 9 (828 groups) :
# F3+ A23 A24 A25 A26 A27 A28 L2(2^18) L2(3^15) L2(5^10) L2(7^10) L2(19^6) L2(53^5) L2(59^4) L2(61^3) L2(79^4) L2(103^3) L2(107^3) L2(109^3) L2(137^3) L2(149^3) L2(197^3) L2(227^3) L2(233^3) L2(251^3) L2(257^3) L2(307^2) L2(419^2) L2(421^2) L2(449^3) L2(499^3) L2(577^3) L2(599^2) L2(607^3) L2(701^2) L2(727^2) L2(743^2) L2(811^2) L2(827^2) L2(829^2) L2(857^2) L2(859^2) L2(919^2) L2(967^2) L2(1013^2) L2(1021^2) L2(1033^2) L2(1061^2) L2(1087^2) L2(1109^2) L2(1223^2) L2(1277^2) L2(1291^2) L2(1303^2) L2(1321^2) L2(1327^2) L2(1373^2) L2(1409^2) L2(1433^2) L2(1481^2) L2(1487^2) L2(1549^2) L2(1553^2) L2(1567^2) L2(1583^2) L2(1609^2) L2(1613^2) L2(1627^2) L2(1637^2) L2(1699^2) L2(1723^2) L2(1777^2) L2(1787^2) L2(1789^2) L2(1823^2) L2(1861^2) L2(1913^2) L2(1979^2) L2(2089^2) L2(2111^2) L2(2143^2) L2(2153^2) L2(2203^2) L2(2213^2) L2(2267^2) L2(2293^2) L2(2297^2) L2(2311^2) L2(2417^2) L2(2441^2) L2(2503^2) L2(2531^2) L2(2543^2) L2(2579^2) L2(2767^2) L2(2777^2) L2(2851^2) L2(2903^2) L2(2917^2) L2(2953^2) L2(2971^2) L2(3079^2) L2(3083^2) L2(3203^2) L2(3221^2) L2(3251^2) L2(3301^2) L2(3307^2) L2(3343^2) L2(3361^2) L2(3389^2) L2(3463^2) L2(3617^2) L2(3727^2) L2(3907^2) L2(3911^2) L2(4157^2) L2(4219^2) L2(4261^2) L2(4283^2) L2(4297^2) L2(4337^2) L2(4363^2) L2(4391^2) L2(4493^2) L2(4513^2) L2(4643^2) L2(4673^2) L2(4679^2) L2(4733^2) L2(4751^2) L2(4783^2) L2(4787^2) L2(4793^2) L2(4937^2) L2(4943^2) L2(4967^2) L2(5023^2) L2(5087^2) L2(5107^2) L2(5113^2) L2(5227^2) L2(5323^2) L2(5347^2) L2(5477^2) L2(5507^2) L2(5557^2) L2(5581^2) L2(5743^2) L2(5843^2) L2(5861^2) L2(5869^2) L2(6037^2) L2(6043^2) L2(6067^2) L2(6151^2) L2(6173^2) L2(6217^2) L2(6263^2) L2(6311^2) L2(6337^2) L2(6353^2) L2(6451^2) L2(6521^2) L2(6569^2) L2(6661^2) L2(6703^2) L2(6779^2) L2(6827^2) L2(6977^2) L2(6983^2) L2(7079^2) L2(7187^2) L2(7477^2) L2(7643^2) L2(7649^2) L2(7687^2) L2(8011^2) L2(8039^2) L2(8191^2) L2(8221^2) L2(8297^2) L2(8387^2) L2(8443^2) L2(8521^2) L2(8573^2) L2(8597^2) L2(8707^2) L2(8783^2) L2(8863^2) L2(8999^2) L2(9209^2) L2(9479^2) L2(9839^2) L2(9949^2) L3(2^10) L3(3^6) L3(5^5) L3(7^4) L3(23^2) L3(29^2) L3(31^2) L3(53^2) L3(59^2) L3(79^2) L3(97^2) L3(127^2) L3(211) L3(373) L3(461) L3(809) L3(811) L3(821) L3(947) L3(991) L3(1031) L3(1033) L3(1049) L3(1069) L3(1103) L3(1109) L3(1129) L3(1259) L3(1283) L3(1291) L3(1301) L3(1303) L3(1327) L3(1381) L3(1493) L3(1571) L3(1637) L3(1693) L3(1699) L3(1759) L3(1789) L3(1823) L3(1831) L3(1987) L3(2039) L3(2053) L3(2081) L3(2113) L3(2131) L3(2267) L3(2281) L3(2293) L3(2297) L3(2311) L3(2347) L3(2389) L3(2459) L3(2473) L3(2521) L3(2557) L3(2591) L3(2683) L3(2699) L3(2713) L3(2801) L3(2843) L3(2857) L3(2927) L3(2971) L3(3001) L3(3019) L3(3037) L3(3109) L3(3203) L3(3257) L3(3319) L3(3347) L3(3373) L3(3461) L3(3467) L3(3527) L3(3581) L3(3607) L3(3623) L3(3673) L3(3701) L3(3779) L3(3847) L3(4133) L3(4219) L3(4283) L3(4481) L3(4621) L3(4651) L3(4783) L3(4793) L3(4903) L3(4943) L3(5051) L3(5101) L3(5261) L3(5431) L3(5483) L3(5581) L3(5743) L3(5779) L3(5801) L3(5807) L3(5827) L3(5861) L3(5869) L3(5879) L3(5927) L3(6113) L3(6133) L3(6229) L3(6277) L3(6427) L3(6571) L3(6607) L3(6737) L3(6803) L3(6829) L3(6907) L3(6961) L3(7121) L3(7159) L3(7283) L3(7349) L3(7393) L3(7499) L3(7529) L3(7559) L3(7687) L3(7727) L3(8039) L3(8101) L3(8111) L3(8209) L3(8291) L3(8389) L3(8563) L3(8713) L3(8747) L3(8951) L3(9001) L3(9007) L3(9091) L3(9103) L3(9227) L3(9649) L3(9677) L4(64) L4(2^7) L4(81) L4(5^3) L4(11^2) L4(19^2) L4(47) L4(67) L4(107) L4(109) L4(113) L4(139) L4(151) L4(157) L4(163) L4(179) L4(197) L4(227) L4(239) L4(251) L4(283) L4(313) L4(457) L4(479) L4(577) L4(607) L4(719) L5(27) L6(8) L6(9) L6(11) L6(19) L7(7) L9(3) L10(2) S4(2^9) S4(5^5) S4(7^5) S4(19^3) S4(59^2) S4(79^2) S4(307) S4(419) S4(421) S4(599) S4(701) S4(727) S4(743) S4(811) S4(827) S4(829) S4(857) S4(859) S4(919) S4(967) S4(1013) S4(1021) S4(1033) S4(1061) S4(1087) S4(1109) S4(1223) S4(1277) S4(1291) S4(1303) S4(1321) S4(1327) S4(1373) S4(1409) S4(1433) S4(1481) S4(1487) S4(1549) S4(1553) S4(1567) S4(1583) S4(1609) S4(1613) S4(1627) S4(1637) S4(1699) S4(1723) S4(1777) S4(1787) S4(1789) S4(1823) S4(1861) S4(1913) S4(1979) S4(2089) S4(2111) S4(2143) S4(2153) S4(2203) S4(2213) S4(2267) S4(2293) S4(2297) S4(2311) S4(2417) S4(2441) S4(2503) S4(2531) S4(2543) S4(2579) S4(2767) S4(2777) S4(2851) S4(2903) S4(2917) S4(2953) S4(2971) S4(3079) S4(3083) S4(3203) S4(3221) S4(3251) S4(3301) S4(3307) S4(3343) S4(3361) S4(3389) S4(3463) S4(3617) S4(3727) S4(3907) S4(3911) S4(4157) S4(4219) S4(4261) S4(4283) S4(4297) S4(4337) S4(4363) S4(4391) S4(4493) S4(4513) S4(4643) S4(4673) S4(4679) S4(4733) S4(4751) S4(4783) S4(4787) S4(4793) S4(4937) S4(4943) S4(4967) S4(5023) S4(5087) S4(5107) S4(5113) S4(5227) S4(5323) S4(5347) S4(5477) S4(5507) S4(5557) S4(5581) S4(5743) S4(5843) S4(5861) S4(5869) S4(6037) S4(6043) S4(6067) S4(6151) S4(6173) S4(6217) S4(6263) S4(6311) S4(6337) S4(6353) S4(6451) S4(6521) S4(6569) S4(6661) S4(6703) S4(6779) S4(6827) S4(6977) S4(6983) S4(7079) S4(7187) S4(7477) S4(7643) S4(7649) S4(7687) S4(8011) S4(8039) S4(8191) S4(8221) S4(8297) S4(8387) S4(8443) S4(8521) S4(8573) S4(8597) S4(8707) S4(8783) S4(8863) S4(8999) S4(9209) S4(9479) S4(9839) S4(9949) S6(32) S6(27) S6(49) S6(23) S6(29) S6(31) S6(53) S6(59) S6(79) S6(97) S6(127) S8(8) S8(9) S8(11) S8(19) S12(3) O7(27) O7(49) O7(23) O7(29) O7(31) O7(53) O7(59) O7(79) O7(97) O7(127) O9(9) O9(11) O9(19) O13(3) O8+(32) O8+(27) O8+(49) O8+(23) O8+(29) O8+(31) O8+(53) O8+(59) O8+(79) O8+(97) O8+(127) O10+(4) O10+(5) O14+(2) U3(2^10) U3(3^8) U3(5^5) U3(13^3) U3(29^2) U3(41^2) U3(47^2) U3(73^2) U3(373) U3(409) U3(419) U3(439) U3(491) U3(521) U3(563) U3(571) U3(619) U3(677) U3(719) U3(739) U3(857) U3(881) U3(929) U3(941) U3(953) U3(1031) U3(1039) U3(1051) U3(1063) U3(1069) U3(1109) U3(1129) U3(1277) U3(1297) U3(1301) U3(1319) U3(1327) U3(1361) U3(1399) U3(1433) U3(1481) U3(1483) U3(1489) U3(1499) U3(1571) U3(1583) U3(1759) U3(1871) U3(1879) U3(1889) U3(1951) U3(2083) U3(2099) U3(2203) U3(2267) U3(2269) U3(2309) U3(2339) U3(2341) U3(2383) U3(2411) U3(2437) U3(2579) U3(2609) U3(2687) U3(2719) U3(2833) U3(2843) U3(2887) U3(2909) U3(2927) U3(2953) U3(2957) U3(3001) U3(3011) U3(3079) U3(3083) U3(3121) U3(3137) U3(3307) U3(3323) U3(3343) U3(3389) U3(3449) U3(3491) U3(3527) U3(3529) U3(3673) U3(3851) U3(3853) U3(3917) U3(4007) U3(4013) U3(4049) U3(4073) U3(4177) U3(4231) U3(4243) U3(4271) U3(4297) U3(4597) U3(4621) U3(4679) U3(4723) U3(4751) U3(4789) U3(4903) U3(4951) U3(4967) U3(4973) U3(4987) U3(5113) U3(5119) U3(5347) U3(5407) U3(5413) U3(5419) U3(5557) U3(5657) U3(5683) U3(5693) U3(5737) U3(5827) U3(5879) U3(6287) U3(6469) U3(6473) U3(6779) U3(6803) U3(6967) U3(7057) U3(7103) U3(7207) U3(7213) U3(7529) U3(7583) U3(7603) U3(7681) U3(7723) U3(7759) U3(7883) U3(7949) U3(7993) U3(8069) U3(8111) U3(8287) U3(8297) U3(8461) U3(8537) U3(8641) U3(8707) U3(8831) U3(8837) U3(8999) U3(9103) U3(9187) U3(9209) U3(9479) U3(9551) U3(9649) U3(9679) U3(9733) U3(9887) U3(9923) U3(9949) U4(64) U4(3^5) U4(19^2) U4(43) U4(47) U4(73) U4(83) U4(89) U4(101) U4(109) U4(131) U4(197) U4(223) U4(227) U4(239) U4(241) U4(251) U4(257) U4(263) U4(269) U4(277) U4(431) U4(607) U4(809) U5(32) U5(49) U5(13) U5(53) U6(8) U6(19) U7(4) U7(5) U10(2) O8-(8) O8-(9) O8-(11) O8-(19) O10-(7) O12-(3) O14-(2) G2(64) G2(3^5) G2(19^2) G2(61) G2(103) G2(107) G2(109) G2(137) G2(149) G2(197) G2(227) G2(233) G2(251) G2(257) G2(449) G2(499) G2(577) G2(607) F4(7) E6(3) 3D4(16) 3D4(11) 3D4(23) 3D4(53) 3D4(73) Sz(2^15) 

#  Groups with prime spectrum of size 10 (641 groups) :
# J4 A29 A30 L2(2^24) L2(11^6) L2(43^4) L2(137^4) L2(179^3) L2(181^3) L2(229^3) L2(239^3) L2(239^4) L2(263^3) L2(269^3) L2(277^3) L2(283^3) L2(307^3) L2(311^3) L2(331^3) L2(347^3) L2(353^3) L2(367^3) L2(397^3) L2(431^3) L2(463^2) L2(463^3) L2(509^3) L2(523^3) L2(547^3) L2(569^3) L2(593^3) L2(631^3) L2(647^3) L2(653^3) L2(659^2) L2(787^3) L2(823^3) L2(853^2) L2(853^3) L2(877^3) L2(911^2) L2(983^3) L2(1009^3) L2(1123^2) L2(1153^3) L2(1301^2) L2(1367^3) L2(1427^2) L2(1429^2) L2(1483^2) L2(1553^3) L2(1607^2) L2(1663^3) L2(1721^2) L2(1747^2) L2(1783^3) L2(1877^2) L2(1931^2) L2(2129^2) L2(2153^3) L2(2309^2) L2(2333^2) L2(2393^2) L2(2437^2) L2(2551^2) L2(2621^2) L2(2633^2) L2(2707^2) L2(2801^2) L2(2843^2) L2(2861^2) L2(2939^2) L2(2969^2) L2(3011^2) L2(3319^2) L2(3323^2) L2(3359^2) L2(3373^2) L2(3557^2) L2(3583^2) L2(3659^2) L2(3671^2) L2(3761^2) L2(3769^2) L2(3793^2) L2(3863^2) L2(3947^2) L2(4159^2) L2(4229^2) L2(4327^2) L2(4423^2) L2(4483^2) L2(4649^2) L2(4789^2) L2(4817^2) L2(4831^2) L2(4957^2) L2(4969^2) L2(4987^2) L2(5153^2) L2(5171^2) L2(5413^2) L2(5479^2) L2(5503^2) L2(5623^2) L2(5701^2) L2(5813^2) L2(5867^2) L2(5923^2) L2(6007^2) L2(6073^2) L2(6133^2) L2(6163^2) L2(6247^2) L2(6257^2) L2(6269^2) L2(6277^2) L2(6343^2) L2(6481^2) L2(6551^2) L2(6553^2) L2(6571^2) L2(6691^2) L2(6863^2) L2(6917^2) L2(6959^2) L2(7103^2) L2(7127^2) L2(7193^2) L2(7207^2) L2(7297^2) L2(7307^2) L2(7549^2) L2(7603^2) L2(7669^2) L2(7699^2) L2(7883^2) L2(7951^2) L2(7963^2) L2(8093^2) L2(8117^2) L2(8171^2) L2(8237^2) L2(8293^2) L2(8317^2) L2(8363^2) L2(8419^2) L2(8537^2) L2(8663^2) L2(8669^2) L2(8689^2) L2(8807^2) L2(8887^2) L2(9011^2) L2(9133^2) L2(9221^2) L2(9587^2) L2(9811^2) L2(9833^2) L2(9871^2) L2(9901^2) L3(2^14) L3(3^8) L3(3^9) L3(5^6) L3(37^2) L3(43^2) L3(61^2) L3(67^2) L3(73^2) L3(89^2) L3(113^2) L3(571) L3(919) L3(1231) L3(1429) L3(1451) L3(1511) L3(1597) L3(1721) L3(1871) L3(1913) L3(1979) L3(2243) L3(2393) L3(2551) L3(2609) L3(2671) L3(2837) L3(2851) L3(2939) L3(3089) L3(3359) L3(3739) L3(3761) L3(3769) L3(3877) L3(3917) L3(4027) L3(4073) L3(4111) L3(4271) L3(4289) L3(4339) L3(4423) L3(4561) L3(4637) L3(4643) L3(4657) L3(4663) L3(4729) L3(4799) L3(4861) L3(4909) L3(4951) L3(4969) L3(5021) L3(5099) L3(5279) L3(5381) L3(5419) L3(5441) L3(5479) L3(5639) L3(5659) L3(5749) L3(5791) L3(6067) L3(6091) L3(6323) L3(6353) L3(6421) L3(6449) L3(6701) L3(6841) L3(6863) L3(6871) L3(6899) L3(6997) L3(7177) L3(7621) L3(7907) L3(8009) L3(8147) L3(8171) L3(8243) L3(8297) L3(8429) L3(8861) L3(9181) L3(9241) L3(9421) L3(9697) L3(9739) L3(9851) L3(9883) L4(7^3) L4(83) L4(137) L4(149) L4(229) L4(233) L4(263) L4(269) L4(277) L4(281) L4(311) L4(331) L4(337) L4(353) L4(359) L4(431) L4(439) L4(491) L4(499) L4(509) L4(523) L4(557) L4(593) L4(601) L4(643) L4(647) L4(691) L4(733) L4(787) L4(971) L4(983) L4(1153) L4(1237) L4(1279) L4(1471) L4(1601) L4(1621) L4(1733) L4(1783) L4(1999) L4(2017) L4(2689) L4(2749) L5(16) L5(32) L5(25) L5(49) L5(71) L7(4) L8(7) L10(3) S4(2^12) S4(11^3) S4(43^2) S4(137^2) S4(239^2) S4(463) S4(659) S4(853) S4(911) S4(1123) S4(1301) S4(1427) S4(1429) S4(1483) S4(1607) S4(1721) S4(1747) S4(1877) S4(1931) S4(2129) S4(2309) S4(2333) S4(2393) S4(2437) S4(2551) S4(2621) S4(2633) S4(2707) S4(2801) S4(2843) S4(2861) S4(2939) S4(2969) S4(3011) S4(3319) S4(3323) S4(3359) S4(3373) S4(3557) S4(3583) S4(3659) S4(3671) S4(3761) S4(3769) S4(3793) S4(3863) S4(3947) S4(4159) S4(4229) S4(4327) S4(4423) S4(4483) S4(4649) S4(4789) S4(4817) S4(4831) S4(4957) S4(4969) S4(4987) S4(5153) S4(5171) S4(5413) S4(5479) S4(5503) S4(5623) S4(5701) S4(5813) S4(5867) S4(5923) S4(6007) S4(6073) S4(6133) S4(6163) S4(6247) S4(6257) S4(6269) S4(6277) S4(6343) S4(6481) S4(6551) S4(6553) S4(6571) S4(6691) S4(6863) S4(6917) S4(6959) S4(7103) S4(7127) S4(7193) S4(7207) S4(7297) S4(7307) S4(7549) S4(7603) S4(7669) S4(7699) S4(7883) S4(7951) S4(7963) S4(8093) S4(8117) S4(8171) S4(8237) S4(8293) S4(8317) S4(8363) S4(8419) S4(8537) S4(8663) S4(8669) S4(8689) S4(8807) S4(8887) S4(9011) S4(9133) S4(9221) S4(9587) S4(9811) S4(9833) S4(9871) S4(9901) S6(2^7) S6(81) S6(5^3) S6(37) S6(43) S6(61) S6(67) S6(73) S6(89) S6(113) S10(4) S10(5) S10(7) S14(2) O7(81) O7(5^3) O7(37) O7(43) O7(61) O7(67) O7(73) O7(89) O7(113) O11(5) O11(7) O8+(2^7) O8+(81) O8+(5^3) O8+(37) O8+(43) O8+(61) O8+(67) O8+(73) O8+(89) O8+(113) O10+(11) O12+(4) O12+(5) O12+(7) O14+(3) O16+(2) U3(23^3) U3(89^2) U3(97^2) U3(113^2) U3(829) U3(859) U3(1091) U3(1429) U3(1699) U3(1931) U3(1973) U3(1979) U3(2243) U3(2393) U3(2539) U3(2971) U3(3181) U3(3191) U3(3221) U3(3319) U3(3391) U3(3533) U3(3559) U3(3613) U3(3631) U3(3637) U3(3659) U3(3709) U3(4021) U3(4027) U3(4079) U3(4091) U3(4129) U3(4211) U3(4217) U3(4219) U3(4261) U3(4549) U3(4651) U3(4969) U3(5009) U3(5167) U3(5237) U3(5351) U3(5431) U3(5477) U3(5503) U3(5849) U3(5857) U3(5927) U3(6029) U3(6263) U3(6299) U3(6359) U3(6529) U3(6863) U3(6907) U3(6949) U3(6971) U3(7699) U3(7853) U3(7877) U3(7919) U3(8011) U3(8039) U3(8093) U3(8221) U3(8273) U3(8291) U3(8429) U3(8447) U3(8527) U3(8623) U3(8821) U3(8861) U3(8863) U3(8867) U3(8893) U3(8951) U3(8971) U3(9631) U3(9721) U3(9833) U3(9929) U4(103) U4(157) U4(179) U4(211) U4(229) U4(233) U4(283) U4(293) U4(311) U4(313) U4(331) U4(401) U4(499) U4(509) U4(577) U4(709) U4(757) U4(1097) U4(1153) U4(1193) U4(1229) U4(1283) U4(1601) U4(1697) U4(1999) U4(2039) U4(3217) U4(3469) U5(17) U5(23) U5(29) U5(41) U5(79) U6(25) U6(13) U7(7) U8(4) U8(5) U9(3) U11(2) O10-(9) O14-(3) G2(2^8) G2(11^2) G2(179) G2(181) G2(229) G2(239) G2(263) G2(269) G2(277) G2(283) G2(307) G2(311) G2(331) G2(347) G2(353) G2(367) G2(397) G2(431) G2(463) G2(509) G2(523) G2(547) G2(569) G2(593) G2(631) G2(647) G2(653) G2(787) G2(823) G2(853) G2(877) G2(983) G2(1009) G2(1153) G2(1367) G2(1553) G2(1663) G2(1783) G2(2153) F4(9) 3D4(32) 3D4(41) 3D4(47) 2E6(3) 2E6(5) 2F4(32) 

#  Groups with prime spectrum of size 11 (398 groups) :
# B A31 A32 A33 A34 A35 A36 L2(23^6) L2(41^6) L2(53^6) L2(211^3) L2(439^3) L2(491^3) L2(521^3) L2(619^3) L2(719^3) L2(809^3) L2(821^3) L2(929^3) L2(941^3) L2(953^3) L2(997^3) L2(1033^3) L2(1087^3) L2(1103^3) L2(1283^3) L2(1301^3) L2(1399^3) L2(1543^3) L2(1597^2) L2(1601^3) L2(1637^3) L2(1831^3) L2(1999^3) L2(2039^3) L2(2207^3) L2(2269^3) L2(2459^3) L2(2927^3) L2(3323^3) L2(3373^3) L2(3541^2) L2(3623^3) L2(3739^2) L2(4027^2) L2(4231^3) L2(4253^3) L2(4621^3) L2(4783^3) L2(5051^3) L2(5077^3) L2(5641^2) L2(6089^2) L2(6287^3) L2(6323^2) L2(6397^2) L2(6469^2) L2(7253^2) L2(7639^2) L2(7789^2) L2(7867^2) L2(8101^3) L2(8161^2) L2(8377^2) L2(8581^2) L2(8861^2) L2(9403^3) L2(9431^2) L2(9463^2) L2(9941^2) L3(2^12) L3(3^10) L3(11^4) L3(19^4) L3(47^2) L3(83^2) L3(103^2) L3(107^2) L3(109^2) L3(137^2) L3(149^2) L3(157^2) L3(197^2) L3(227^2) L3(239^2) L3(251^2) L3(257^2) L3(313^2) L3(607^2) L3(3229) L3(3389) L3(3539) L3(3541) L3(3571) L3(4523) L3(4691) L3(5711) L3(5821) L3(6581) L3(6659) L3(6733) L3(6763) L3(6971) L3(7151) L3(7193) L3(7639) L3(7879) L3(8219) L3(8329) L3(8647) L3(8779) L3(8941) L3(9109) L3(9281) L3(9419) L3(9491) L3(9929) L4(3^6) L4(31^2) L4(191) L4(211) L4(307) L4(809) L4(829) L4(967) L4(1049) L4(1291) L4(1453) L4(1543) L4(1553) L4(1567) L4(1571) L4(1693) L4(1759) L4(2039) L4(2207) L4(2311) L4(2903) L4(3253) L4(3313) L4(4219) L4(4481) L4(4493) L4(4933) L4(6037) L4(6911) L4(7703) L4(8389) L4(9067) L5(37) L5(53) L5(59) L5(89) L6(16) L6(32) L6(27) L6(25) L6(71) L7(8) L7(9) L8(4) L11(2) S4(23^3) S4(41^3) S4(53^3) S4(1597) S4(3541) S4(3739) S4(4027) S4(5641) S4(6089) S4(6323) S4(6397) S4(6469) S4(7253) S4(7639) S4(7789) S4(7867) S4(8161) S4(8377) S4(8581) S4(8861) S4(9431) S4(9463) S4(9941) S6(64) S6(3^5) S6(11^2) S6(19^2) S6(47) S6(83) S6(103) S6(107) S6(109) S6(137) S6(149) S6(157) S6(197) S6(227) S6(239) S6(251) S6(257) S6(313) S6(607) S8(27) S8(31) S12(4) S12(5) S14(3) S16(2) O7(3^5) O7(11^2) O7(19^2) O7(47) O7(83) O7(103) O7(107) O7(109) O7(137) O7(149) O7(157) O7(197) O7(227) O7(239) O7(251) O7(257) O7(313) O7(607) O9(27) O9(31) O13(5) O15(3) O8+(64) O8+(3^5) O8+(11^2) O8+(19^2) O8+(47) O8+(83) O8+(103) O8+(107) O8+(109) O8+(137) O8+(149) O8+(157) O8+(197) O8+(227) O8+(239) O8+(251) O8+(257) O8+(313) O8+(607) O10+(8) O10+(9) O10+(19) O16+(3) U3(2617) U3(2729) U3(2789) U3(3769) U3(5059) U3(5197) U3(5281) U3(5591) U3(5659) U3(6491) U3(6733) U3(7309) U3(7549) U3(7669) U3(8179) U3(8363) U3(8501) U3(8669) U3(8737) U3(9109) U3(9239) U3(9619) U3(9791) U4(173) U4(307) U4(353) U4(419) U4(421) U4(439) U4(467) U4(491) U4(523) U4(593) U4(599) U4(647) U4(719) U4(743) U4(787) U4(827) U4(863) U4(983) U4(1033) U4(1319) U4(1409) U4(1481) U4(1543) U4(1553) U4(1571) U4(1637) U4(1723) U4(1759) U4(1777) U4(1783) U4(1879) U4(1889) U4(1913) U4(2099) U4(2153) U4(2207) U4(2213) U4(2417) U4(2909) U4(3079) U4(3389) U4(3449) U4(4357) U4(4373) U4(4783) U4(7607) U4(9479) U5(27) U5(5^3) U5(137) U6(32) U6(49) U6(17) U6(41) U6(53) U7(8) U8(7) U9(5) U10(3) U12(2) O8-(27) O8-(31) O10-(8) O10-(19) O12-(4) O12-(5) O16-(2) G2(23^2) G2(41^2) G2(53^2) G2(211) G2(439) G2(491) G2(521) G2(619) G2(719) G2(809) G2(821) G2(929) G2(941) G2(953) G2(997) G2(1033) G2(1087) G2(1103) G2(1283) G2(1301) G2(1399) G2(1543) G2(1601) G2(1637) G2(1831) G2(1999) G2(2039) G2(2207) G2(2269) G2(2459) G2(2927) G2(3323) G2(3373) G2(3623) G2(4231) G2(4253) G2(4621) G2(4783) G2(5051) G2(5077) G2(6287) G2(8101) G2(9403) F4(8) F4(11) F4(19) 3D4(81) 3D4(49) 3D4(29) 3D4(89) 3D4(97) 3D4(113) 2E6(4) 

#  Groups with prime spectrum of size 12 (309 groups) :
# A37 A38 A39 A40 L2(2^30) L2(5^15) L2(7^12) L2(29^6) L2(73^6) L2(373^3) L2(571^3) L2(829^3) L2(1031^3) L2(1069^3) L2(1109^3) L2(1129^3) L2(1327^3) L2(1429^3) L2(1571^3) L2(1759^3) L2(1823^3) L2(1871^3) L2(1913^3) L2(2267^3) L2(2383^4) L2(2843^3) L2(3001^3) L2(3319^3) L2(3467^3) L2(3527^3) L2(3631^3) L2(3673^3) L2(4217^2) L2(4219^3) L2(4271^3) L2(4723^3) L2(4903^3) L2(5419^3) L2(5431^3) L2(5441^3) L2(5483^3) L2(5827^3) L2(5879^3) L2(6113^3) L2(6737^3) L2(6803^3) L2(6997^3) L2(7529^3) L2(8111^3) L2(9043^2) L2(9103^3) L2(9649^3) L3(43^3) L3(179^2) L3(229^2) L3(233^2) L3(263^2) L3(269^2) L3(277^2) L3(283^2) L3(311^2) L3(331^2) L3(431^2) L3(499^2) L3(509^2) L3(577^2) L3(6269) L3(9811) L4(5^5) L4(59^2) L4(79^2) L4(463) L4(811) L4(853) L4(1033) L4(1087) L4(1109) L4(1123) L4(1283) L4(1301) L4(1303) L4(1327) L4(1429) L4(1451) L4(1493) L4(1637) L4(1699) L4(1789) L4(1979) L4(2153) L4(2267) L4(2293) L4(2297) L4(2503) L4(2851) L4(2971) L4(3319) L4(3323) L4(3793) L4(4283) L4(4327) L4(4783) L4(4793) L4(4937) L4(4943) L4(5099) L4(5581) L4(5743) L4(5807) L4(5861) L4(5869) L4(6571) L4(6703) L4(7187) L4(7687) L4(8039) L4(8573) L4(9739) L5(81) L5(197) L6(49) L6(53) L9(7) L11(3) L12(2) S4(2^15) S4(7^6) S4(29^3) S4(73^3) S4(2383^2) S4(4217) S4(9043) S6(179) S6(229) S6(233) S6(263) S6(269) S6(277) S6(283) S6(311) S6(331) S6(431) S6(499) S6(509) S6(577) S8(59) S8(79) S10(9) S12(7) O7(179) O7(229) O7(233) O7(263) O7(269) O7(277) O7(283) O7(311) O7(331) O7(431) O7(499) O7(509) O7(577) O9(59) O9(79) O11(9) O13(7) O8+(179) O8+(229) O8+(233) O8+(263) O8+(269) O8+(277) O8+(283) O8+(311) O8+(331) O8+(431) O8+(499) O8+(509) O8+(577) O12+(9) O18+(2) U3(59^3) U3(467^2) U3(8161) U3(8779) U3(9461) U4(5^5) U4(463) U4(563) U4(853) U4(857) U4(859) U4(1087) U4(1109) U4(1277) U4(1297) U4(1301) U4(1327) U4(1429) U4(1483) U4(1487) U4(1583) U4(1823) U4(1979) U4(2203) U4(2267) U4(2309) U4(2333) U4(2383) U4(2437) U4(2579) U4(2777) U4(2917) U4(2953) U4(3011) U4(3083) U4(3137) U4(3221) U4(3307) U4(3343) U4(3373) U4(3463) U4(3947) U4(4007) U4(4219) U4(4297) U4(4363) U4(4679) U4(4751) U4(4789) U4(4967) U4(5119) U4(5153) U4(5323) U4(5347) U4(5507) U4(5557) U4(6529) U4(6779) U4(6983) U4(8297) U4(8707) U4(8999) U4(9209) U4(9587) U4(9887) U4(9949) U5(64) U5(107) U5(239) U6(27) U6(23) U6(29) U6(79) U9(4) U13(2) O8-(59) O8-(79) O12-(7) O18-(2) G2(2^10) G2(5^5) G2(7^4) G2(29^2) G2(73^2) G2(373) G2(571) G2(829) G2(1031) G2(1069) G2(1109) G2(1129) G2(1327) G2(1429) G2(1571) G2(1759) G2(1823) G2(1871) G2(1913) G2(2267) G2(2843) G2(3001) G2(3319) G2(3467) G2(3527) G2(3631) G2(3673) G2(4219) G2(4271) G2(4723) G2(4903) G2(5419) G2(5431) G2(5441) G2(5483) G2(5827) G2(5879) G2(6113) G2(6737) G2(6803) G2(6997) G2(7529) G2(8111) G2(9103) G2(9649) E6(4) E6(5) E6(7) E7(2) 

#  Groups with prime spectrum of size 13 (238 groups) :
# A41 A42 L2(3^24) L2(47^6) L2(89^6) L2(97^6) L2(113^6) L2(1699^3) L2(1979^3) L2(2243^3) L2(2393^3) L2(2609^3) L2(2971^3) L2(3389^3) L2(3917^3) L2(4027^3) L2(4073^3) L2(4651^3) L2(4951^3) L2(4969^3) L2(5927^3) L2(6863^3) L2(6907^3) L2(6971^3) L2(8039^3) L2(8291^3) L2(8297^3) L2(8429^3) L2(8861^3) L2(8951^3) L2(9721^3) L3(211^2) L3(307^2) L3(353^2) L3(439^2) L3(491^2) L3(523^2) L3(593^2) L3(647^2) L3(719^2) L3(787^2) L3(809^2) L3(983^2) L3(1153^2) L3(1553^2) L3(1601^2) L3(1783^2) L3(1999^2) L3(2039^2) L4(43^2) L4(919) L4(1721) L4(1823) L4(1913) L4(2393) L4(2551) L4(2801) L4(2843) L4(2939) L4(3203) L4(3359) L4(3373) L4(3389) L4(3739) L4(3761) L4(3769) L4(4423) L4(4643) L4(4969) L4(5479) L4(6067) L4(6133) L4(6277) L4(6659) L4(6863) L4(8171) L4(8297) L5(64) L5(5^3) L5(19^2) L5(149) L5(163) L6(81) L6(37) L6(59) L6(89) L8(8) L8(9) L9(4) L12(3) L13(2) S4(3^12) S4(47^3) S4(89^3) S4(97^3) S4(113^3) S6(211) S6(307) S6(353) S6(439) S6(491) S6(523) S6(593) S6(647) S6(719) S6(787) S6(809) S6(983) S6(1153) S6(1553) S6(1601) S6(1783) S6(1999) S6(2039) S8(43) S10(8) S10(19) S12(9) S16(3) S18(2) O7(211) O7(307) O7(353) O7(439) O7(491) O7(523) O7(593) O7(647) O7(719) O7(787) O7(809) O7(983) O7(1153) O7(1553) O7(1601) O7(1783) O7(1999) O7(2039) O9(43) O11(19) O13(9) O17(3) O8+(211) O8+(307) O8+(353) O8+(439) O8+(491) O8+(523) O8+(593) O8+(647) O8+(719) O8+(787) O8+(809) O8+(983) O8+(1153) O8+(1553) O8+(1601) O8+(1783) O8+(1999) O8+(2039) O10+(27) O12+(8) O12+(19) O14+(4) O20+(2) U3(421^2) U3(727^2) U3(1013^2) U3(1697^2) U4(829) U4(1433) U4(1699) U4(1931) U4(2393) U4(2843) U4(2971) U4(3319) U4(3323) U4(3659) U4(4261) U4(4969) U4(4987) U4(5113) U4(5413) U4(5477) U4(6263) U4(6469) U4(6863) U4(7103) U4(7207) U4(7603) U4(7699) U4(7883) U4(8011) U4(8039) U4(8093) U4(8221) U4(8537) U4(8863) U6(5^3) U8(8) U10(5) U11(3) U14(2) O8-(43) O12-(9) O14-(4) O14-(5) O16-(3) G2(3^8) G2(47^2) G2(89^2) G2(97^2) G2(113^2) G2(1699) G2(1979) G2(2243) G2(2393) G2(2609) G2(2971) G2(3389) G2(3917) G2(4027) G2(4073) G2(4651) G2(4951) G2(4969) G2(5927) G2(6863) G2(6907) G2(6971) G2(8039) G2(8291) G2(8297) G2(8429) G2(8861) G2(8951) G2(9721) 

#  Groups with prime spectrum of size 14 (119 groups) :
# A43 A44 A45 A46 L2(3373^4) L2(3769^3) L2(5659^3) L2(6733^3) L2(9929^3) L3(463^2) L3(853^2) L3(1033^2) L3(1283^2) L3(1301^2) L3(1429^2) L3(1543^2) L3(1571^2) L3(1637^2) L3(1759^2) L3(2153^2) L3(2207^2) L3(4219^2) L3(4783^2) L4(2^12) L4(137^2) L4(239^2) L4(1597) L4(3541) L4(4027) L4(6323) L4(6353) L4(7193) L4(8861) L5(307) L6(5^3) L6(149) L6(197) L10(4) L10(7) L14(2) S4(3373^2) S6(463) S6(853) S6(1033) S6(1283) S6(1301) S6(1429) S6(1543) S6(1571) S6(1637) S6(1759) S6(2153) S6(2207) S6(4219) S6(4783) S8(64) S8(137) S8(239) S20(2) O7(463) O7(853) O7(1033) O7(1283) O7(1301) O7(1429) O7(1543) O7(1571) O7(1637) O7(1759) O7(2153) O7(2207) O7(4219) O7(4783) O9(137) O9(239) O8+(463) O8+(853) O8+(1033) O8+(1283) O8+(1301) O8+(1429) O8+(1543) O8+(1571) O8+(1637) O8+(1759) O8+(2153) O8+(2207) O8+(4219) O8+(4783) O14+(7) O18+(3) U4(23^3) U4(3769) U4(4027) U4(5503) U4(7549) U4(7669) U4(8363) U4(8669) U4(8861) U4(9833) U5(277) U6(64) U6(137) U6(239) U10(4) U12(3) U15(2) O8-(64) O8-(137) O8-(239) O10-(27) O14-(7) O20-(2) G2(3769) G2(5659) G2(6733) G2(9929) E7(3) 

#  Groups with prime spectrum of size 15 (87 groups) :
# M A47 A48 A49 A50 A51 A52 L2(8779^3) L2(9109^3) L3(5^10) L3(829^2) L3(1087^2) L3(1109^2) L3(1327^2) L3(1913^2) L3(1979^2) L3(2267^2) L3(3319^2) L3(3323^2) L3(3373^2) L3(3389^2) L4(6269) L4(7639) L4(9811) L6(64) L6(19^2) L7(16) L15(2) S6(5^5) S6(829) S6(1087) S6(1109) S6(1327) S6(1913) S6(1979) S6(2267) S6(3319) S6(3323) S6(3373) S6(3389) S12(8) S12(19) S14(4) O7(5^5) O7(829) O7(1087) O7(1109) O7(1327) O7(1913) O7(1979) O7(2267) O7(3319) O7(3323) O7(3373) O7(3389) O13(19) O8+(5^5) O8+(829) O8+(1087) O8+(1109) O8+(1327) O8+(1913) O8+(1979) O8+(2267) O8+(3319) O8+(3323) O8+(3373) O8+(3389) O14+(9) O16+(4) U3(3011^2) U3(4027^2) U4(4217) U4(8161) U5(599) U6(107) U7(27) U7(23) U16(2) O10-(79) O12-(8) O12-(19) O18-(3) O22-(2) G2(8779) G2(9109) E6(9) 

#  Groups with prime spectrum of size 16 (62 groups) :
# A53 A54 A55 A56 A57 A58 L3(1699^2) L3(1823^2) L3(2393^2) L3(2843^2) L3(2971^2) L3(4969^2) L3(6863^2) L3(8039^2) L3(8297^2) L5(3^6) L6(307) L7(49) L9(9) L16(2) S6(1699) S6(1823) S6(2393) S6(2843) S6(2971) S6(4969) S6(6863) S6(8039) S6(8297) S10(27) S14(7) S18(3) O7(1699) O7(1823) O7(2393) O7(2843) O7(2971) O7(4969) O7(6863) O7(8039) O7(8297) O11(27) O15(7) O19(3) O8+(1699) O8+(1823) O8+(2393) O8+(2843) O8+(2971) O8+(4969) O8+(6863) O8+(8039) O8+(8297) O10+(59) O12+(27) O16+(7) O20+(3) O22+(2) U5(523) U11(4) U11(5) E8(2) 

#  Groups with prime spectrum of size 17 (32 groups) :
# A59 A60 L3(3769^2) L3(4027^2) L3(8861^2) L7(59) L10(9) L11(4) S6(3769) S6(4027) S6(8861) S20(3) S22(2) O7(3769) O7(4027) O7(8861) O21(3) O8+(3769) O8+(4027) O8+(8861) O14+(8) O24+(2) U6(277) U8(27) U12(4) U12(5) O10-(64) O10-(137) O10-(239) O14-(8) O20-(3) 3D4(4027) 

#  Groups with prime spectrum of size 18 (12 groups) :
# A61 A62 A63 A64 A65 A66 L12(4) S24(2) O10+(64) U6(523) U7(5^3) O24-(2) 

#  Groups with prime spectrum of size 19 (18 groups) :
# A67 A68 A69 A70 L4(3373^2) L7(64) S8(3373) S14(8) O9(3373) O16+(8) O22+(3) O26+(2) U5(7103) O8-(3373) O22-(3) O26-(2) E7(4) E8(3) 

#  Groups with prime spectrum of size 20 (7 groups) :
# A71 A72 L8(59) L13(4) S26(2) O28+(2) U13(4) 

#  Groups with prime spectrum of size 21 (16 groups) :
# A73 A74 A75 A76 A77 A78 L2(4027^6) L5(2^12) L11(9) S4(4027^3) S10(64) S22(3) O23(3) O12+(64) O24+(3) G2(4027^2) 

#  Groups with prime spectrum of size 22 (15 groups) :
# A79 A80 A81 A82 L8(64) L12(9) L14(4) S16(8) S24(3) S28(2) O25(3) U14(4) O16-(8) O24-(3) O28-(2) 

#  Groups with prime spectrum of size 23 (8 groups) :
# A83 A84 A85 A86 A87 A88 O30+(2) O30-(2) 

#  Groups with prime spectrum of size 24 (12 groups) :
# A89 A90 A91 A92 A93 A94 A95 A96 L15(4) S30(2) O32+(2) U15(4) 

####

##  Printing the 3-primary simple groups with their spectra

piSizeSorted[1][1] = 3; # true                                           ## confirming n = 3
List( piSizeSorted[1][2], code -> [ NameByCode(code), PiByCode(code)] );

# [ [     "A5", [ 2, 3,  5 ] ], 
#   [     "A6", [ 2, 3,  5 ] ], 
#   [  "L2(8)", [ 2, 3,  7 ] ], 
#   [  "L2(7)", [ 2, 3,  7 ] ], 
#   [ "L2(17)", [ 2, 3, 17 ] ], 
#   [  "L3(3)", [ 2, 3, 13 ] ], 
#   [  "S4(3)", [ 2, 3,  5 ] ], 
#   [  "U3(3)", [ 2, 3,  7 ] ] ]

## Obs. These are ALL 3-primary groups ( not only those with max( pi(G) ) < 10000 ), see
##
## M. Herzog, On finite simple groups of order divisible by three primes only, Journal of Algebra, Volume 10, Issue 3, November 1968, Pages 383-388.
## https://doi.org/10.1016/0021-8693(68)90088-4

### END ###
###########
