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
## t = 1,...,18  encodes the following 18 families of FSGs
## 
##   t    Family      Parameters
## -----------------------------------
##   1    Sporadic    n = 1,...,26, p = *, k = *   ( * = any number, usually 0. Value ignored )
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
## In other words, we find all n-primary nonabelian FSGs for n >=3 
## with all prime divisors of their orders not exceeding 10000

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
  piSize := Size(Collected(Factors(OrderByCode(code))));        ## size of prime spectrum
  rcd := First( piSizeSortedNonAlt, r -> r[1] = piSize );
  AddSet( rcd[2], code );
od;

List( piSizeSortedNonAlt, r -> [r[1],Size(r[2])] );             ## numbers of n-primary NON-ALTERNATING groups for n = 3..24

# [ [  3,   6 ], [  4,  61 ], [ 5,  347 ], [ 6, 711 ], [  7, 593 ], [  8, 624 ], [  9, 822 ], [ 10, 639 ], [ 11, 392 ], 
#   [ 12, 305 ], [ 13, 236 ], [ 14, 115 ], [ 15, 81 ], [ 16,  56 ], [ 17,  30 ], [ 18,   6 ], [ 19,  14 ], [ 20,   5 ], 
#   [ 21,  10 ], [ 22,  11 ], [ 23,   2 ], [ 24,  4 ] ]

### Adding the codes of n-primary alternating groups ( up to n = 24 ) :

##  Obs. The number of n-primary alternating groups equals p{n+1} - p{n} where p{n} is the n-th prime

## The result of the following procedure is a list <piSizeSorted> of pairs [ size, codes_size ], where 
##    size        is one of possible sizes 3..24 of prime spectrum
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

## Case n = 24. Printing the groups from K_24 :

piSizeSorted[22][1] = 24; # true   ## confirming n = 24
List( piSizeSorted[22][2], NameByCode );
## [ "A89", "A90", "A91", "A92", "A93", "A94", "A95", "A96", "L15(4)", "S30(2)", "O32+(2)", "U15(4)" ]

## This justifies the last example in the paper.


## Case n = 3. Printing the 3-primary with their spectra

piSizeSorted[1][1] = 2; # true   ## confirming n = 3
List( piSizeSorted[1][2], code -> [ NameByCode(code), PiByCode(code)] );

# [ [     "A5", [ 2, 3,  5 ] ], 
#   [     "A6", [ 2, 3,  5 ] ], 
#   [  "L2(8)", [ 2, 3,  7 ] ], 
#   [  "L2(7)", [ 2, 3,  7 ] ], 
#   [ "L2(17)", [ 2, 3, 17 ] ], 
#   [  "L3(3)", [ 2, 3, 13 ] ], 
#   [  "S4(3)", [ 2, 3,  5 ] ], 
#   [  "U3(3)", [ 2, 3,  7 ] ] ]

## These are all 3-primary groups, see
##
## M. Herzog, On finite simple groups of order divisible by three primes only, Journal of Algebra, Volume 10, Issue 3, November 1968, Pages 383-388
## https://doi.org/10.1016/0021-8693(68)90088-4

### END ###
###########
