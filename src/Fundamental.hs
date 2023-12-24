module Bokowski.Fundamental where

import Data.List 

type MA =[[Integer]]            -- matrix
type OB =(Tu,Or)                -- oriented base
type OM1= [Int]                 -- rank1 oriented matroid
type OM2=[[Int]]                -- rank2 oriented matroid
type OM3=[(OM1,OM2)]            -- rank3 oriented matroid
type OM5=[([Int],OM2)]          -- rank5 matroid polytope
type Tu = [Int]                 -- tuple of elements
type Or =  Int                  -- orientation
type OF =[Int]->[Int]->Ordering -- order function, rank~2
type Ngon=[Int]                 -- hyperline,polytope,r=5


-- r -> n -> all r-tuples of [1..n]
tuples::Int->Int->[[Int]]       
tuples 0 n = [[]]
tuples r n = tuplesL r [1..n]
  
-- r -> list -> all r-tuples of list
tuplesL::Int->[Int]->[[Int]]  
tuplesL  r list@(x:xs)        
  | length list <  r = []
  | length list == r = [list] 
  | r == 1           = [[el]|el<-list]
  | otherwise = [[x]++el| el<-tuplesL (r-1) xs]
                 ++tuplesL r xs

norm::OB->OB 
norm (tu@(h:rest),s) = normPos (list,s*signum prod)
 where prod = product tu; list = map abs tu
       normPos::OB->OB
       normPos  (tuple@(h:rest),sign) 
        |rest == [] = ([h],sign)
        |h==minimum tuple=([h]++fst next,snd next)
        |odd (length rest) =normPos (rest++[h],-sign)
        |otherwise         =normPos (rest++[h], sign)
         where  next = normPos (rest,sign) 

--
preHypR2::[(Tu,Or)]->[[Int]]
preHypR2  chi = siIn (genSets chi) chi

-- prep. 2 h.d. -> chi -> prep. 3 of h.d.
siIn::[[Int]]->[(Tu,Or)]->[[Int]]
siIn preom2 chi=signsHead chi(signsTail chi preom2)
  where 
  els=(concat preom2);min=minimum els;ord=chi2ordf chi
  signsTail::[(Tu,Or)]->[[Int]]->[[Int]]
  signsTail chi preom2@(l:ls)
   =[l]++[ map signT set | set<-ls]
   where
   signT::Int->Int
   signT el | ord [min] [el] ==LT = el |otherwise= -el
  -- inserting the signs in the head of a sublist
  signsHead::[(Tu,Or)]->[[Int]]->[[Int]]
  signsHead chi preom2@(l:ls)
   =[[min]++map(\el->signH el chi) (l\\[min]) ]++ls
   where
   signH::Int->[(Tu,Or)]->Int
   signH el chi|ord[el][last(last preom2)]==LT =el
               |otherwise = -el 

-- chi -> preparation 1 of hyperline data
genSets::[(Tu,Or)]->[[Int]] 
genSets chi = sort(glue chi (tuplesL 1 els))
 where 
 els=sort (nub (concat (map fst chi)))
 -- chi -> hyperline data -> hyperline data
 glue::[(Tu,Or)]->[[Int]]->[[Int]];    glue [] pre = pre
 glue (([u,v],s):xs) pre 
  |s==0= glue xs([set|set<-pre,intersect set [u,v] == []]
    ++[nub(concat[a++b|a<-pre,b<-pre,u`elem`a,v`elem`b])])
  |otherwise = glue xs pre

-- ngon -> chi -> pair of hyperline with its sequence
hl2Pair::Ngon->[(Tu,Or)]->([Int],[[Int]])
hl2Pair hl chi=(nGonSort hl om2, om2)
 where 
 om2 = chi2HypR2 (ctrSetChi hl chi)
 nGonSort::[Int]->OM2->[Int]
 nGonSort hl om2 = [m]++sortBy fSort (hl\\[m])  
  where  m    = minimum hl
         [x,y]= [head(head om2),last(last om2)]
         fSort::Int->Int->Ordering 
         fSort a b|norm ([m,a,b,x,y],1)`elem`chi = LT
                  | otherwise                    = GT  

-- chi -> ordering function in hyperline
chi2ordf::[(Tu,Or)]->([Int]->[Int]->Ordering)
chi2ordf chi 
 = f where f::[Int]->[Int]->Ordering
           f a b |norm([head a, head b],1)`elem`chi = LT
                 |otherwise                         = GT







-------------------------------------------------------------
-- e -> set -> chi -> e in closure of set in chi? 
eInClSet::Int->[Int]->[OB]->Bool                       
eInClSet e set chi   
 |rankE == rankSet = True
 |otherwise        = False
 where  rankSet = fst (findRankInd set chi)
        rankE   = fst (findRankInd ([e]++set) chi)

-- r -> n -> chi -> dual chirotope of chi
dC::Int->Int->[Int]->[Int] 
dC r n l=reverse[(l!!i)*(plm(m1exp n r ((tuples r n)!!i))) 
                            |i<-[0..length(tuples r n)-1]]

-- exponent function used in function dC
m1exp::Int->Int->[Int]->Int
m1exp  n  r  tuple  
 | q == 0    = 0 
 | otherwise = q*(n-r-q + 1) 
              +(sum[(tuple!!(i-1))-i | i<-[1..(r-q)]]) 
              +(sum[(([1..n]\\tuple)!!(q+i-1))-(r + i)  
                              | i<-[1..(n-r-q)] ])  
                            where q = tu2q r n tuple

-- used in function dC for finding a dual chirotope
tu2q::Int->Int->[Int]->Int                 
tu2q r n [] = 0                         
tu2q r n (h:li)|h `elem`[(r+1)..n]=1+tu2q r n li  
               |otherwise         =  tu2q r n li  
plm::Int->Int
plm n |n==0 = 1 |n==1 = -1 |otherwise= plm(n-2)

-- k -> r -> n -> k-term GP-relations 
kTermGPrels::Int->Int->Int->[[([Int],[Int])]]
kTermGPrels k r n  
 |k/=3=[ map(\i->(a++(take (i-1) c)++(drop i c),
                  a++b++(take 1(drop (i-1)c))))[1..k]
       |a<-tuplesL (r-k+1)[1..n],b<-tuplesL(k-2)([1..n]\\a),
        c<-tuplesL k ([1..n]\\(a++b))]
 |k==3=[[(a++[b!!0]++[b!!1], a++[b!!2]++[b!!3])]
        ++[(a++[b!!0]++[b!!2], a++[b!!1]++[b!!3])]
        ++[(a++[b!!0]++[b!!3], a++[b!!1]++[b!!2])]
        |a<-tuplesL(r-2)[1..n],b<-tuplesL  4([1..n]\\a)]

-- exterior product in dimension 3
xProd::MA->[Integer]
xProd  [v1,v2] =[  det [[v1!!1,v1!!2],[v2!!1,v2!!2]],
                 -(det [[v1!!0,v1!!2],[v2!!0,v2!!2]]),
                   det [[v1!!0,v1!!1],[v2!!0,v2!!1]] ]

-- set1 -> set2 -> set1 contained in set2?
isSubSet::[Int]->[Int]->Bool
isSubSet  []     set = True
isSubSet  (x:xs) set  | x `elem` set = isSubSet xs set
                      | otherwise    = False

-- chi -> [dep] -> [] -> circuits of chi
chi2C::[OB]->[[Int]]->[[Int]]->[[Int]] 
chi2C chi [] cs = cs 
chi2C chi (dep:deps) cs 
 |length dep == 4  
  = chi2C chi deps (cs++[[    cComp4 p chi dep |p<-sels]]
                      ++[[-1*(cComp4 p chi dep)|p<-sels]])
 |length dep == 3
  =chi2C chi deps (cs++[[    cComp3 p ch dep |p<-sels]]
                     ++[[-1*(cComp3 p ch dep)|p<-sels]])
  where   els  = nub (concat (map fst chi))
          sels = [1..length els]
          ch   = ctrSetChi(take 1(els\\dep))chi


-- used in chi2C for finding circuits of a chirotope
cComp4::Int->[OB]->[Int]->Int
cComp4 p ch [a,b,c,z] 
 |p==a=     msc!!(head(elemIndices[b,c,z]mfc))
 |p==b= -1*(msc!!(head(elemIndices[a,c,z]mfc)))
 |p==c=     msc!!(head(elemIndices[a,b,z]mfc))
 |p==z= -1*(msc!!(head(elemIndices[a,b,c]mfc)))
 |otherwise=  0      where msc = map snd ch
                           mfc = map fst ch

-- used in chi2C for finding circuits of a chirotope
cComp3::Int->[OB]->[Int]->Int
cComp3  p ch [a,b,z] 
 |p==a= -1*(msc!!(head(elemIndices [b,z] mfc)))
 |p==b=     msc!!(head(elemIndices [a,z] mfc))
 |p==z= -1*(msc!!(head(elemIndices [a,b] mfc)))
 |otherwise=  0      where msc = map snd ch
                           mfc = map fst ch

-- matrix -> determinant of matrix
det::MA -> Integer 
det m
 |n == 1   = head (head m)
 |otherwise=sum(map
  (\i->((-1)^(i+1))*(head(m!!i))*(det
  [(map tail m)!!l|l<-[0..n-1],l/=i]))[0..n-1])
  where n = length m

-- rsets -> matrix -> (r x r)-sub-determinants
dets::[[Int]]->MA-> [Integer]
dets sets matrix = [det[matrix!!(i-1)|i<-set]|set<-sets] 

-- matrix -> chirotope of matrix
m2Chi::MA->[OB]
m2Chi m=zip trn (map toInt (map signum(dets trn m)))
        where n=length m
              r=length(head m)
              trn=tuples r n 

-- set -> chi -> deletes set in chi
delSetChi::[Int]->[OB]->[OB]
delSetChi [] chi = chi
delSetChi (h:rest) chi = delElChi h (delSetChi rest chi)

-- el -> chi -> deletes el in chi
delElChi::Int->[OB]->[OB]
delElChi el [] = []
delElChi el (h@(tu,_):rest)
 |el`elem`tu = delElChi el rest
 |otherwise  = [h]++delElChi el rest

-- set -> chi -> contracted chi at set
ctrSetChi::[Int]->[OB]->[OB]
ctrSetChi [] chi = chi
ctrSetChi set@(h:rest) chi 
 |k == length set = ctrSetChi rest (ctrElChi h chi)
 |otherwise = ctrSetChi list (delSetChi (set\\list) chi) 
 where (k,list)=findRankInd set chi

-- el -> chi -> contracted chi at el
ctrElChi::Int->[OB]->[OB]; ctrElChi k [] = []
ctrElChi k (h:list) = ((ctrST k h)++ctrElChi k list)
 where ctrST::Int->OB->[OB] 
       ctrST k (tu,sign)
        |k `notElem` tu    = []
        |posk `mod` 2 == 0 = [(tu\\[k],    sign)]
        |otherwise         = [(tu\\[k], -1*sign)]
         where  posk = head (elemIndices k tu)

-- set -> chi -> (k,ind), (rank of set, k-base in set)
findRankInd::[Int]->[OB]->(Int,[Int])
findRankInd  set chi                    
 |or[length(base\\set)==r-k|base<-bases]= (k,set)
 |otherwise = maximum (map(\i->findRankInd 
             (take(i-1)set++drop i set)chi)[1..k])
 where k    =length set
       r    =length(fst (head chi))
       bases=[fst st|st<-chi,snd st`elem`[-1,1]]

-- rank 5 hyperlines -> chirotope
hyp2ChiR5::[(Tu,OM2)]->[(Tu,Or)]
hyp2ChiR5 []=[]
hyp2ChiR5  ((hl,om2):rest) 
  =nub(sort
     [norm(tr++[b,c],1)| [i,j]<-tuples 2 l, 
    b<-om2!!(i-1), c<-om2!!(j-1), tr<-tuplesL 3 hl]
   ++[ norm (tr++[b,c],0)| i<-[1..l], 
    [b,c]<-tuplesL 2(om2!!(i-1)),tr<-tuplesL 3 hl]
   ++[ norm (qu++[x],0)  | qu<-tuplesL 4 hl,          
                            x<-(hl++concat om2)\\qu]
   ++ hyp2ChiR5 rest) where  l = length om2


-- chi -> hyperlines, rank 2
chi2HypR2::[(Tu,Or)]->OM2
chi2HypR2 chi=map nub(sortBy(chi2ordf chi)(preHypR2 chi))

