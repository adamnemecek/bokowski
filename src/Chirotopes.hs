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


-- chi -> hyperlines, rank 2
chi2HypR2::[(Tu,Or)]->OM2
chi2HypR2 chi=map nub(sortBy(chi2ordf chi)(preHypR2 chi))

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

chi2ordf::[OB]->([Int]->[Int]->Ordering)
chi2ordf chi = f 
 where f::[Int]->[Int]->Ordering
       f a b|norm([head a,head b],1)`elem`chi=LT
            |otherwise                       =GT
-----------------------------------------------------------------

-- chi -> cocircuits
chi2Coc::[OB]->[[Int]] 
chi2Coc chi 
 = sort(result++(map (map negate) result))
 where
  result = [ map (\i-> sideOfHplane i hplane) [1..n]
             | hplane <- rankRm1 chi ] 
  els   = nub(concat(map fst chi))
  r     = length (fst (head chi))
  n     = length els
  bases = [fst st| st <- chi, snd st `elem` [-1,1]]
  sideOfHplane::Int->[Int]->Or
  sideOfHplane el hp 
   | el `elem` hp                             =  0
   | norm (((baseOfHp hp)++[el]),1)`elem` chi =  1
   | otherwise                                = -1
  baseOfHp::[Int]->[Int]  
  baseOfHp hplane = head[el| el <- tuplesL (r-1) hplane,
                              x <- (els\\hplane),
                              sort (el++[x]) `elem` bases ]

-- chi -> all (rank-1)-flats of chi
rankRm1::[OB]->[[Int]]
rankRm1 chi=nub(map sort(nub[clHP hp chi|hp<-hPlanes]))
 where 
 r      = length(fst (head chi))
 n      = maximum (concat (map fst chi))
 bases  = [fst st| st <- chi, snd st `elem` [-1,1]]
 hPlanes= nub[           fst (splitAt(j-1)base)
              ++drop 1 ( snd (splitAt(j-1)base) ) 
                          | base<-bases, j <- [1..r]] 

 -- hyperplane -> chi -> closure of hyperplane in chi
 clHP::[Int]->[OB]->[Int]
 clHP hp c = sort(hp++[el| el <- [1..n]\\hp, 
                          (sort(hp++[el]),0)`elem`c])

-- rank 2 hyperlines -> chirotope
hyp2ChiR2::OM2->[OB] 
hyp2ChiR2 [] = []
hyp2ChiR2 (h:rest)   
 =  [norm([h!!(i-1),h!!(j-1)],0)|[i,j]<-tuples 2 l]
  ++[norm([h!!i,(rest!!j)!!k],1) 
     | i<-[0..l-1], j<-[0..lr-1],
       k<-[0..length(rest!!j)-1]]
  ++hyp2ChiR2 rest    where  l = length h
                             lr= length rest
-- chi -> hyperlines, rank 3
chi2HypR3::[OB]->[([Int],OM2)]
chi2HypR3 chi=map(\i->([i],chi2HypR2(ctrElChi i chi)))els
           where els=nub(concat(map fst chi))

-- rank 3 hyperlines -> chirotope
hyp2ChiR3::[([Int],OM2)]->[OB] 
hyp2ChiR3 [] = []
hyp2ChiR3 (h:rest) 
 =nub(sort([norm([a,b,c],1)|
            a<-fst h,[i,j]<-tuples 2 l,
            b<-((snd h)!!(i-1)), 
            c<-((snd h)!!(j-1)) ]
   ++[norm(pair++[c],0)|pair<-(tuplesL 2(fst h)), 
                        c   <-concat(snd h)]
   ++[norm([a]++pair,0)|a<-fst h,i<-[1..l],
                        pair<-tuplesL 2((snd h)!!(i-1))] 
   ++ hyp2ChiR3 rest)) 
                        where  l = length (snd h)

-- chi -> chirotope with signs of chi reversed
signRevChi::[OB]->[OB]
signRevChi chi = map (\(tu,s)->(tu, negate s)) chi

-- set -> chi -> reoriented chi at set
reorSetChi::[Int]->[OB]->[OB]
reorSetChi [] chi = chi
reorSetChi (el:els) chi =reorSetChi els (reorElChi el chi)

-- el -> chi -> reoriented chi at el
reorElChi::Int->[OB]->[OB]
reorElChi el chi = map (reorChiTuple el) chi

-- k -> base -> reoriented base at k
reorChiTuple::Int->OB->OB
reorChiTuple  x (tu,sign) | x`elem`tu = (tu,-sign) 
                          | otherwise = (tu, sign)

{-
-- for finding a mutation in a chirotope, rank 4
mutOfChi::[Int]->[OB]->Bool 
mutOfChi  [m,n,o,p]  chi
 =and[gpCheckR2(sort[a,b,c,d])(ctrSetChi[u,v]testChi) 
          |[u,v] <- tuplesL 2  [m,n,o,p], 
           [a,b] <- tuplesL 2 ([m,n,o,p]\\[u,v]),
           [c,d] <- tuplesL 2 ([1..10]\\[u,v,a,b])] 
 where 
 testChi = [changeSign [m,n,o,p] el| el<-chi]
 changeSign::[Int]->OB->OB   --
 changeSign mut sTuple
  | mut == fst sTuple = (mut, -(snd sTuple))
  | otherwise         = sTuple
-}

-- chi -> facets of uniform chirotope
simplicialFacetsChi::[OB]->[[Int]]
simplicialFacetsChi chi
 =[p|p<-tuples (r-1) n,
       (and[norm(p++[x], 1)`elem`chi|x<-[1..n]\\p])
     ||(and[norm(p++[x],-1)`elem`chi|x<-[1..n]\\p])]
  where r   = length (fst (head chi))
        n   = maximum (concat (map fst chi))
