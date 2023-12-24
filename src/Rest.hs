module Bokowski.Rest where

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


-- n -> concat (map(i->tuples i n)[o..n])
reorLists::Int->[[Int]] 
reorLists n = concat(map (\i-> tuples i n) [0..n]) 

-- list -> list of all permutations of list
permsSet::[Int]->[[Int]] 
permsSet l 
 |length l == 1 = [l]
 |otherwise=concat(map(\e->map([e]++)(permsSet(l\\[e])))l) 

-- list -> list of all permutations of list
perm::[Int]->(Int->Int)
perm list = (\i-> list!!(i-1)) 

-- permutation -> chi -> relabeling of chi
relabelChi::(Int->Int)->[OB]->[OB]
relabelChi pi (st:sts) 
 = sort ([relabelST pi st]++(relabelChi pi sts)) 

-- permutation -> signed tupel -> relabeling of signed tupel
relabelST::(Int->Int)->OB->OB
relabelST pi (tu,s) = norm (map pi tu,s)

-- candidates of chirotopes, rank 3, 5 elements
all5::[[Or]]
all5=map([1,1,1,1,1,1]++)[[a,b,c,d]|a<-s,b<-s,c<-s,d<-s]
     where s = [-1,1]

--candidates of hyperline sequences, rank 3, 5 elements
cand::[[([Int],OM2)]]
cand = map chi2HypR3 (map (zip (tuples 3 5)) all5)

-- resulting hyperline sequence, rank 3, 5 elements
rest::[[([Int],OM2)]]
rest=[hyp|hyp<-cand,length(nub(sort(hyp2ChiR3 hyp)))==10] 

-- relabeling of hyperlines in rank 3
relabelHypR3::(Int->Int)->[(Tu,OM2)]->[(Tu,OM2)]
relabelHypR3  pi om3 = map (relab pi) om3

-- used for relabeling in rank 3
relab::(Int->Int)->(Tu,OM2)->(Tu,OM2)
relab pi (om1,om2) = (rel pi om1,map (rel pi) om2)

-- used for relabeling in relab
rel::(Int->Int)->[Int]->[Int]
rel pi om1 = map(\x->(signum x)*(pi(abs x))) om1

-- for finding normalized hyperline sequence
normSeqs::[(Tu,OM2)]->[(Tu,OM2)]; normSeqs []=[]
normSeqs (l:ls) = sort ([normSeq l]++normSeqs ls) 
normSeq::(Tu,OM2)->(Tu,OM2)
normSeq (om1,om2)
 |head om1<0=normSeq([-(head om1)],reverse om2)
 |otherwise =(om1, findNorm om2)

-- for finding normalized hyperline in rank 3
findNorm::[[Int]]->[[Int]]
findNorm om2@(c:cs)
 | head c == minimum (map abs (concat om2)) =(c:cs) 
 | otherwise = findNorm (cs++[[-(head c)]])

-- for sign reversal in rank 3
signRevR3::[(Tu,OM2)]->[(Tu,OM2)]
signRevR3 om3 = map (signRevRow) om3

-- for sign reversal in rank 3
signRevRow:: (Tu,OM2)->(Tu,OM2)
signRevRow ([i],om2) = ([negate i],om2) 

-- reorientation of uniform hyperline sequences in rank 3 
reorSetR3::[Int]->[(Tu,OM2)]->[(Tu,OM2)]
reorSetR3 [] om3 = om3
reorSetR3 (el:els) om3 = reorSetR3 els (reorElR3 el om3)

-- for reorSetR3
reorElR3::Int->[(Tu,OM2)]->[(Tu,OM2)]
reorElR3 el om3 = map (reorRowR3 el) om3

-- for reorElR3
reorRowR3::Int->(Tu,OM2)->(Tu,OM2)
reorRowR3 x (tu,(e:es))
 |x`elem`map abs tu
       =(tu,[e]++map(map negate)(reverse es))
 |x`elem`map abs(concat es) 
       =(tu,[e]++map(reorR1 x) es )
 |x`elem`map abs e 
       =(tu,[map negate(reorR1 x e)]++map(map negate)es) 

-- for reorRowR3
reorR1::Int->[Int]->[Int]; reorR1 el [] = []
reorR1 el (x:xs) |el== abs x = [-x]++xs
                 |otherwise  = [ x]++(reorR1 el xs)

-- equivalence check
checkOM3Pair::[(Tu,OM2)]->[(Tu,OM2)]->[([Int],[Int],Bool)]
checkOM3Pair  om3A om3B 
 =  concat[[(s1,s2,sr)]
             |s1 <- permsSet [1..5], 
              s2 <- reorLists 5,
              sr <- [True,False],  
              sr&&  (nS (sR(r (p s1)(rS s2 om3A)))==om3B)]
  ++concat[[(s1,s2,sr)]
             |s1 <- permsSet [1..5], 
              s2 <- reorLists 5,  
              sr <- [True,False],  
              not sr &&(nS (r (p s1)(rS s2 om3A)) ==om3B)]
  where   r  = relabelHypR3; p  = perm
          rS = reorSetR3  
          sR = signRevR3
          nS = normSeqs    

-- consistency check in rank 2 
gpCheckR2::[Int]->[OB]->Bool
gpCheckR2   [a,b,c,d] chi
 | s1*s2== -s3*s4 && s1*s2==s5*s6 = False
 | otherwise                      = True
 where
 s1=si a b chi;   s2=si c d chi
 s3=si a c chi;   s4=si b d chi
 s5=si a d chi;   s6=si b c chi

 si::Int->Int->[([Int],Int)]->Int
 si _ _ [] = 2
 si  a b (([c,d],s):hs) |[a,b]==[c,d]= s 
                        |otherwise   = si a b hs

-- signs -> characters for signs
change::[Int]->[Char]
change [] = []
change (x:xs)| x ==  0 = "0" ++ (change xs)
             | x ==  1 = "+" ++ (change xs)
             | x == -1 = "-" ++ (change xs)

-- chi -> facets of chi
chi2Facets::[OB]->[[Int]]
chi2Facets chi
 =[el| el <- rankRm1 chi, 
   not(or[(norm(tu++[x], 1)`elem`chi
         &&norm(tu++[y],-1)`elem`chi)
        ||(norm(tu++[x],-1)`elem`chi
         &&norm(tu++[y], 1)`elem`chi)
           | tu  <-  tuplesL (r-1) el,
             tu `elem` hps,
             [x,y] <- tuplesL 2 ([1..n]\\el) ])]
 where  
  r = length(fst(head chi))
  n = maximum (concat (map fst chi))
  bases = [fst st| st <- chi, snd st `elem` [-1,1]]
  hps   = nub[           fst(splitAt(j-1)base)
              ++drop 1 ( snd(splitAt(j-1)base) ) 
                  | base <- bases,  j <- [1..r] ] 

-- simplicial facets of 3-sphere -> subfacets
subfacets::[[Int]]->[[Int]]         
subfacets facets = nub (sub facets)
  where sub::[[Int]]->[[Int]]
        sub [] = []
        sub (f:fs) = [ f\\[j]| j<-f] ++ sub fs

-- simplicial facets -> hyperline bounds
hlBds::[[Int]]->[([Int],[Int])] 
hlBds facets=[(sf,pair)|sf   <- subfacets facets,
                        pair <- 
             let pairs = tuplesL 2 ([1..n]\\sf)
             in  pairs ++ (map reverse pairs),
               sort(sf++[head pair])`elem`facets,
               sort(sf++[last pair])`elem`facets]
   where n = length (nub (concat facets))

-- generates necessary simplex orientations for a 3-sphere
nSO::[[Int]]->[([Int],[Int])]->[OB]->[OB] 
nSO  _ [] so = so
nSO facets ( hlb@(hl,[x,y]):hlbRest) so  
 |norm (hl++[x,y],1) `elem` so
  = nSO facets [el|el<-hlbRest,el/=(hl,[y,x])]
    (so++[norm((hl++[x,i]),1)|i<-[1..n]\\(hl++[x,y])]
       ++[norm((hl++[i,y]),1)|i<-[1..n]\\(hl++[x,y])])  
 |otherwise = nSO facets (hlbRest++[hlb]) so
    where n = length (nub (concat facets))

-- sign consequences from GP relations
consR5::[Int]->[Int]->[OB]->[OB] 
consR5 hline [a,b,c,d] om2    -- new signs in rank 5
 |s3*s4/=0 && s3*s4+s5*s6==0
  if(s1==2&&s2/=0&&known 1)then=[norm(hline++[a,b],s2*s3*s4)] 
  if(s2==2&&s1/=0&&known 2)then=[norm(hline++[c,d],s1*s3*s4)] 
 |s1*s2/=0 && s1*s2==s5*s6  
  if(s3==2&&s4/=0&&known 3)then=[norm(hline++[a,c],s4*s1*s2)] 
  if(s4==2&&s3/=0&&known 4)then=[norm(hline++[b,d],s3*s1*s2)] 
 |s1*s2/=0 && s1*s2+s3*s4==0
  if(s5==2&&s6/=0&&known 5)then=[norm(hline++[a,d],s6*s3*s4)] 
  if(s6==2&&s5/=0&&known 6)then=[norm(hline++[b,c],s5*s3*s4)] 
 | otherwise = []
 where
 s1=si a b om2; s2=si c d om2 
 s3=si a c om2; s4=si b d om2
 s5=si a d om2; s6=si b c om2
 sv = [s1,s2,s3,s4,s5,s6]
 known::Int->Bool
 known i = 2 `notElem` (take (i-1) sv ++ drop i sv)

-- used in gpCheck, consR5, contra
si::Int->Int->[OB]->Or; sign _ _ [] = 2
si a b (([c,d],s):hs) |(a,b)==(c,d)=s |otherwise = si a b hs

--
listOfNewSigns::Int->[OB]->[OB]
listOfNewSigns n oldSigns
 | newSigns==[] = sort oldSigns 
 | otherwise    = listOfNewSigns n (oldSigns++newSigns)   
 where newSigns = nub (concat set) 
       set=[consR5 hline four (ctrSetChi hline oldSigns) 
               | four  <- tuplesL 4 [1..n],
                 hline <- tuplesL (r-2) ([1..n]\\four)]
       r = length (fst (head oldSigns))

-- 4 elements -> chi -> GP contradiction?
contra::[Int]->[OB]->Bool
contra [a,b,c,d] list          -- a < b < c < d
 | s1*s2==  1 && s3*s4== -1  && s5*s6==  1 = False
 | s1*s2== -1 && s3*s4==  1  && s5*s6== -1 = False
 | otherwise = True
 where
 s1=si a b;s2=si c d;s3=si a c
 s4=si b d;s5=si a d;s6=si b c
 si::Int->Int->Int;  si a b = sign a b list

-- n -> chi -> any GP contradiction?
contraGP::Int->[OB]->Bool
contraGP n oS =and[contra t4 (ctrSetChi t3 oS) 
                 |t4<-tuples 4 n,t3<-tuplesL 3([1..n]\\t4)]

inRow::Int->Int->([(Ngon,OM2)],[Or])->[([(Ngon,OM2)],[Or])]
inRow n row (hyp,chi)
 = [((aHyp++[(tr, ext s n p om2)]++bHyp), newsigns)
     | s<-[-1,1], p<-[1..lom2], newsigns<-
  let st= [norm(tr++[el,s*n],1)|i<-[1..p],   el<-om2!!(i-1)]
    ++[norm(tr++[s*n,el],1)|i<-[(p+1)..lom2],el<-om2!!(i-1)] 
 in  newOrEmpty n chi st ]
 where (aHyp,((tr,om2):bHyp)) = splitAt (row-1) hyp
       lom2 = length om2
       ext::Int->Int->Int->OM2->OM2   -- s sign of n          
       ext   s    n    p   om2 = a++[[s*n]]++b      
        where  (a,b) = splitAt p om2
       newOrEmpty::Int->[Or]->[(Tu,Or)]->[[Or]]
       newOrEmpty n chi [] = [chi]  
       newOrEmpty n chi ((tu,s):rest)
        |e`notElem`[s,2] = []
        |otherwise = newOrEmpty n newChi rest
         where  i  = head(elemIndices tu(tuples 5 finalN))
          (a,(e:b))= splitAt i chi; newChi= a++[s]++b

-- all matroid polytope extensions 
inAll::Int->Int->Int->([OM5],[Or])->[([OM5],[Or])]
inAll  finN  n   row      sofar 
 |row == 1 =inRow n 1 sofar
 |otherwise=concat(map(inRow n row)
                  (inAll finN n(row-1)sofar))

-- extensions of matroid polytopes, uniform case
extMPu::Int->Int->[Or]->[[Or]]
extMPu finN k knownSigns
 | k == 5 = map snd (inAll finN 6 10 (startHyp,knownSigns))
 |otherwise
  =concat
   (map(\sl->
  let slist=delSetChi[k..finN](zip(tuples 5 finN)sl)
  in  map snd(inAll finN k rows  
         (chi2HypR5 slist, sl) )) 
         previousSignlists)
 where
  startHyp           = chi2HypR5 [([1,2,3,4,5],1)]
  rows               = length (tuples 3 (k-1))
  previousSignlists  = extMPu finN (k-1) knownSigns

erg=extMPu 7 7 [1]++drop 1(replicate(length(tuples 5 7))2) 

-- chi -> ordering function in hyperline
chi2ordf::[(Tu,Or)]->([Int]->[Int]->Ordering)
chi2ordf chi 
 = f where f::[Int]->[Int]->Ordering
           f a b |norm([head a, head b],1)`elem`chi = LT
                 |otherwise                         = GT

-- chi -> hyperlines, rank 5
chi2HypR5::[(Tu,Or)]->[OM5]   
chi2HypR5 chi = map (\hl->hl2Pair hl chi) hls
 where trs  = tuplesL 3 els
       hls  = nub(map sort (map (\tr-> cl tr chi) trs))
       els  = sort(nub(concat(map fst chi)))

-- set -> chi -> closure of set (chi) 
cl::[Int]->[(Tu,Or)]->[Int] 
cl tr chi = tr++[e| e<-els, eInHl e tr els chi]
 where els = sort(nub(concat(map fst chi)))

--erste Version  cl::[Int]->[OB]->[Int] 
--               cl set chi = set++[e| e<-(els\\set), eInClSet e set chi]
--                where els = sort(nub(concat(map fst chi)))

-- used in cl
eInHl::Int->Ngon->[Int]->[(Tu,Or)]->Bool
eInHl e tr [] chi = True
eInHl e tr (x:xs) chi
  |x `elem` (tr++[e])            = eInHl e tr xs chi
  |norm(tr++[e,x],0)`notElem`chi = False
  |otherwise                     = eInHl e tr xs chi

main = print (map snd (extMP 7 7 (signs 7)))

-- extensions of matroid polytopes, non-uniform
extMP::Int->Int->[Or]->[([OM5],[Or])]
extMP n k signs 
 | k == 6  = inAll 6 10 (startHyp, startSigns)
 |otherwise= concat ( map (inAll k lTu3s)  
             [(el, signsForExt n k signs) 
              |el<-map chi2HypR5(map hyp2ChiR5
               (map fst(extMP n (k-1) signs)))])
 where startHyp  = chi2HypR5 [([1,2,3,4,5],1)]
       startSigns= signsForExt n 6 signs
       lTu3s     = length (tuples 3 (k-1))

--
tailTup::Int->[[Int]]
tailTup n=map(++[n])(tuples 4 (n-1))
 
--
signsForExt::Int->Int->[Or]->[Or] 
signsForExt n k signs
  =map (\i-> signs!!(head (elemIndices i (tuples 5 n)))) 
       (map (++[k]) (tuples 4 (k-1))) 

inAll::Int->Int->([OM5],[Or])->[([OM5],[Or])]
inAll n row sofar 
 |row == 1  =inRow n 1 sofar
 |row>maxRow=concat(map(inRow n maxRow)
                       (inAll n(maxRow-1)sofar))
 |otherwise =concat(map(inRow n row)
                       (inAll n(row-1)sofar))
 where maxRow = length (fst sofar) 

-- inserting an element in a row, uniform case
inRow::Int->Int->([OM5],[Or])->[([OM5],[Or])]
inRow n row pair = (inHl n row pair)++(inOM2 n row pair) 
inHl::Int->Int->([OM5],[Or])->[([OM5],[Or])]
inHl n row (rows,chi)
 =[((firstRows++[(take g gon++[n]++drop g gon,om2)]
                                 ++lastRows),signs)
   | g<-[1..length gon], signs <- 
  let si= [norm(tr++[p1,p2],1)
            |tr<-tuplesL 3 (take g gon++[n]++drop g gon), 
             n`elem`tr, [p1,p2]<-pairs om2]
         ++[norm(tr++[p1,p2],0)
            |tr <- tuplesL 3 (take g gon++[n]++drop g gon), 
             n`elem`tr, u<-[1..length om2],
             [p1,p2]<-tuplesL 2(om2!!(u-1))]
         ++[norm(tr++[n,x],0) |tr <- tuplesL 3 gon,
             n`notElem`tr, u<-[1..length om2], 
                           x<-(om2!!(u-1))++(gon\\tr)]  
  in         newOrEmpty n chi si                       ]
 where (firstRows,((gon,om2):lastRows))=splitAt(row-1)rows
       pairs::OM2->OM2
       pairs om2=[[x,y]| [u,v] <- tuples 2 (length om2),
                          x<-om2!!(u-1), y<-om2!!(v-1)]

ext::Int->Int->Int->Int->OM2->OM2          
ext s n p q om2|q==0=take (p-1) a++[(last a)++[s*n]]++b
               |q==1=a++[[s*n]]++b 
    where(a,b)=splitAt p om2
> ext (-1) 6 2 0 [[1],[2],[3,4],[5]]
leads to [[1],[2,-6],[3,4],[5]]

newOrEmpty::Int->[Or]->[(Tu,Or)]->[[Or]]
newOrEmpty n chi [] = [chi]  
newOrEmpty n chi ((tu,s):rest)
 |e`notElem`[s,2]= []
 |otherwise      = newOrEmpty n newChi rest
 where  i        = head (elemIndices tu (tailTup n))
        (a,(e:b))= splitAt i chi; newChi= a++[s]++b

-- inserting in rank 2 oriented matroid
inOM2::Int->Int->([OM5],[Or])->[([OM5],[Or])]
inOM2 n row (rows,chi)   
 =[((firstRows++[(gon,ext s n p q om2)]
              ++lastRows),newsigns)
          | s <- [-1, 1], p <- [1..lom2], q <- [0,1],
            newsigns<-    
 let s1=if q==0
     then[norm(tr++[el,s*n],1)|i<-[1..p-1],el<-om2!!(i-1), 
          tr<-trs ]++[norm(tr++[el,s*n],0)|i<-[p], 
          el<-om2!!(i-1), tr<-trs ]++[norm(tr++[s*n,el],1)
          |i<-[p+1..lom2],el<-om2!!(i-1), tr<-trs ]
         ++[norm(qu++[n],0)|qu <- tuplesL 4 gon]
     else []
  s2=if q==1 
     then[norm(tr++[el,s*n],1)| i<-[1..p],el<-om2!!(i-1), 
          tr<-trs]++[norm(tr++[s*n,el],1)|i<-[p+1..lom2],
          el<-om2!!(i-1),tr<-trs]++[norm(qu++[n],0)   
          | qu<-tuplesL 4 gon]
     else [] 
 in (newOrEmpty n chi (s1++s2))]
 where(firstRows,((gon,om2):lastRows))=splitAt(row-1)rows
       lom2 = length om2; trs = tuplesL 3 gon

-- preparation of GP-relations, 10 elements
gpRelations::[([Int],[Int])]  --  { a,b,c,d | v,w,x,y }
gpRelations   -- we prepare all Grassmann--Pluecker relations
 = [([a,b,c,d],[v,w,x,y])
    | [a,b,c,d]<-tuplesL 4 [1..10],
      [v,w,x,y]<-tuplesL 4 ([1..10]\\[a,b,c,d])] 

-- take 2 gpRelations
--[([1,2,3,4],[5,6,7,8]),([1,2,3,4],[5,6,7,9])]
                  
gpRel2Products::([Int],[Int])->[([Int],Int)]  -- ordered
gpRel2Products  gprel@([a,b,c,d],[v,w,x,y])   
 = [ norm ([a,b,c,d,v,w],1), norm ([a,b,c,d,x,y],1),
     norm ([a,b,c,d,v,x],1), norm ([a,b,c,d,y,w],1), 
     norm ([a,b,c,d,v,y],1), norm ([a,b,c,d,w,x],1) ]

gpRelProducts = (map gpRel2Products gpRelations) 

-- index for a bracket
bracket2Index::([Int],Int)->Int 
bracket2Index  br = head (elemIndices (fst br) (tuples 6 10))

--
modifiedSign::([Int],Int)->Int  -- dC inserted 
modifiedSign br = (dC!!(bracket2Index br))*(snd br)

-- used in reduced system calculation
g::[(Int,Int)]->[((Int,Int),(Int,Int))] 
g list@[(a,sa),(b,sb),(c,sc),(d,sd),(e,se),(f,sf)] 
 | sa*sb ==  1 && sc*sd ==  1 = [((a,b),(e,f)),((c,d),(e,f))]
 | sa*sb ==  1 && se*sf ==  1 = [((a,b),(c,d)),((e,f),(c,d))]
 | sc*sd ==  1 && se*sf ==  1 = [((c,d),(a,b)),((e,f),(a,b))]
 | sa*sb == -1 && sc*sd == -1 = [((a,b),(e,f)),((c,d),(e,f))]
 | sa*sb == -1 && se*sf == -1 = [((a,b),(c,d)),((e,f),(c,d))]
 | sc*sd == -1 && se*sf == -1 = [((c,d),(a,b)),((e,f),(a,b))]

--((0,9),(2,5)),((1,6),(2,5))  0 * 9 < 2 * 5 and 1 * 6 < 2 * 5

-- reduced system calculation
main=print(concat(map g (map part) gpRelProducts)))
     where part=map(\br->(bracket2Index br,modifiedSign br))


--
symmetry::Int->Int
symmetry k = 15 - k

