module Bokowski.MatroidPolytopes where


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

-- oriented base -> normalized oriented base
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



genSets::[OB]->[[Int]] 
genSets chi = sort(glue chi (tuplesL 1 els))
 where  els=sort (nub (concat (map fst chi)))

glue::[OB]->[[Int]]->[[Int]]    
glue [] pre = pre
glue (([u,v],s):xs) pre 
 |s==0= glue xs([set|set<-pre,intersect set[u,v]==[]]
       ++[nub(concat[a++b|a<-pre,b<-pre,
                          u`elem`a, v`elem`b])])
 |otherwise = glue xs pre

chi2ordf::[OB]->([Int]->[Int]->Ordering)
chi2ordf chi = f 
 where f::[Int]->[Int]->Ordering
       f a b|norm([head a,head b],1)`elem`chi=LT
            |otherwise                       =GT

-- ordering function -> list -> inserted sign in tail of list
signsTail::OF->[[Int]]->[[Int]]
signsTail ord (l:ls)=[l]++[map signT set|set<-ls]
 where signT::Int->Int
       signT el |ord [min] [el] ==LT =  el 
                |otherwise           = -el
         where min = minimum l --????

signsHead::OF->[[Int]]->[[Int]]
signsHead ord (l:ls)
 =[[min]++map(\el->signH ord el) (l\\[min]) ]++ls
 where min = minimum l
       signH::OF->Int->Int
       signH  ord el 
        |ord [el] [last(last ls)]==LT =  el
        |otherwise                    = -el 

-- complete sign insertion
siIn::[OB]->[[Int]]
siIn chi=signsHead ord (signsTail ord (genSets chi))
     where ord = chi2ordf chi

chi2HypR2::[OB]->OM2
chi2HypR2 chi = sortBy (chi2ordf chi) (siIn chi)

