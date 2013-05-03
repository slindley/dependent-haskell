{-# LANGUAGE DataKinds, PolyKinds, RankNTypes,
    KindSignatures, GADTs, TypeOperators, TypeFamilies #-}

import Control.Applicative

{-
   Heterogeneous lists wrt a functor f:
     
      FList f [a1,...,an] == [f a1,  ..., f ak]
-}
data FList (f :: * -> *) (ts :: [*]) where
  FNil ::                      FList f '[]
  (:>) :: f a -> FList f ts -> FList f (a ': ts)

{- Identity functor -}
newtype Id a = Id a
type IdFList = FList Id

{- Type list concatenation -}
type family (ts :: [*]) :++: (ts' :: [*]) :: [*]
type instance '[]       :++: ts' = ts'
type instance (t ': ts) :++: ts' = t ': (ts :++: ts')

{- FList concatenation -}
(/++/) :: FList f ts -> FList f ts' -> FList f (ts :++: ts')
FNil      /++/ cs' = cs' 
(c :> cs) /++/ cs' = c :> (cs /++/ cs')

{- The free applicative functor -}
data FreeApp f a = forall ts.FreeApp (FList f ts) (IdFList ts -> a)

instance Functor f => Functor (FreeApp f) where
  fmap g (FreeApp cs f) = FreeApp cs (g . f)
  
instance Functor f => Applicative (FreeApp f) where
  pure v                         = FreeApp FNil (const v)
  FreeApp cs f <*> FreeApp cs' g =
     FreeApp (cs /++/ cs')
       (\xs -> let (ys, zs) = split cs cs' xs in f ys (g zs))

{- Split an FList into two parts.

   The first two arguments direct where to split the list. Both are
necessary for type inference even though the second is never
deconstructed.
-}
split :: FList f ts -> FList f ts' ->
           FList g (ts :++: ts') -> (FList g ts, FList g ts')
split FNil      _    xs       = (FNil, xs)
split (c :> cs) cs' (x :> xs) = (x :> ys, zs) where
  (ys, zs) = split cs cs' xs

{- The free alternative applicative functor -}
newtype FreeAlt f a = FreeAlt [FreeApp f a]

instance Functor f => Functor (FreeAlt f) where
  fmap g (FreeAlt ps) = FreeAlt (map (fmap g) ps)

instance Functor f => Applicative (FreeAlt f) where
  pure v                     = FreeAlt [pure v]
  FreeAlt ps <*> FreeAlt ps' = FreeAlt [p <*> p' | p <- ps, p' <- ps']

instance Functor f => Alternative (FreeAlt f) where
  empty                      = FreeAlt []
  FreeAlt ps <|> FreeAlt ps' = FreeAlt (ps ++ ps')
