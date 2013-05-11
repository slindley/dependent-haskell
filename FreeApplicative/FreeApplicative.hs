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

{-
  

  -- (FreeApp cs f) <*> (FreeApp cs' g) =
  --   let n = flength cs in
  --    FreeApp (cs /++/ cs')
  --      (\xs -> dropLem cs cs'
  --                (takeLem cs cs'
  --                  (f (ftake n xs) (g (fdrop n xs)))))


data Nat = Z | S Nat

data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

takeLem :: forall f ts ts' t.FList f ts -> FList f ts' -> ((ts ~ FTake (FLength ts) (ts :++: ts')) => t) -> t
takeLem FNil      _   t = t 
takeLem (c :> cs) cs' t = takeLem cs cs' t

dropLem :: forall f ts ts' t.FList f ts -> FList f ts' -> ((ts' ~ FDrop (FLength ts) (ts :++: ts')) => t) -> t
dropLem FNil _        t = t
dropLem (c :> cs) cs' t = dropLem cs cs' t

type family FLength (ts :: [*]) :: Nat
type instance FLength '[] = Z
type instance FLength (a ': ts) = S (FLength ts)

flength :: FList f ts -> Natty (FLength ts)                       
flength FNil      = Zy
flength (c :> cs) = Sy (flength cs) 
                    
type family FTake (n :: Nat) (ts :: [*]) :: [*]
type instance FTake Z      ts       = '[]
type instance FTake (S n) '[]       = '[]
type instance FTake (S n) (t ': ts) = t ': FTake n ts

ftake :: Natty n -> FList f ts -> FList f (FTake n ts)
ftake Zy     cs        = FNil
ftake (Sy n) FNil      = FNil
ftake (Sy n) (c :> cs) = c :> ftake n cs

type family FDrop (n :: Nat) (ts :: [*]) :: [*]
type instance FDrop Z      ts       = ts
type instance FDrop (S n) '[]       = '[]
type instance FDrop (S n) (t ': ts) = FDrop n ts

fdrop :: Natty n -> FList f ts -> FList f (FDrop n ts)
fdrop Zy     cs        = cs
fdrop (Sy n) FNil      = FNil
fdrop (Sy n) (c :> cs) = fdrop n cs
-}