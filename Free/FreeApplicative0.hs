{- Free applicative functor over a functor -}

{- (plain version - no type-level computation) -}

{-# LANGUAGE GADTs, KindSignatures #-}

import Control.Applicative

{-
   heterogeneous lists wrt a functor f:
     
      FList f [a1,...,an] == [f a1,  ..., f ak]
-}
data FList (f :: * -> *) (ts :: *) where
  FNil ::                      FList f ()
  (:>) :: f a -> FList f ts -> FList f (a , ts)

{- the free applicative functor -}
data FreeApp f a where
  FreeApp :: (FList f ts) -> (ts -> a) -> FreeApp f a

instance Functor f => Functor (FreeApp f) where
  fmap g (FreeApp cs f) = FreeApp cs (g . f)
  
instance Functor f => Applicative (FreeApp f) where
  pure v                          = FreeApp FNil (\() -> v)
  FreeApp FNil f <*> FreeApp cs g =
    FreeApp cs (\xs -> (f ()) (g xs))
  FreeApp (c :> cs) f <*> p =
    case FreeApp cs (\xs v x -> f (x, xs) v) <*> p of
      FreeApp cs' f' ->
        FreeApp (c :> cs') (\(x, xs) -> f' xs x)

{- the free alternative applicative functor -}
newtype FreeAlt f a = FreeAlt [FreeApp f a]

instance Functor f => Functor (FreeAlt f) where
  fmap g (FreeAlt ps) = FreeAlt (map (fmap g) ps)

instance Functor f => Applicative (FreeAlt f) where
  pure v                     = FreeAlt [pure v]
  FreeAlt ps <*> FreeAlt ps' = FreeAlt [p <*> p' | p <- ps, p' <- ps']

instance Functor f => Alternative (FreeAlt f) where
  empty                      = FreeAlt []
  FreeAlt ps <|> FreeAlt ps' = FreeAlt (ps ++ ps')
