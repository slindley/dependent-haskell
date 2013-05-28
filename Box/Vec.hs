{-# LANGUAGE
    DataKinds, KindSignatures,
    RankNTypes, GADTs, TypeOperators #-}

module Vec where

import Data.Monoid
import Control.Applicative
import Data.Foldable
import Data.Traversable

import Nat

data Vec :: Nat -> * -> * where
  V0   ::                 Vec Z x
  (:>) :: x -> Vec n x -> Vec (S n) x

vlength :: Vec n x -> Natty n
vlength V0        = SZ
vlength (x :> xs) = natter n (SS n) where n = vlength xs
-- The extra constraints on singletons introduced by the singletons
-- library require us to call natter to introduce the NATTY n type
-- class constraint. Without these constraints we can write simply:
--                                          
--   vlength (x :> xs) = SS (vlength xs)

instance Show x => Show (Vec n x) where
  show = show . foldMap (:[])

vcopies :: forall n x.Natty n -> x -> Vec n x
vcopies SZ x = V0
vcopies (SS n) x = x :> vcopies n x   

vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
vapp V0 V0 = V0
vapp (f :> fs) (s :> ss) = f s :> vapp fs ss

instance NATTY n => Applicative (Vec n) where
  pure = vcopies natty where
  (<*>) = vapp where

instance Traversable (Vec n) where
  traverse f V0 = pure V0
  traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs

instance Functor (Vec n) where
  fmap = fmapDefault

instance Foldable (Vec n) where
  foldMap = foldMapDefault

vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
vappend V0        ys = ys
vappend (x :> xs) ys = x :> vappend xs ys

vchop :: Natty m -> Natty n -> Vec (m :+ n) x -> (Vec m x, Vec n x)
vchop SZ n xs = (V0, xs)
vchop (SS m) n (x :> xs) = (x :> ys, zs) where (ys, zs) = vchop m n xs
