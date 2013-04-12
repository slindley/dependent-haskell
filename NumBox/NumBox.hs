{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables #-}

module NumBox where

import Data.Monoid
import Control.Applicative
import Data.Foldable
import Data.Traversable

data Nat = Z | S Nat

data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

class NATTY (n :: Nat) where
  natty :: Natty n

instance NATTY Z where
  natty = Zy

instance NATTY n => NATTY (S n) where
  natty = Sy natty

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance S m :+ n = S (m :+ n)

(/+/) :: Natty m -> Natty n -> Natty (m :+ n)
Zy /+/ n = n
Sy m /+/ n = Sy (m /+/ n)

data Cmp :: Nat -> Nat -> * where
  LTNat :: Natty y -> Cmp x (x :+ S y)
  EQNat :: Cmp x x
  GTNat :: Natty x -> Cmp (y :+ S x) y

cmp :: Natty x -> Natty y -> Cmp x y
cmp Zy Zy = EQNat
cmp Zy (Sy y) = LTNat y
cmp (Sy x) Zy = GTNat x
cmp (Sy x) (Sy y) = case cmp x y of
  LTNat z -> LTNat z
  EQNat -> EQNat
  GTNat z -> GTNat z

data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
  LTCuts :: Natty b -> CmpCuts a (S b :+ c) (a :+ S b) c
  EQCuts :: CmpCuts a b a b
  GTCuts :: Natty b -> CmpCuts (a :+ S b) c a (S b :+ c)

cmpCuts :: ((a :+ b) ~ (c :+ d)) => Natty a -> Natty b -> Natty c -> Natty d -> CmpCuts a b c d
cmpCuts Zy b Zy     d  = EQCuts
cmpCuts Zy b (Sy c) d  = LTCuts c
cmpCuts (Sy a) b Zy d  = GTCuts a
cmpCuts (Sy a) b (Sy c) d = case cmpCuts a b c d of
  LTCuts z -> LTCuts z
  EQCuts -> EQCuts
  GTCuts z -> GTCuts z

{-
leftCan :: forall a b c t. ((a :+ b) ~ (a :+ c)) => Natty a -> Natty b -> Natty c -> ((b ~ c) => t) -> t
leftCan Zy b c t = t
leftCan (Sy a) b c t = leftCan a b c t

assocLR :: forall l a b c t. (l ~ ((a :+ b) :+ c)) => Natty a -> Natty b -> Natty c -> ((l ~ (a :+ (b :+ c))) => t) -> t
assocLR Zy b c t = t
assocLR (Sy a) b c t = assocLR a b c t
-}

data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p xy -> Box p xy
  Clear :: Box p xy
  Hor :: Natty x1 -> Box p '(x1, y) -> Natty x2 -> Box p '(x2, y) -> Box p '(x1 :+ x2, y)
  Ver :: Natty y1 -> Box p '(x, y1) -> Natty y2 -> Box p '(x, y2) -> Box p '(x, y1 :+ y2)

type s :-> t = forall i. s i -> t i

ebox :: (p :-> Box q) -> Box p :-> Box q
ebox f (Stuff b) = f b
ebox f Clear = Clear
ebox f (Hor x1 l x2 r) = Hor x1 (ebox f l) x2 (ebox f r)
ebox f (Ver y1 t y2 b) = Ver y1 (ebox f t) y2 (ebox f b)

class Cut (p :: (Nat, Nat) -> *) where
  horCut :: Natty xl -> Natty xr -> p '(xl :+ xr, y) -> (p '(xl, y), p '(xr, y))
  verCut :: Natty yt -> Natty yb -> p '(x, yt :+ yb) -> (p '(x, yt), p '(x, yb))

instance Cut p => Cut (Box p) where

  horCut xl xr (Stuff p) = (Stuff pl, Stuff pr) where (pl, pr) = horCut xl xr p
  horCut xl xr Clear = (Clear, Clear)
  horCut xl xr (Hor x1 b1 x2 b2) = case cmpCuts xl xr x1 x2 of
    LTCuts z -> let (ll, lr) = horCut xl (Sy z) b1 in (ll, Hor (Sy z) lr x2 b2)
    EQCuts -> (b1, b2)
    GTCuts z -> let (rl, rr) = horCut (Sy z) xr b2 in (Hor x1 b1 (Sy z) rl, rr)
  horCut xl xr (Ver y1 tb y2 bb) = (Ver y1 tl y2 bl, Ver y1 tr y2 br)
    where (tl, tr) = horCut xl xr tb ; (bl, br) = horCut xl xr bb

  verCut yl yr (Stuff p) = (Stuff pl, Stuff pr) where (pl, pr) = verCut yl yr p
  verCut yl yr Clear = (Clear, Clear)
  verCut yl yr (Ver y1 b1 y2 b2) = case cmpCuts yl yr y1 y2 of
    LTCuts z -> let (tt, tb) = verCut yl (Sy z) b1 in (tt, Ver (Sy z) tb y2 b2)
    EQCuts -> (b1, b2)
    GTCuts z -> let (bt, bb) = verCut (Sy z) yr b2 in (Ver y1 b1 (Sy z) bt, bb)
  verCut yl yr (Hor x1 tb x2 bb) = (Hor x1 tl x2 bl, Hor x1 tr x2 br)
    where (tl, tr) = verCut yl yr tb ; (bl, br) = verCut yl yr bb

instance Cut p => Monoid (Box p xy) where
  mempty = Clear
  mappend b Clear = b
  mappend Clear b' = b'
  mappend b@(Stuff _) _ = b
  mappend (Hor x1 b1 x2 b2) b' = Hor x1 (mappend b1 b1') x2 (mappend b2 b2')
    where (b1', b2') = horCut x1 x2 b'
  mappend (Ver y1 b1 y2 b2) b' = Ver y1 (mappend b1 b1') y2 (mappend b2 b2')
    where (b1', b2') = verCut y1 y2 b'

data Vec :: Nat -> * -> * where
  V0 :: Vec Z x
  (:>) :: x -> Vec n x -> Vec (S n) x

instance Show x => Show (Vec n x) where
  show = show . foldMap (:[])

instance NATTY n => Applicative (Vec n) where
  pure = vcopies natty where
    vcopies :: forall n x.Natty n -> x -> Vec n x
    vcopies Zy x = V0
    vcopies (Sy n) x = x :> vcopies n x   
  (<*>) = vapp where
    vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
    vapp V0 V0 = V0
    vapp (f :> fs) (s :> ss) = f s :> vapp fs ss

instance Traversable (Vec n) where
  traverse f V0 = pure V0
  traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs

instance Functor (Vec n) where
  fmap = fmapDefault

instance Foldable (Vec n) where
  foldMap = foldMapDefault

vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
vappend V0 ys = ys
vappend (x :> xs) ys = x :> vappend xs ys

vchop :: Natty m -> Natty n -> Vec (m :+ n) x -> (Vec m x, Vec n x)
vchop Zy n xs = (V0, xs)
vchop (Sy m) n (x :> xs) = (x :> ys, zs) where (ys, zs) = vchop m n xs

data Matrix :: * -> (Nat, Nat) -> * where
  Mat :: Vec y (Vec x a) -> Matrix a '(x, y)

instance Cut (Matrix e) where
  horCut xl xr (Mat ess) = (Mat (fst <$> lrs), Mat (snd <$> lrs)) where
    lrs = vchop xl xr <$> ess
  verCut yt yb (Mat ess) = (Mat tess, Mat bess) where
    (tess, bess) = vchop yt yb ess
