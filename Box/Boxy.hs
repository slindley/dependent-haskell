-- experimenting with replacing Hor and Ver with a single Jux constructor

{-# LANGUAGE
    DataKinds, PolyKinds, TypeFamilies,
    RankNTypes, GADTs, TypeOperators, FlexibleInstances #-}

module Boxy where

import Data.Monoid
import Control.Applicative
import Data.Foldable

import Nat
import Vec

     
-- data Foo (z :: Nat) (m :: Nat) (s :: (Nat, Nat)) :: * where
--   Ho :: Foo z m '(m, z)
--   Ve :: Foo z m '(z, m)

-- data EBox :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
--   EStuff :: p wh -> EBox p wh
--   EClear :: EBox p wh
--   EHor :: Natty w1 -> EBox p '(w1, h) -> Natty w2 -> EBox p '(w2, h) -> EBox p '(w1 :+ w2, h)
--   EVer :: Natty h1 -> EBox p '(w, h1) -> Natty h2 -> EBox p '(w, h2) -> EBox p '(w, h1 :+ h2)

-- class Foo (d :: Dimension) where
--   type Bar (d :: Dimension) (m :: Nat) (n :: Nat) :: (Nat, Nat)
--
-- instance Foo Hor where
--   type Bar Hor m n = '(m, n)
--
-- instance Foo Ver where
--   type Bar Ver m n = '(n, m)

-- data EqDim (d :: Dimension) (d' :: Dimension) :: * where
--   EqDim :: SDimension d -> EqDim d d

-- eqDim :: SDimension d -> SDimension d' -> Maybe (EqDim d d')
-- eqDim SHor SHor = Just (EqDim SHor)
-- eqDim SHor SVer = Nothing
-- eqDim SVer SHor = Nothing
-- eqDim SVer SVer = Just (EqDim SVer)


data Dimension = Hor | Ver
  deriving (Show, Eq)

data SDimension :: Dimension -> * where
  SHor :: SDimension Hor
  SVer :: SDimension Ver

type family Comp (z :: Nat) (d :: Dimension) (m :: Nat) :: (Nat, Nat)
type instance Comp z Hor m = '(m, z)
type instance Comp z Ver m = '(z, m) 


data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p wh -> Box p wh
  Clear :: Box p wh
  Jux :: Natty z -> SDimension d ->
         Natty m -> Box p (Comp z d m) ->
         Natty n -> Box p (Comp z d n) -> Box p (Comp z d (m :+ n))
--   Hor :: Natty w1 -> Box p '(w1, h) -> Natty w2 -> Box p '(w2, h) -> Box p '(w1 :+ w2, h)
--   Ver :: Natty h1 -> Box p '(w, h1) -> Natty h2 -> Box p '(w, h2) -> Box p '(w, h1 :+ h2)

type s :-> t = forall i. s i -> t i

ebox :: (p :-> Box q) -> Box p :-> Box q
ebox f (Stuff c)             = f c
ebox f Clear                 = Clear
ebox f (Jux z d m1 b1 m2 b2) = Jux z d m1 (ebox f b1) m2 (ebox f b2)

class Cut (p :: (Nat, Nat) -> *) where
  cut :: Natty z -> SDimension d -> Natty m -> Natty n -> p (Comp z d (m :+ n)) -> (p (Comp z d m), p (Comp z d n))

-- equal dimensions
cutEq :: (Cut p, (m :+ n) ~ (w1 :+ w2)) =>
           Natty r -> SDimension d ->
             Natty m -> Natty n ->
               Natty w1 -> Box p (Comp r d w1) ->
               Natty w2 -> Box p (Comp r d w2) ->
                 (Box p (Comp r d m), Box p (Comp r d n))
cutEq r d m n w1 b1 w2 b2 =
  case cmpCuts m n w1 w2 of
    LTCuts z  ->  let (b11, b12) = cut r d m (SS z) b1
                  in (b11, Jux r d (SS z) b12 w2 b2)
    EQCuts    ->  (b1, b2)
    GTCuts z  ->  let (b21, b22) = cut r d (SS z) n b2
                  in (Jux r d w1 b1 (SS z) b21, b22)

-- unequal dimensions
cutNeq d d' m n h1 b1 h2 b2 =
  (Jux m d' h1 b11 h2 b21, Jux n d' h1 b12 h2 b22)
  where (b11, b12) = cut h1 d m n b1
        (b21, b22) = cut h2 d m n b2

instance Cut p => Cut (Box p) where
  cut r d m n (Stuff p) = (Stuff p1, Stuff p2)  
    where (p1, p2) = cut r d m n p
  cut r d m n Clear = (Clear, Clear)
  cut r d m n (Jux _ d' w1 b1 w2 b2) =
    case (d, d') of
      (SHor, SHor) -> cutEq r SHor m n w1 b1 w2 b2
      (SHor, SVer) -> cutNeq SHor SVer m n w1 b1 w2 b2
      (SVer, SHor) -> cutNeq SVer SHor m n w1 b1 w2 b2
      (SVer, SVer) -> cutEq r SVer m n w1 b1 w2 b2


join' ::
  (Comp h1 d w1 ~ Comp w1 d' h1,
   Comp h1 d w2 ~ Comp w2 d' h1,
   Comp h2 d w1 ~ Comp w1 d' h2,
   Comp h2 d w2 ~ Comp w2 d' h2) =>
     SDimension d -> SDimension d' ->
       Natty w1 -> Natty h1 ->
         Natty w2 -> Natty h2 ->
           Box p (Comp h1 d w1) -> Box p (Comp h2 d w2) ->
             Box p (Comp (Max h1 h2) d (w1 :+ w2))
join' d d' w1 h1 w2 h2 b1 b2 =
  case cmp h1 h2 of
    LTNat n -> Jux (maxn h1 h2) d w1 (Jux w1 d' h1 b1 (SS n) Clear) w2 b2
    EQNat   -> Jux (maxn h1 h2) d w1 b1 w2 b2
    GTNat n -> Jux (maxn h1 h2) d w1 b1 w2 (Jux w2 d' h2 b2 (SS n) Clear)


-- place boxes next to each other
joinD :: SDimension d ->
           (Natty w1, Natty h1) ->
             (Natty w2, Natty h2) ->
               Box p (Comp h1 d w1) -> Box p (Comp h2 d w2) ->
                 Box p (Comp (Max h1 h2) d (w1 :+ w2))
joinD d (w1, h1) (w2, h2) b1 b2 =
  case d of
    SHor -> join' SHor SVer w1 h1 w2 h2 b1 b2
    SVer -> join' SVer SHor w1 h1 w2 h2 b1 b2


-- instance Cut p => Monoid (Box p wh) where
--   mempty = Clear
--   mappend b Clear = b
--   mappend Clear b' = b'
--   mappend b@(Stuff _) _ = b
--   mappend (Hor w1 b1 w2 b2) b' = Hor w1 (mappend b1 b1') w2 (mappend b2 b2')
--     where (b1', b2') = horCut w1 w2 b'
--   mappend (Ver h1 b1 h2 b2) b' = Ver h1 (mappend b1 b1') h2 (mappend b2 b2')
--     where (b1', b2') = verCut h1 h2 b'

-- data Matrix :: * -> (Nat, Nat) -> * where
--   Mat :: Vec y (Vec x a) -> Matrix a '(x, y)

-- instance Show a => Show (Matrix a '(x, y)) where
--   show = show . (foldMap ((:[]) . foldMap (:[]))) . unMat

-- unMat :: Matrix a '(x,y) -> Vec y (Vec x a)
-- unMat (Mat m) = m

-- instance Cut (Matrix e) where
--   horCut m n (Mat ess) =
--     (Mat (fst <$> ps), Mat (snd <$> ps)) where
--       ps = vchop m n <$> ess
--   verCut m n (Mat ess) = (Mat tess, Mat bess) where
--     (tess, bess) = vchop m n ess 

-- {- smart constructors for clear boxes -}
clear :: (Natty w, Natty h) -> Box p '(w, h)
clear (x, y) = Clear

-- emptyBox :: Box p '(Z, Z)
-- emptyBox = Clear

-- hGap :: Natty w -> Box p '(w, Z)
-- hGap _ = Clear

-- vGap :: Natty h -> Box p '(Z, h)
-- vGap _ = Clear

-- {- placing boxes -}

-- {-
-- --- lemmas about max ---

-- -- we wire this knowledge into the Cmp datatype

-- maxAddR :: forall x y z t.Natty x -> Natty y -> ((Max x (x :+ S y) ~ (x :+ S y)) => t) -> t
-- maxAddR SZ     y t = t
-- maxAddR (SS x) y t = maxAddR x y t

-- maxAddL :: forall x y z t.Natty x -> Natty y -> ((Max (x :+ S y) x ~ (x :+ S y)) => t) -> t
-- maxAddL x y t = maxAddR x y (maxSym x (x /+/ SS y) t)

-- maxRefl :: forall x y t.Natty x -> ((Max x x ~ x) => t) -> t
-- maxRefl SZ     t = t
-- maxRefl (SS x) t = maxRefl x t

-- maxSym :: forall x y t.Natty x -> Natty y -> ((Max x y ~ Max y x) => t) -> t
-- maxSym SZ SZ         t = t
-- maxSym SZ (SS y)     t = t
-- maxSym (SS x) SZ     t = t
-- maxSym (SS x) (SS y) t = maxSym x y t
-- ------------------------
-- -}

-- -- place boxes horizontally
-- joinH :: (Natty w1, Natty h1) -> (Natty w2, Natty h2) ->
--             Box p '(w1, h1) -> Box p '(w2, h2) -> Box p '(w1 :+ w2, Max h1 h2)
-- joinH (w1, h1) (w2, h2) b1 b2 =
--   case cmp h1 h2 of
--     LTNat n -> Hor w1 (Ver h1 b1 (SS n) (clear (w1, SS n))) w2 b2
--     EQNat    -> Hor w1 b1 w2 b2
--     GTNat n -> Hor w1 b1 w2 (Ver h2 b2 (SS n) (clear (w2, SS n)))

-- -- place boxes vertically
-- joinV :: (Natty w1, Natty h1) -> (Natty w2, Natty h2) ->
--             Box p '(w1, h1) -> Box p '(w2, h2) -> Box p '(Max w1 w2, h1 :+ h2)
-- joinV (w1, h1) (w2, h2) b1 b2 =
--   case cmp w1 w2 of
--     LTNat n -> Ver h1 (Hor w1 b1 (SS n) (clear (SS n, h1))) h2 b2
--     EQNat   -> Ver h1 b1 h2 b2
--     GTNat n -> Ver h1 b1 h2 (Hor w2 b2 (SS n) (clear (SS n, h2)))

-- {- cropping -}
-- type Size w h = (Natty w, Natty h)
-- type Point x y = (Natty x, Natty y)

-- type Region x y w h = (Point x y, Size w h)

-- crop :: Cut p => Region x y w h -> Size s t -> Box p '(s, t) -> Box p '(w, h)
-- crop ((x, y), (w, h)) (s, t) b =
--   fit (s /-/ x, t /-/ y) (w, h) (clip (s, t) (x, y) b)

-- clip :: Cut p => Size w h -> Point x y -> Box p '(w, h) -> Box p '(w :- x, h :- y)
-- clip (w, h) (x, y) b = clipV (w /-/ x, h) y (clipH (w, h) x b)

-- clipH :: Cut p => Size w h -> Natty x -> Box p '(w, h) -> Box p '(w :- x, h)
-- clipH (w, h) x b =
--   case cmp w x of
--     GTNat d -> snd (horCut x (SS d) b)
--     _       -> Clear

-- clipV :: Cut p => Size w h -> Natty y -> Box p '(w, h) -> Box p '(w, h :- y)
-- clipV (w, h) y b =
--   case cmp h y of
--     GTNat d -> snd (verCut y (SS d) b)
--     _       -> Clear

-- fit :: Cut p => Size w1 h1 -> Size w2 h2 -> Box p '(w1, h1) -> Box p '(w2, h2)
-- fit (w1, h1) (w2, h2) b = fitV h1 h2 (fitH w1 w2 b)

-- fitH :: Cut p => Natty w1 -> Natty w2 -> Box p '(w1, h) -> Box p '(w2, h)
-- fitH w1 w2 b =
--   case cmp w1 w2 of
--     LTNat d -> Hor w1 b (SS d) Clear
--     EQNat   -> b
--     GTNat d -> fst (horCut w2 (SS d) b)

-- fitV :: Cut p => Natty h1 -> Natty h2 -> Box p '(w, h1) -> Box p '(w, h2)
-- fitV h1 h2 b =
--   case cmp h1 h2 of
--     LTNat d -> Ver h1 b (SS d) Clear
--     EQNat   -> b
--     GTNat d -> fst (verCut h2 (SS d) b)
