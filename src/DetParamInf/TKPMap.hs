{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module DetParamInf.TKPMap (TKPMap(..), empty, insert, lookup1, lookup2, lookup3, toList1, toList2, toList3, delete1, delete2, delete3, delete) where

import Data.Hashable
import GHC.Generics (Generic)
import Control.DeepSeq
import Data.Maybe (fromMaybe)
import qualified Data.List as L
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M

data TKPMap ka kb kc v = TKPMap (M.HashMap ka (S.HashSet v),
                                 M.HashMap kb (S.HashSet v),
                                 M.HashMap kc (S.HashSet v),
                                 v -> [ka], v -> [kb], v -> [kc])
      deriving (Generic, NFData)
instance (Show v, Eq v) => Show (TKPMap ka kb kc v) where
    show x = "TKPMap (" ++ show (L.nub $ toList1 x ++ toList2 x ++ toList3 x) ++ ")"

empty :: (v -> [ka]) -> (v -> [kb]) -> (v -> [kc]) -> TKPMap ka kb kc v
empty f1 f2 f3 = TKPMap (M.empty, M.empty, M.empty, f1, f2, f3)

insert :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Ord ka, Ord kb, Ord kc, Ord v) => v -> TKPMap ka kb kc v -> TKPMap ka kb kc v
insert v (TKPMap (m1, m2, m3, f1, f2, f3)) =
  TKPMap (mminsertall v m1 ka,
          mminsertall v m2 kb,
          mminsertall v m3 kc, f1, f2, f3)
  where ka = f1 v
        kb = f2 v
        kc = f3 v

mminsertall v = L.foldl' (mminsert v) 
mminsert v x y = minsert y v x

minsert :: (Hashable k, Hashable a, Ord k, Ord a) => k -> a -> M.HashMap k (S.HashSet a) -> M.HashMap k (S.HashSet a)
minsert k v m = M.insert k (case M.lookup k m of
                              Just s -> S.insert v s
                              Nothing -> S.fromList [v]) m

mFindWithDefault d k m = fromMaybe d (M.lookup k m)

lookup1 :: (Hashable ka, Ord ka) => ka -> TKPMap ka kb kc a -> S.HashSet a
lookup1 ka (TKPMap (m1, m2, m3, f1, f2, f3)) = mFindWithDefault S.empty ka m1

lookup2 :: (Hashable kb, Ord kb) => kb -> TKPMap ka kb kc a -> S.HashSet a
lookup2 kb (TKPMap (m1, m2, m3, f1, f2, f3)) = mFindWithDefault S.empty kb m2

lookup3 :: (Hashable kc, Ord kc) => kc -> TKPMap ka kb kc a -> S.HashSet a
lookup3 kc (TKPMap (m1, m2, m3, f1, f2, f3)) = mFindWithDefault S.empty kc m3

delete :: (Hashable ka, Hashable kb, Hashable kc, Hashable v, Ord ka, Ord kb, Ord kc, Ord v) => v -> TKPMap ka kb kc v -> TKPMap ka kb kc v
delete v dk@(TKPMap (m1, m2, m3, f1, f2, f3)) =
  TKPMap ( mdeleteall v luf m1 ka
         , mdeleteall v luf m2 kb
         , mdeleteall v luf m3 kc
         , f1, f2, f3 )
  where luf k m = mFindWithDefault S.empty k m
        ka = f1 v
        kb = f2 v
        kc = f3 v

mdeleteall :: (Hashable k, Hashable v, Ord k, Ord v) =>
   v -> (k -> M.HashMap k (S.HashSet v) -> S.HashSet v) -> M.HashMap k (S.HashSet v) -> [k] -> M.HashMap k (S.HashSet v)
mdeleteall v luf = L.foldl' (\x y -> M.insert y (S.delete v (luf y x)) x)

toList1 :: TKPMap t t1 t2 v-> [v]
toList1 (TKPMap (m1, m2, m3, f1, f2, f3)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m1

toList2 :: TKPMap t t1 t2 v-> [v]
toList2 (TKPMap (m1, m2, m3, f1, f2, f3)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m2

toList3 :: TKPMap t t1 t2 v-> [v]
toList3 (TKPMap (m1, m2, m3, f1, f2, f3)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m3

delete1 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Ord v, Ord ka, Ord kb, Ord kc) => ka -> TKPMap ka kb kc v -> TKPMap ka kb kc v
delete1 ka dk = S.foldl' (flip delete) dk (lookup1 ka dk)

delete2 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Ord v, Ord ka, Ord kb, Ord kc) => kb -> TKPMap ka kb kc v -> TKPMap ka kb kc v
delete2 kb dk = S.foldl' (flip delete) dk (lookup2 kb dk)

delete3 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Ord v, Ord ka, Ord kb, Ord kc) => kc -> TKPMap ka kb kc v -> TKPMap ka kb kc v
delete3 kc dk = S.foldl' (flip delete) dk (lookup3 kc dk)

