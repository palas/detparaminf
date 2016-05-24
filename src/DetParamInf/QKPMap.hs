{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module DetParamInf.QKPMap (QKPMap(..), empty, insert, lookup1, lookup2, lookup3, lookup4, collisions4, toList1, toList2, toList3, toList4, delete1, delete2, delete3, delete4, delete) where

import Data.Hashable
import GHC.Generics (Generic)
import Control.DeepSeq
import Data.Maybe (fromMaybe)
import qualified Data.List as L
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M

data QKPMap ka kb kc kd v = QKPMap (M.HashMap ka (S.HashSet v),
                                 M.HashMap kb (S.HashSet v),
                                 M.HashMap kc (S.HashSet v),
                                 M.HashMap kd (S.HashSet v),
                                 v -> [ka], v -> [kb], v -> [kc], v -> [kd],
                                 S.HashSet kd)
      deriving (Generic, NFData)
instance (Show v, Eq v) => Show (QKPMap ka kb kc kd v) where
    show x = "QKPMap (" ++ show (L.nub $ toList1 x ++ toList2 x ++ toList3 x) ++ ")"

updateSet [] m4 s4 = s4
updateSet (kd:t) m4 s4
  | S.size res > 1 = updateSet t m4 (S.insert kd s4)
  | otherwise = updateSet t m4 (S.delete kd s4)
  where res = mFindWithDefault S.empty kd m4

empty :: (v -> [ka]) -> (v -> [kb]) -> (v -> [kc]) -> (v -> [kd]) -> QKPMap ka kb kc kd v
empty f1 f2 f3 f4 = QKPMap (M.empty, M.empty, M.empty, M.empty, f1, f2, f3, f4, S.empty)

insert :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Hashable kd, Ord ka, Ord kb, Ord kc, Ord kd, Ord v) => v -> QKPMap ka kb kc kd v -> QKPMap ka kb kc kd v
insert v (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) =
  QKPMap (mminsertall v m1 ka,
           mminsertall v m2 kb,
           mminsertall v m3 kc,
           nm4, f1, f2, f3, f4, updateSet kd nm4 s4)
  where ka = f1 v
        kb = f2 v
        kc = f3 v
        kd = f4 v
        nm4 = mminsertall v m4 kd

mminsertall v = L.foldl' (mminsert v) 
mminsert v x y = minsert y v x

minsert :: (Hashable k, Hashable a, Ord k, Ord a) => k -> a -> M.HashMap k (S.HashSet a) -> M.HashMap k (S.HashSet a)
minsert k v m = M.insert k (case M.lookup k m of
                              Just s -> S.insert v s
                              Nothing -> S.fromList [v]) m

mFindWithDefault d k m = fromMaybe d (M.lookup k m)

lookup1 :: (Hashable ka, Ord ka) => ka -> QKPMap ka kb kc kd a -> S.HashSet a
lookup1 ka (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = mFindWithDefault S.empty ka m1

lookup2 :: (Hashable kb, Ord kb) => kb -> QKPMap ka kb kc kd a -> S.HashSet a
lookup2 kb (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = mFindWithDefault S.empty kb m2

lookup3 :: (Hashable kc, Ord kc) => kc -> QKPMap ka kb kc kd a -> S.HashSet a
lookup3 kc (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = mFindWithDefault S.empty kc m3

lookup4 :: (Hashable kd, Ord kd) => kd -> QKPMap ka kb kc kd a -> S.HashSet a
lookup4 kd (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = mFindWithDefault S.empty kd m4

collisions4 (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = s4

delete :: (Hashable ka, Hashable kb, Hashable kc, Hashable kd, Hashable v, Ord ka, Ord kb, Ord kc, Ord kd, Ord v) => v -> QKPMap ka kb kc kd v -> QKPMap ka kb kc kd v
delete v dk@(QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) =
  QKPMap ( mdeleteall v luf m1 ka
         , mdeleteall v luf m2 kb
         , mdeleteall v luf m3 kc
         , nm4 
         , f1, f2, f3, f4, updateSet kd nm4 s4 )
  where luf k m = mFindWithDefault S.empty k m
        ka = f1 v
        kb = f2 v
        kc = f3 v
        kd = f4 v
        nm4 = mdeleteall v luf m4 kd

mdeleteall :: (Hashable k, Hashable v, Ord k, Ord v) =>
   v -> (k -> M.HashMap k (S.HashSet v) -> S.HashSet v) -> M.HashMap k (S.HashSet v) -> [k] -> M.HashMap k (S.HashSet v)
mdeleteall v luf = L.foldl' (\x y -> M.insert y (S.delete v (luf y x)) x)

toList1 :: QKPMap ka kb kc kd v-> [v]
toList1 (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m1

toList2 :: QKPMap ka kb kc kd v-> [v]
toList2 (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m2

toList3 :: QKPMap ka kb kc kd v-> [v]
toList3 (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m3

toList4 :: QKPMap ka kb kc kd v-> [v]
toList4 (QKPMap (m1, m2, m3, m4, f1, f2, f3, f4, s4)) = res
  where res = concatMap S.toList tmp
        (_, tmp) = unzip $ M.toList m4

delete1 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Hashable kd, Ord v, Ord ka, Ord kb, Ord kc, Ord kd) => ka -> QKPMap ka kb kc kd v -> QKPMap ka kb kc kd v
delete1 ka dk = S.foldl' (flip delete) dk (lookup1 ka dk)

delete2 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Hashable kd, Ord v, Ord ka, Ord kb, Ord kc, Ord kd) => kb -> QKPMap ka kb kc kd v -> QKPMap ka kb kc kd v
delete2 kb dk = S.foldl' (flip delete) dk (lookup2 kb dk)

delete3 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Hashable kd, Ord v, Ord ka, Ord kb, Ord kc, Ord kd) => kc -> QKPMap ka kb kc kd v -> QKPMap ka kb kc kd v
delete3 kc dk = S.foldl' (flip delete) dk (lookup3 kc dk)

delete4 :: (Hashable v, Hashable ka, Hashable kb, Hashable kc, Hashable kd, Ord v, Ord ka, Ord kb, Ord kc, Ord kd) => kd -> QKPMap ka kb kc kd v -> QKPMap ka kb kc kd v
delete4 kd dk = S.foldl' (flip delete) dk (lookup4 kd dk)


