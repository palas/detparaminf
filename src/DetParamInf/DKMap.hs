module DetParamInf.DKMap (DKMap(..), empty, insert, lookup1, lookup2, toList1, toList2, delete1, delete2) where

import Data.Hashable
import qualified Data.HashMap.Strict as M

data DKMap ka kb v = DKMap (M.HashMap ka (v, kb), M.HashMap kb (v, ka))
  deriving (Eq, Show)

empty :: DKMap ka kb v
empty = DKMap (M.empty, M.empty)

insert :: (Hashable ka, Hashable kb, Ord ka, Ord kb) => ka -> kb -> v -> DKMap ka kb v -> DKMap ka kb v
insert ka kb v (DKMap (m1, m2)) = DKMap (M.insert ka (v, kb) m1, M.insert kb (v, ka) m2)

lookup1 :: (Hashable ka, Ord ka) => ka -> DKMap ka kb a -> Maybe a
lookup1 ka (DKMap (m1, m2)) = case M.lookup ka m1 of
                                Just (v, _) -> Just v
                                Nothing -> Nothing

lookup2 :: (Hashable kb, Ord kb) => kb -> DKMap ka kb a -> Maybe a
lookup2 kb (DKMap (m1, m2)) = case M.lookup kb m2 of
                                Just (v, _) -> Just v
                                Nothing -> Nothing

toList1 :: DKMap ka kb v -> [(ka, v)]
toList1 (DKMap (m1, m2)) = zip k v
  where (k, vb) = unzip $ M.toList m1
        (v, b) = unzip vb

toList2 :: DKMap ka kb v -> [(kb, v)]
toList2 (DKMap (m1, m2)) = zip k v
  where (k, va) = unzip $ M.toList m2
        (v, a) = unzip va

delete1 :: (Hashable ka, Hashable kb, Ord ka, Ord kb) => ka -> DKMap ka kb v -> DKMap ka kb v
delete1 ka dk@(DKMap (m1, m2)) =
  case M.lookup ka m1 of
    Nothing -> dk
    Just (_, kb) -> DKMap (M.delete ka m1, M.delete kb m2)

delete2 :: (Hashable ka, Hashable kb, Ord ka, Ord kb) => kb -> DKMap ka kb v -> DKMap ka kb v
delete2 kb dk@(DKMap (m1, m2)) =
  case M.lookup kb m2 of
    Nothing -> dk
    Just (_, ka) -> DKMap (M.delete ka m1, M.delete kb m2)

