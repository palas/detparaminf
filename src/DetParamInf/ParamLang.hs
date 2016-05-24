{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module DetParamInf.ParamLang (ParamCall(..), ParamWord, ParamSample(..), genParamWord, genTraces) where

import Data.Hashable
import Data.List
import GHC.Generics (Generic)
import Control.DeepSeq
import Test.QuickCheck

data ParamCall = PCall String [Integer]
  deriving (Eq, Show, Ord, Generic, NFData)

type ParamWord = [ParamCall]

data ParamSample = ParamSample { posTraces :: [ParamWord]
                               , negTraces :: [ParamWord] }
  deriving (Eq, Show, Ord, Generic, NFData)

genParamCall :: Integer -> Gen ParamCall
genParamCall n = do el <- elements $ map (: []) ['a'..'c']
                    pn <- choose (0, 3)
                    li <- case n of
                            0 -> return []
                            _ -> vectorOf pn $ choose (0, n - 1)
                    return $ PCall el (nub li)

genParamWord :: Gen [ParamCall]
genParamWord = sized genParamWord1

genParamWord1 :: Int -> Gen [ParamCall]
genParamWord1 s = do ns <- choose (0, fromIntegral s `div` 4)
                     genParamWord2 ns []

genParamWord2 :: Integer -> [ParamCall] -> Gen [ParamCall]
genParamWord2 ns l
  | ns == 0 = do { w <- genParamCall 0;
                   return (w:l) }
  | otherwise = do { w <- genParamCall ns;
                     genParamWord2 (ns - 1) (w:l)}

genTraces :: Gen ParamSample
genTraces = suchThat genTraces1 (\x -> posTraces x /= [])

genTraces1 :: Gen ParamSample
genTraces1 = do tracesRaw <- listOf1 genParamWord
                let traces = cut tracesRaw
                let unique = nub traces
                piNeg <- sublistOf unique
                let neg = remSelfIncomp piNeg
                let pos = remIncomp (unique \\ neg) neg
                return ParamSample { posTraces = pos
                                   , negTraces = neg }

cut (h:_:t) = h:cut t
cut l = l

remSelfIncomp :: Eq a => [[a]] -> [[a]]
remSelfIncomp [] = []
remSelfIncomp (h:t) = remSelfIncomp1 t [h]

remSelfIncomp1 :: Eq a => [[a]] -> [[a]] -> [[a]]
remSelfIncomp1 [] l = l
remSelfIncomp1 (h:t) l
  | sharesPrefixWithAny h l = remSelfIncomp1 t l
  | otherwise = remSelfIncomp1 t (h:l)
  where sharesPrefixWith x y = isPrefixOf x y || isPrefixOf y x
        sharesPrefixWithAny x = any (sharesPrefixWith x)

remIncomp :: (Eq a, Foldable t) => [[a]] -> t [a] -> [[a]]
remIncomp pos neg = filter (\x -> not $ any (`isPrefixOf` x) neg) pos

