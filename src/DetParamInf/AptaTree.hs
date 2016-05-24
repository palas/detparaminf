{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module DetParamInf.AptaTree(generateApta, DFSM(..), Transition(..), ParamSrc(..), ParamPos(..), TransitionId, NodeId(..), Id, acceptsTrace, prop_apta, randomTrace) where

import Control.Monad
import Control.Monad.ST
import System.Random
import Data.Array.ST
import Data.Maybe (isJust)
import GHC.Arr
import Data.Hashable
import Test.QuickCheck.Property
import Test.QuickCheck.Gen
import DetParamInf.ParamLang
import Data.List
import Control.Monad.Random
import GHC.Generics (Generic)
import Control.DeepSeq
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

type Id = Integer

data NodeId = InitialState | BadState | NId Id
  deriving (Eq, Show, Ord, Hashable, Generic, NFData)

type TransitionId = Id

data ParamPos = ReturnVal | ParamNum Integer
  deriving (Eq, Show, Ord, Hashable, Generic, NFData)

data ParamSrc = ParamSrc { srcTransition :: TransitionId
                         , srcParamPos :: ParamPos }
  deriving (Eq, Show, Ord, Hashable, Generic, NFData)

data Transition = Transition { transitionId :: TransitionId
                             , funName :: String
                             , params :: [[ParamSrc]] }
  deriving (Eq, Show, Ord, Hashable, Generic, NFData)

data CTransition = CTransition { cTransitionId :: TransitionId
                               , cFunName :: String
                               , cParams :: [ParamSrc] }
  deriving (Eq, Show, Ord, Hashable, Generic, NFData)

data DFSM = DFSM { states :: [NodeId]
                 , transitions :: [(NodeId, Transition, NodeId)] }
  deriving (Show, Ord, Generic, NFData)

instance Eq DFSM where
  (==) (DFSM { states = st1, transitions = tr1 }) (DFSM { states = st2, transitions = tr2 }) =
     (sort st1 == sort st2) && (sort tr1 == sort tr2)

data StData = StData { available :: M.HashMap ParamSrc [Integer]
                     , step :: Integer } deriving (Show, Generic, NFData)

randomTrace :: MonadRandom m => DFSM -> Integer -> m (Bool, ParamWord)
randomTrace apta n = do
     (st, l) <- randomTraceAux apta n [] InitialState emptyStData
     return (st /= BadState, reverse l)

randomTraceAux :: (MonadRandom m) => DFSM
     -> Integer -> ParamWord -> NodeId -> StData -> m (NodeId, ParamWord)
randomTraceAux apta n l st stdata
  | n == 0 = return (st, l)
  | otherwise = do strans <- shuffleList $ transitions apta
                   options <- foldM (\x (a, t, b) -> do issat <- satisfiable t stdata
                                                        return (if (a == st) && issat
                                                                then (a, t, b) : x
                                                                else x)) [] strans
                   case options of
                     [] -> return (st, l)
                     _ -> do let (a@(pa, pt, pb):_) = options
                             b@(inter, newst) <- interpretUpdateSt pt stdata
                             a `deepseq` b `deepseq` randomTraceAux apta (n - 1) (inter:l) pb (istep newst)

-- Based on code from wiki.haskell.org/Random_shuffle
shuffleList xs = do
    let l = length xs
    rands <- take l `fmap` getRandomRs (0, l-1)
    let ar = runSTArray $ do {
        ar <- thawSTArray $ listArray (0, l-1) xs;
        forM_ (zip [0..(l-1)] rands) $ \(i, j) -> do {
            vi <- readSTArray ar i ;
            vj <- readSTArray ar j ;
            writeSTArray ar j vi ;
            writeSTArray ar i vj } ;
        return ar }
    return (elems ar)
-- End of code from wiki.haskell.org/Random_shuffle

istep s@(StData { step = st }) = s { step = st + 1 }

emptyStData :: StData
emptyStData = StData { available = M.empty
                     , step = 0 }

satisfiable :: MonadRandom m => Transition -> StData -> m Bool
satisfiable t stdata = do res <- possibility t stdata
                          case res of
                            Just _ -> return True
                            Nothing -> return False

interpretUpdateSt :: MonadRandom m => Transition -> StData -> m (ParamCall, StData)
interpretUpdateSt pt stdata = do Just a <- possibility pt stdata
                                 return a 

chooseThis a (Left 0) = Right a
chooseThis a (Left n) = Left (n - 1)
chooseThis a (Right b) = Right b

possibility :: (MonadRandom m) => Transition -> StData -> m (Maybe (ParamCall, StData))
possibility t = possibilityAux (transitionId t) (funName t) [] (params t)

advancePossibility :: (MonadRandom m) => TransitionId -> String -> [(ParamSrc, Integer)] -> ParamSrc -> [[ParamSrc]] -> StData -> m (Maybe (ParamCall, StData))
advancePossibility tid n hist h t stdata@(StData { available = ava }) =
  case M.lookup h ava of
    Nothing -> return Nothing
    Just [] -> return Nothing
    Just ops -> do (sl:_) <- shuffleList $ elResListLazy ops
                   shortCutFoldl (\(op, resop) -> possibilityAux tid n ((ParamSrc { srcTransition = tid
                                                           , srcParamPos = ParamNum (genericLength hist) },
                                                 op):hist) t (stdata { available = M.insert h resop ava })) [sl]

possibilityAux :: (MonadRandom m) => TransitionId -> String -> [(ParamSrc, Integer)] -> [[ParamSrc]] -> StData -> m (Maybe (ParamCall, StData))
possibilityAux tid n hist [] stdata = return $ Just (PCall n onlyVals, addThis tid $ addAll stdata rhist)
  where rhist = reverse hist
        (_, onlyVals) = unzip rhist
possibilityAux tid n hist (h:t) stdata = do sl <- shuffleList h
                                            shortCutFoldl (\y -> advancePossibility tid n hist y t stdata) sl

shortCutFoldl f [] = return Nothing
shortCutFoldl f (h:t) = do r <- f h
                           case r of
                             Just res -> return $ Just res
                             Nothing -> shortCutFoldl f t


elResListLazy :: [t] -> [(t, [t])]
elResListLazy lis = elResListLazyAux lis lis 0
elResListLazyAux [] _ _ = []
elResListLazyAux (h:t) lis n = (h, remo n lis):elResListLazyAux t lis (n + 1)

remo 0 (h:t) = t
remo n (h:t) = h:remo (n - 1) t

addThis tid stdata = addAll stdata [(ParamSrc {srcTransition = tid, srcParamPos = ReturnVal},
                                     step stdata)]

addAll :: StData -> [(ParamSrc, Integer)] -> StData
addAll s [] = s 
addAll s@(StData { available = ma, step = st }) ((k, v):t) =
  addAll s { available = case M.lookup k ma of
                           Just l -> M.insert k (v:l) ma
                           Nothing -> M.insert k [v] ma
           , step = st } t

prop_apta :: Property
prop_apta = forAll genTraces aptaWorks

aptaWorks :: ParamSample -> Property
aptaWorks ps =
  conjoin [(pt /= []) ==> forAll (elements pt) (\pos -> acceptsTrace pos apta == Just True),
           (nt /= []) ==> forAll (elements nt) (\neg -> acceptsTrace neg apta == Just False)]
  where apta = generateApta ps
        pt = posTraces ps
        nt = negTraces ps

acceptsTrace :: [ParamCall] -> DFSM -> Maybe Bool
acceptsTrace tra dfsm = acceptsTraceAux tra dfsm (0, M.empty) InitialState

acceptsTraceAux :: [ParamCall] -> DFSM
                               -> (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
                               -> NodeId
                               -> Maybe Bool
acceptsTraceAux [] _ _ st
  | st == BadState = Just False
  | otherwise = Just True
acceptsTraceAux a@(PCall name par:t) dfsm past st =
  case findMatch (transitions dfsm) past st name par of
    [(newpast, (selB, selTra))] -> acceptsTraceAux t dfsm (update newpast selTra par) selB
    [] -> Nothing

update :: (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
     -> Transition
     -> [Integer]
     -> (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
update (n, m) (Transition { transitionId = id }) =
  updateAux (n, m) 0 id

updateAux :: (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
     -> Integer -> TransitionId -> [Integer] -> (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
updateAux (n, m) _ id [] = (n + 1, madd (id, ReturnVal) n m)
updateAux (n, m) c id (h:t) =
  updateAux (n, madd (id, ParamNum c) h m) (c + 1) id t

findMatch :: [(NodeId, Transition, NodeId)]
     -> (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
     -> NodeId
     -> String
     -> [Integer]
     -> [((Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer)), (NodeId, Transition))]
findMatch [] past st name par = []
findMatch ((a, tra, b):t) past st name par
  | (a == st) && (name == funName tra) && isJust matches = (newpast, (b, tra)):findMatch t past st name par
  | otherwise = findMatch t past st name par
  where matches = parMatches past tra par
        Just newpast = matches

parMatches :: (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
     -> Transition -> [Integer] -> Maybe (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
parMatches (n, m) atra = parMatchesAux (n, m) (params atra)

parMatchesAux :: (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
     -> [[ParamSrc]]
     -> [Integer]
     -> Maybe (Integer, M.HashMap (TransitionId, ParamPos) (S.HashSet Integer))
parMatchesAux (n, m) [] [] = Just (n, m)
parMatchesAux (n, m) ([]:t1) (h2:t2) = Nothing
parMatchesAux (n, m) ((h:t):t1) (h2:t2) =
  case mremove (srcTransition h, srcParamPos h) h2 m of
    Just nm -> parMatchesAux (n, nm) t1 t2
    Nothing -> parMatchesAux (n, m) (t:t1) (h2:t2) 
parMatchesAux _ _ _ = Nothing 

madd :: (Hashable k, Hashable v, Ord k, Ord v) => k -> v -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
madd k v m = M.insert k (case M.lookup k m of
                           Nothing -> S.fromList [v]
                           Just ov -> S.insert v ov) m

mremove :: (Hashable k, Hashable v, Ord k, Ord v) => k -> v -> M.HashMap k (S.HashSet v) -> Maybe (M.HashMap k (S.HashSet v))
mremove k v m = case M.lookup k m of
                  Just se -> if S.member v se
                             then Just $ M.insert k (S.delete v se) m
                             else Nothing
                  Nothing -> Nothing

generateApta :: ParamSample -> DFSM
generateApta ps = DFSM { states = InitialState:BadState:addNId [1..(snum - 1)], transitions = trans }
  where (trans, NId snum:_, _) = generateApta1 ps 0 (InitialState:addNId [1..]) [1..] M.empty

addNId :: [Id] -> [NodeId]
addNId = map NId

generateApta1 :: ParamSample -> Integer -> [NodeId] -> [TransitionId] -> M.HashMap Integer ParamSrc -> ([(NodeId, Transition, NodeId)], [NodeId], [TransitionId])
generateApta1 ps l (sn:nsn) ntn as
  | isEmpty ps = ([], nsn, ntn)
  | otherwise = (childTran, restNum, restTran)
  where (gps, bps) = splitPsNeg ps
        bgru = groups bps
        gru = groups gps
        lbgru = length bgru
        lgru = length gru
        bss = replicate lbgru BadState
        (mnum, rnum) = splitAt lgru nsn
        (mtnum, rtnum) = splitAt (lbgru + lgru) ntn
        (childTran, restNum, restTran) = agregate sn l as (bgru ++ gru) (bss ++ mnum) mtnum rnum rtnum []

agregate :: NodeId -> Integer -> M.HashMap Integer ParamSrc -> [ParamSample] -> [NodeId] -> [TransitionId] -> [NodeId] -> [TransitionId] -> [(NodeId, Transition, NodeId)] ->  ([(NodeId, Transition, NodeId)], [NodeId], [TransitionId])
agregate sn l as [] [] [] rnum rtran lst = (lst, rnum, rtran)
agregate sn l as (h:t) (n:rn) (nt:rnt) rnum rtran lst = agregate sn l as t rn rnt ornum ortran (addMaybe tran (lst ++ cTran))
  where (nas, tran, uh) = addTrans l as sn n h nt
        (cTran, ornum, ortran) = generateApta1 uh (l + 1) (n:rnum) rtran nas

addMaybe :: Maybe a -> [a] -> [a]
addMaybe Nothing l = l
addMaybe (Just x) l = x:l

isEmpty :: ParamSample -> Bool
isEmpty ps = null (posTraces ps) && null (negTraces ps)

groups :: ParamSample -> [ParamSample]
groups ps = case getFirstSymb ps of
             Nothing -> []
             Just firstSymb ->
               let (match, noMatch) = splitPsBy firstSymb ps in
               (match:groups noMatch)

splitPsBy :: ParamCall -> ParamSample -> (ParamSample, ParamSample)
splitPsBy s ps = ( ParamSample { posTraces = mpt
                               , negTraces = mnt }
                 , ParamSample { posTraces = nmpt
                               , negTraces = nmnt } )
  where mpt = [t | t@(h:_) <- posTraces ps, h == s]
        mnt = [t | t@(h:_) <- negTraces ps, h == s]
        nmpt = [t | t@(h:_) <- posTraces ps, h /= s]
        nmnt = [t | t@(h:_) <- negTraces ps, h /= s]

splitPsNeg :: ParamSample -> (ParamSample, ParamSample)
splitPsNeg ps = ( ParamSample { posTraces = mpt
                              , negTraces = mnt }
                , ParamSample { posTraces = nmpt
                              , negTraces = nmnt } )
  where mpt = posTraces ps
        mnt = [t | t@(_:_:_) <- negTraces ps]
        nmpt = []
        nmnt = [[t] | [t] <- negTraces ps]

getFirstSymb :: ParamSample -> Maybe ParamCall
getFirstSymb ps
  | pt /= [] = Just h
  | nt /= [] = Just nh
  | otherwise = Nothing
  where pt = posTraces ps
        ((h:_):_) = pt
        nt = negTraces ps
        ((nh:_):_) = nt

addTrans :: Integer -> M.HashMap Integer ParamSrc -> NodeId -> NodeId -> ParamSample -> TransitionId -> (M.HashMap Integer ParamSrc, Maybe (NodeId, Transition, NodeId), ParamSample)
-- SourceNum Num Trace
addTrans l as sn n ps nt
  | isEmpty ps = ( as, Nothing, ParamSample { posTraces = []
                                            , negTraces = [] } )
  | otherwise = ( nas, Just (sn, tra, n), nps )
  where ptt = [t | (h:t) <- posTraces ps]
        ntt = [t | (h:t) <- negTraces ps]
        tid = nt
        ((PCall name paramList:t):_) = posTraces ps ++ negTraces ps
        tra = Transition { transitionId = tid 
                         , funName = name
                         , params = [[ as M.! pl ]
                                     | pl <- paramList ] }
        nps = ParamSample { posTraces = remEmpty ptt
                          , negTraces = remEmpty ntt }
        nas = updateAs as tid l paramList 0

updateAs :: (Hashable k, Ord k) =>
     M.HashMap k ParamSrc -> TransitionId -> k -> [k] -> Integer -> M.HashMap k ParamSrc
updateAs as tid l [] p = M.insert l ParamSrc { srcTransition = tid
                                              , srcParamPos = ReturnVal } as
updateAs as tid l (h:t) p = updateAs nas tid l t (p + 1)
  where nas = M.insert h ParamSrc { srcTransition = tid
                                  , srcParamPos = ParamNum p } as

remEmpty :: [[t]] -> [[t]]
remEmpty [] = []
remEmpty ([]:t) = remEmpty t
remEmpty (h:t) = h:remEmpty t

