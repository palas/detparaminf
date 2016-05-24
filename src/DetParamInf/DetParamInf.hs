{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module DetParamInf.DetParamInf (prop_no_redundant, detParamInf, detParamInfAux, prop_detParamInf_preserves) where

import Data.Hashable
import GHC.Generics (Generic)
import Control.DeepSeq
import Control.Arrow (second)
import Data.List (find, (\\), foldl1', foldl', nub, elem, null, sort, transpose, genericLength)
import Data.Maybe (fromMaybe)
import qualified DetParamInf.QKPMap as Q
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import qualified DetParamInf.DKMap as DK
import DetParamInf.TranMerge
import DetParamInf.AptaTree
import DetParamInf.ParamLang
import Test.QuickCheck


genListList :: Gen [[Int]]
genListList = listOf1 $ listOf1 $ sized (\x -> choose (1, x))

prop_exclusive_elements :: Property
prop_exclusive_elements = forAll genListList getGroupCharsWorks

getGroupCharsWorks :: (Hashable a, Ord a, Eq a, Show a) => [[a]] -> Property
getGroupCharsWorks listOfLists
    | not $ null res = forAll (elements (S.toList res)) (`isMemberInOne` listOfLists)
    | otherwise = sort (nub (flat \\ nub flat)) === sort (nub flat)
  where res = getGroupChars listOfLists
        flat = concatMap nub listOfLists

isMemberInOne :: Eq a => a -> [[a]] -> Bool
isMemberInOne el [] = False
isMemberInOne el (h:t)
 | el `elem` h = isMemberInNone el t
 | otherwise = isMemberInOne el t

isMemberInNone :: Eq a => a -> [[a]] -> Bool
isMemberInNone el = all $ notElem el

getGroupChars :: (Hashable a, Eq a, Ord a) => [[a]] -> S.HashSet a
getGroupChars groups = getGroupCharsAux groups S.empty S.empty

getGroupCharsAux [] onlyOnce severalTimes = onlyOnce
getGroupCharsAux (h:t) onlyOnce severalTimes = getGroupCharsAux t newOnlyOnce newSeveralTimes
  where (newOnlyOnce, newSeveralTimes) = getGroupCharsAux2 h S.empty onlyOnce severalTimes

getGroupCharsAux2 [] _ onlyOnce severalTimes = (onlyOnce, severalTimes)
getGroupCharsAux2 (h:t) inThis onlyOnce severalTimes
  | S.member h inThis = getGroupCharsAux2 t inThis onlyOnce severalTimes
  | otherwise = case activeFind h onlyOnce of
                  Just newOnlyOnce2 -> getGroupCharsAux2 t newInThis newOnlyOnce2 newSeveralTimes
                  Nothing -> if S.member h severalTimes
                             then getGroupCharsAux2 t newInThis onlyOnce severalTimes
                             else getGroupCharsAux2 t newInThis newOnlyOnce severalTimes
                             
  where newInThis = S.insert h inThis
        newOnlyOnce = S.insert h onlyOnce
        newSeveralTimes = S.insert h severalTimes
 
activeFind el set
  | S.member el set = Just $ S.delete el set
  | otherwise = Nothing

prop_detParamInf_preserves :: Property
prop_detParamInf_preserves = forAll genTraces detParamInfWorks

detParamInfWorks :: ParamSample -> Property
detParamInfWorks ps =
  conjoin [(pt /= []) ==> forAll (elements pt) (\pos -> acceptsTrace pos dfsm == Just True),
           (nt /= []) ==> forAll (elements nt) (\neg -> acceptsTrace neg dfsm == Just False)]
  where dfsm = detParamInf ps 
        pt = posTraces ps
        nt = negTraces ps

prop_no_redundant :: Property
prop_no_redundant = forAll genTraces noRedundant

noRedundant :: ParamSample -> Property
noRedundant ps = forAll somests $ noRedundantInApta apta
  where apta = generateApta ps
        sts = states apta
        somests = suchThat (sublistOf sts) (\x -> x /= [])

noRedundantInApta :: DFSM -> [NodeId] -> Bool
noRedundantInApta apta (h:subtest) = noRedund mres $ mergeRedundantTrans mres
  where mres = foldl' (mergeNodes h) apta subtest

noRedund :: DFSM -> DFSM -> Bool
noRedund dfsmori dfsmsim = length utrasim == length (nub utrasim) && (length utrasim <= length (nub utra))
  where tra = transitions dfsmori
        trasim = transitions dfsmsim
        utra = [(a, b, fn, par) | (a, Transition { funName = fn , params = par }, b) <- tra]
        utrasim = [(a, b, fn, par) | (a, Transition { funName = fn , params = par }, b) <- trasim]

data RDFSM = RDFSM { inStates :: S.HashSet NodeId
                   , inTransitions :: Q.QKPMap TransitionId NodeId NodeId (NodeId, Transition) (NodeId, Transition, NodeId)
                   , renamings :: M.HashMap NodeId NodeId }
  deriving (Show, Generic, NFData)

detParamInf :: ParamSample -> DFSM
detParamInf ps = mergeGenTrans $ detParamInfAux ps

detParamInfAux :: ParamSample -> DFSM
detParamInfAux ps = detParamInfMerge $ generateApta ps

detParamInfMerge :: DFSM -> DFSM
detParamInfMerge dfsm = detParamInfAux2 dfsm red
  where red = [InitialState]

detParamInfAux2 :: DFSM -> [NodeId] -> DFSM
detParamInfAux2 dfsm red = case blue of
                     [] -> dfsm
                     _ -> detParamInfAux3 dfsm red blue
  where blue = computeBlue red dfsm

toRDFSM dfsm = RDFSM { inStates = S.fromList $ states dfsm
                      , inTransitions = foldl' (flip Q.insert) emp $ transitions dfsm
                      , renamings = M.empty }

emp = Q.empty (\(_, x, _) -> [transitionId x]) (\(x, _, _) -> [x]) (\(_, _, y) -> [y]) (\(a, t, _) -> [(a, t {transitionId = 0})])

fromRDFSM RDFSM { inStates = states
                 , inTransitions = transitions
                 , renamings = renam } red = (newdfsm, newred)
  where newdfsm = DFSM { states = S.toList states
                       , transitions = Q.toList1 transitions }
        newred = applyRenamings renam red

detParamInfAux3 :: DFSM -> [NodeId] -> [NodeId] -> DFSM
detParamInfAux3 dfsm red blue = case anyNewReds candidates of
                           Just nr -> detParamInfAux2 dfsm (nr:red)
                           Nothing -> case bestCandidate of
                                        Nothing -> detParamInfAux2 dfsm (blue ++ red)
                                        Just (_, -1) -> detParamInfAux2 dfsm (blue ++ red)
                                        Just ((a, b), _) -> let (newdfsm, newred) = fromRDFSM (merge a b dfsm) (a:red) in
                                                            newdfsm `deepseq` (newred `deepseq` detParamInfAux2 newdfsm newred)
  where candidates = dfsm `deepseq` [let score = computeScore r b dfsm in
                                     score `deepseq` ((r, b), score) | r <- red, b <- blue]
        bestCandidate = maxWith (\(_, n) (_, n2) -> n < n2) candidates

anyNewReds :: [((NodeId, NodeId), Integer)] -> Maybe NodeId
anyNewReds candidates = case find (\(_, y) -> all (\((_, _), n) -> n == -1) y) gr of
                          Just (no, _) -> Just no
                          Nothing -> Nothing
  where gr = cluster (\((_, n), _) -> n) candidates

applyRenamings re [] = []
applyRenamings re (h:t) = case M.lookup h re of
                            Just h2 -> applyRenamings re (h2:t)
                            Nothing -> h:applyRenamings re t

maxWith :: (r -> r -> Bool) -> [r] -> Maybe r
maxWith _ [] = Nothing
maxWith smlr l = Just $ foldl1' (\x y -> if smlr x y then y else x) l

mergeNodes :: NodeId -> DFSM -> NodeId -> DFSM
mergeNodes h x y = simpleRenameNode y h x

simpleRenameNode :: NodeId -> NodeId -> DFSM -> DFSM
simpleRenameNode y h x = let (newdfsm, _) = fromRDFSM rdfsm [] in newdfsm
  where rdfsm = renameNode y h (toRDFSM x)

prop_mrt_noeffect_on_apta :: Property
prop_mrt_noeffect_on_apta = forAll genTraces noEffectOnApta

noEffectOnApta :: ParamSample -> Bool
noEffectOnApta ps = apta == mergeRedundantTrans apta
  where apta = generateApta ps

computeBlue :: [NodeId] -> DFSM -> [NodeId]
computeBlue st ps = S.toList $ S.difference (S.fromList [c | (a, t, c) <- tra, S.member a sts]) sts
  where sts = S.fromList st
        tra = transitions ps

merge :: NodeId -> NodeId -> DFSM -> RDFSM
merge a b fs = case res of
                  Just (_, nfs) -> nfs
  where res = computeMerge a b fs

computeScore :: NodeId -> NodeId -> DFSM -> Integer
computeScore a b fs = case res of
                         Just (n, _) -> n
                         Nothing -> -1 
  where res = computeMerge a b fs

computeMerge :: Num t => NodeId -> NodeId -> DFSM -> Maybe (t, RDFSM)
computeMerge a b fs = mergeAux [(a, b)] (toRDFSM fs) 0
 where c = min a b

mergeAux :: Num t => [(NodeId, NodeId)] -> RDFSM -> t -> Maybe (t, RDFSM)
mergeAux [] fs n = fs `deepseq` case findNonDeterminism fs of
                                      [] -> Just (n, fs)
                                      li -> let coup = couplify li in
                                            mergeAux coup fs n
mergeAux ((a, b):t) fs n
  | (a == BadState) || (b == BadState) = Nothing
  | otherwise = mrtw `deepseq` mergeAux t mrtw (n + 1)
  where mrtw = mergeRedundantTransWrapper (renameNode a b fs)
        c = min a b

couplify :: Ord t => [[t]] -> [(t, t)]
couplify = foldr ((++) . couplifyAux) []

couplifyAux :: Ord t => [t] -> [(t, t)]
couplifyAux (h:[]) = []
couplifyAux (h:h2:t)
 | h < h2 = (h2, h):couplifyAux (h:t)
 | otherwise = (h, h2):couplifyAux (h2:t)

findNonDeterminism :: RDFSM -> [[NodeId]]
findNonDeterminism dfsm = [[n | (_, _, n) <- co] | co <- col]
  where tra = inTransitions dfsm
        col = S.foldl' (\x y -> S.toList (Q.lookup4 y tra):x) [] $ Q.collisions4 tra

cluster :: (Hashable a, Hashable b, NFData a, NFData b, Ord a, Ord b) => (a -> b) -> [a] -> [(b, [a])]
cluster fu li = map (second S.toList) $ M.toList finalMap
  where finalMap = foldl' (flip (clusterAux fu)) M.empty li

clusterAux :: (Hashable k, Hashable a, NFData k, NFData a, Ord k, Ord a) => (a -> k) -> a -> M.HashMap k (S.HashSet a) -> M.HashMap k (S.HashSet a)
clusterAux fu h ma =
  let nma = (case M.lookup k ma of
               Just se -> M.insert k (S.insert h se) ma
               Nothing -> M.insert k (S.fromList [h]) ma) in nma `deepseq` nma
  where k = fu h

renameNode :: NodeId -> NodeId -> RDFSM -> RDFSM
renameNode a b r
  | a < b = renameNodeAux b a r
  | otherwise = renameNodeAux a b r

renameNodeAux :: NodeId -> NodeId -> RDFSM -> RDFSM
renameNodeAux is ds RDFSM { inStates = sts
                          , inTransitions = tra
                          , renamings = re } =
  RDFSM { inStates = S.delete is sts
        , inTransitions = ins 
        , renamings = M.insert is ds re }
    where atra = S.toList $ S.union (Q.lookup2 is tra) (Q.lookup3 is tra)
          del = foldl' (flip Q.delete) tra atra
          retra = [(renameOneNode is ds a, t, renameOneNode is ds b) | (a, t, b) <- atra]
          ins = foldl' (flip Q.insert) del retra

renameOneNode :: NodeId -> NodeId -> NodeId -> NodeId
renameOneNode is ds n
  | is == n = ds
  | otherwise = n

mergeRedundantTransWrapper :: RDFSM -> RDFSM
mergeRedundantTransWrapper rdfsm = newrdfsm { renamings = renamings rdfsm }
  where newrdfsm = toRDFSM $ mergeRedundantTrans dfsm
        (dfsm, []) = fromRDFSM rdfsm []

mergeRedundantTrans :: DFSM -> DFSM
mergeRedundantTrans d@(DFSM { transitions = tra }) =
  d { transitions = mergeRedundantTrans_aux (indexById tra) (indexInverseDeps tra) DK.empty }

mergeRedundantTrans_aux :: M.HashMap TransitionId (NodeId, Transition, NodeId) -> M.HashMap TransitionId (S.HashSet TransitionId) -> DK.DKMap TransitionId (NodeId, (String, [[ParamSrc]]), NodeId) (NodeId, Transition, NodeId) -> [(NodeId, Transition, NodeId)]
mergeRedundantTrans_aux feed iidep ibtid
  | null feed = let (_, result) = unzip $ DK.toList2 ibtid in result
  | otherwise = case DK.lookup2 (a1, (fn1, para1), c1) ibtid of
                  Just (a2, t2@( Transition { transitionId = id2 }), c2) -> let (niidep, nidtid, newrest) = removeRedirectOneTrans id2 id1 t2 iidep ibtid rest in
                                                                            mergeRedundantTrans_aux newrest niidep nidtid
                  Nothing -> mergeRedundantTrans_aux rest iidep $ DK.insert id1 (a1, (fn1, para1), c1) t1 ibtid
   where ((_, t1@(a1, Transition { transitionId = id1
                                 , funName = fn1
                                 , params = para1 }, c1)):_) = M.toList feed
         rest = M.delete id1 feed

mFindWithDefault d k m = fromMaybe d (M.lookup k m)

indexById :: [(NodeId, Transition, NodeId)] -> M.HashMap TransitionId (NodeId, Transition, NodeId)
indexById list = indexById_aux list M.empty

indexById_aux :: [(NodeId, Transition, NodeId)] -> M.HashMap TransitionId (NodeId, Transition, NodeId) -> M.HashMap TransitionId (NodeId, Transition, NodeId)
indexById_aux [] m = m
indexById_aux ((val@(_, tra, _)):rest) m = indexById_aux rest $ M.insert (transitionId tra) val m

indexInverseDeps :: [(NodeId, Transition, NodeId)] -> M.HashMap TransitionId (S.HashSet TransitionId)
indexInverseDeps l = indexInverseDeps_aux l M.empty
indexInverseDeps_aux [] m = m
indexInverseDeps_aux ((a, Transition { transitionId = tid
                                     , params = para }, c):t) m = indexInverseDeps_aux t (indexInverseDeps_aux2 tid para m)

indexInverseDeps_aux2 :: TransitionId -> [[ParamSrc]] -> M.HashMap TransitionId (S.HashSet TransitionId) -> M.HashMap TransitionId (S.HashSet TransitionId)
indexInverseDeps_aux2 _ [] m = m
indexInverseDeps_aux2 dtid ([]:t) m = indexInverseDeps_aux2 dtid t m
indexInverseDeps_aux2 dtid (((ParamSrc { srcTransition = tid }):st):t) m = indexInverseDeps_aux2 dtid t $ addToMapSet tid dtid m

addToMapSet :: (Hashable k, Hashable a, Ord k, Ord a) => k -> a -> M.HashMap k (S.HashSet a) -> M.HashMap k (S.HashSet a)
addToMapSet k v m = M.insert k (case M.lookup k m of
                                  Nothing -> S.fromList [v]
                                  Just p -> S.insert v p) m

removeRedirectOneTrans :: TransitionId -> TransitionId -> Transition
                  -> M.HashMap TransitionId (S.HashSet TransitionId)
                  -> DK.DKMap TransitionId (NodeId, (String, [[ParamSrc]]), NodeId) (NodeId, Transition, NodeId)
                  -> M.HashMap TransitionId (NodeId, Transition, NodeId)
                  -> (M.HashMap TransitionId (S.HashSet TransitionId),
                      DK.DKMap TransitionId (NodeId, (String, [[ParamSrc]]), NodeId) (NodeId, Transition, NodeId),
                      M.HashMap TransitionId (NodeId, Transition, NodeId))
removeRedirectOneTrans id1 id2 t2 iidep ibtid feed = (finaliidep, b, c)
   where revdeps = mFindWithDefault S.empty id2 iidep
         revdeplist = S.toList revdeps
         (b, c) = redirectOneTrans id1 id2 revdeplist ibtid feed
         finaliidep = addNewDeps id1 revdeps $ M.delete id2 (remTranIidep id2 iidep t2)

addNewDeps :: (Hashable k, Ord k) => k -> S.HashSet TransitionId -> M.HashMap k (S.HashSet TransitionId) -> M.HashMap k (S.HashSet TransitionId)
addNewDeps id depset m = case M.lookup id m of
                                Just s -> M.insert id (depset `S.union` s) m
                                Nothing -> M.insert id depset m

remTranIidep :: TransitionId -> M.HashMap TransitionId (S.HashSet TransitionId) -> Transition
                             -> M.HashMap TransitionId (S.HashSet TransitionId)
remTranIidep id2 iidep (Transition { funName = fn2
                                   , params = para2 }) =
       remTranIidep_aux iidep deps id2
    where deps = concat [[srcTransition para | para <- paras] | paras <- para2]

remTranIidep_aux :: M.HashMap TransitionId (S.HashSet TransitionId) -> [TransitionId]
                    -> TransitionId -> M.HashMap TransitionId (S.HashSet TransitionId)
remTranIidep_aux iidep t t2 = foldl (flip (M.adjust (S.delete t2))) iidep t

redirectOneTrans :: TransitionId -> TransitionId 
                  -> [TransitionId]
                  -> DK.DKMap TransitionId (NodeId, (String, [[ParamSrc]]), NodeId) (NodeId, Transition, NodeId)
                  -> M.HashMap TransitionId (NodeId, Transition, NodeId)
                  -> (DK.DKMap TransitionId (NodeId, (String, [[ParamSrc]]), NodeId) (NodeId, Transition, NodeId),
                      M.HashMap TransitionId (NodeId, Transition, NodeId))
redirectOneTrans id1 id2 [] idtid acc = (idtid, acc)
redirectOneTrans id1 id2 (h:t) ibtid acc =
  case DK.lookup1 h ibtid of
    Just tr -> redirectOneTrans id1 id2 t (DK.delete1 h ibtid) (M.insert h (updateTr id1 id2 tr) acc)
    Nothing -> redirectOneTrans id1 id2 t ibtid (M.adjust (updateTr id1 id2) h acc)

updateTr :: TransitionId -> TransitionId -> (NodeId, Transition, NodeId) -> (NodeId, Transition, NodeId)
updateTr id1 id2 (a, tr, b) = (a, tr { params = updateTr_aux id1 id2 (params tr) }, b)

updateTr_aux :: TransitionId -> TransitionId -> [[ParamSrc]] -> [[ParamSrc]]
updateTr_aux id1 id2 = map (updateTr_aux2 id1 id2)

updateTr_aux2 :: TransitionId -> TransitionId -> [ParamSrc] -> [ParamSrc]
updateTr_aux2 id1 id2 [] = []
updateTr_aux2 id1 id2 ((p@(ParamSrc { srcTransition = st })):t) =
  (p {srcTransition = if st == id2 then id1 else st}):updateTr_aux2 id1 id2 t


