module DetParamInf.TranMerge (mergeGenTrans) where

import Data.Hashable
import DetParamInf.AptaTree
import DetParamInf.ParamLang
import Test.QuickCheck
import Data.List ((\\), foldl1', foldl', nub, elem, null, sort, transpose, genericLength, find)
import qualified Data.Foldable as F
import qualified Data.Sequence as Q
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Maybe (catMaybes)
import qualified DetParamInf.TKPMap as T

mergeGenTrans :: DFSM -> DFSM
mergeGenTrans dfsm = dfsm { transitions = T.toList1 (mergeProcess idxTrans) }
  where 
        tra = transitions dfsm
        idxTrans = idxTran tra

idxTran :: [(NodeId, Transition, NodeId)]
   -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
idxTran = foldl' (flip T.insert) idxTranBase
 where idxTranBase = T.empty (\(_, x, _) -> [transitionId x]) deps (\x -> [bigGroup x])

deps :: (NodeId, Transition, NodeId) -> [TransitionId]
deps (_, t, _) = nub (concat [[srcTransition p1 | p1 <- p2] | p2 <- params t])

bigGroup :: (NodeId, Transition, NodeId) -> (NodeId, String, Integer)
bigGroup (x, t, _) = (x, funName t, genericLength $ params t)

mergeProcess :: T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
   -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
mergeProcess idxTrans 
  | modified = mergeProcess newIdxTrans
  | otherwise = newIdxTrans
  where rootTransitions = [toTid a | a <- T.toList1 idxTrans, null $ deps a]
        (modified, newIdxTrans) = mergeProcessAux False idxTrans (Q.fromList rootTransitions, S.empty)

mergeProcessAux :: Bool
  -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
  -> (Q.Seq TransitionId, S.HashSet TransitionId)
  -> (Bool, T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId))
mergeProcessAux modified idxTrans (queue, se)
  | Q.null queue = (modified, idxTrans)
  | otherwise = case res of
                  Just (h2, newIdxTrans) -> mergeProcessAux True newIdxTrans (addToQueue (st, se) newIdxTrans h2)
                  Nothing -> mergeProcessAux modified idxTrans (addToQueue (st, se) idxTrans h)
  where (sh, st) = Q.splitAt 1 queue
        [h] = F.toList sh
        res = if exists h idxTrans
              then getMergeable h idxTrans
              else Nothing

exists h idxTrans = not $ S.null $ T.lookup1 h idxTrans

addToQueue (queue, se) idxTrans traId = (queue Q.><  Q.fromList invDepsTids, se `S.union` S.fromList invDepsTids)
  where invDeps = S.toList $ T.lookup2 traId idxTrans
        invDepsTids = [transitionId x | (_, x, _) <- invDeps, not $ S.member (transitionId x) se]

mergeTrans :: TransitionId
  -> TransitionId
  -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
  -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
mergeTrans oriId destId idxTrans = insert2IdxTrans
  where idxTransUpdated = S.foldl' (\itr t -> updateRef itr oriId destId $ toTid t) idxTrans (T.lookup2 oriId idxTrans)
        deleteIdxTrans = T.delete1 oriId idxTransUpdated
        delete2IdxTrans = T.delete1 destId deleteIdxTrans
        insert2IdxTrans = T.insert (a, mergedTran, b) delete2IdxTrans
        mergedTran = dest { params = mergePars (params ori) (params dest) }
        [(_, ori, _)] = S.toList $ T.lookup1 oriId idxTransUpdated
        [(a, dest, b)] = S.toList $ T.lookup1 destId deleteIdxTrans

toTid :: (NodeId, Transition, NodeId) -> TransitionId
toTid (_, t, _) = transitionId t

updateRef :: T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
  -> TransitionId
  -> TransitionId
  -> TransitionId
  -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
updateRef idx oriId destId tid = insIdx
  where [tra] = S.toList $ T.lookup1 tid idx
        delIdx = T.delete1 tid idx
        insIdx = T.insert (renameInTrans oriId destId tra) delIdx

renameInTrans :: TransitionId -> TransitionId -> (NodeId, Transition, NodeId) -> (NodeId, Transition, NodeId)
renameInTrans oriId destId (a, trans@(Transition {params = p}), b) =
  (a, trans {params = [[p2 { srcTransition = if tra == oriId then destId else tra }
                        | p2@(ParamSrc { srcTransition = tra }) <- p1]
                       | p1 <- p]}, b)
 
mergePars :: (Eq a) => [[a]] -> [[a]] -> [[a]]
mergePars [] [] = []
mergePars (h1:t1) (h2:t2) = nub (h1 ++ h2):mergePars t1 t2

getMergeable :: TransitionId
  -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
  -> Maybe (TransitionId, T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId))
getMergeable tid idxTrans = shortCutFoldl (solveMerge tid idxTrans) res
  where res = map (\(_, tra, _) -> transitionId tra) $ filter (suitable idxTrans thistra) bg 
        bg = getBg tid idxTrans
        thistra = goodLookup idxTrans tid
        extractDest (_, _, x) = x 

shortCutFoldl :: (a -> Maybe b) -> [a] -> Maybe b
shortCutFoldl f [] = Nothing
shortCutFoldl f (h:t) = case f h of
                          Just res -> Just res
                          Nothing -> shortCutFoldl f t

solveMerge :: TransitionId -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
     -> TransitionId
     -> Maybe (TransitionId, T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId))
solveMerge h1 idxTrans h2 = case solveNonDeterminisms mergeResult nonDeterministic of
                              Just newIdxTrans -> Just (h2, newIdxTrans)
                              Nothing -> Nothing
  where nonDeterministic = nonDeterminisms h2 mergeResult
        mergeResult = mergeTrans h1 h2 idxTrans

solveNonDeterminisms :: T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
     -> [(TransitionId, TransitionId)]
     -> Maybe (T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId))
solveNonDeterminisms idxTrans [] = Just idxTrans
solveNonDeterminisms idxTrans l@((a, b):t)
  | not (exists a idxTrans && exists b idxTrans) = solveNonDeterminisms idxTrans t
  | otherwise = if suitable idxTrans tra1 tra2
                then remFirst $ solveMerge a idxTrans b
                else Nothing
  where tra1 = goodLookup idxTrans a
        tra2 = goodLookup idxTrans b 

remFirst :: Maybe (a, b) -> Maybe b
remFirst (Just (_, b)) = Just b
remFirst Nothing = Nothing

goodLookup :: (Ord ka, Hashable ka) => T.TKPMap ka kb kc v -> ka -> v
goodLookup idxTrans tid = tra
  where [tra] = S.toList $ T.lookup1 tid idxTrans

getBg :: TransitionId -> T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
     -> [(NodeId, Transition, NodeId)]
getBg tid idxTrans = S.toList $ T.lookup3 (bigGroup $ goodLookup idxTrans tid) idxTrans

computeSe :: [(NodeId, Transition, NodeId)] -> [S.HashSet ParamSrc]
computeSe bg = map getGroupChars $ transpose $ map ((map concat . transpose) . map (\ (_, x, _) -> params x)) gtrans 
  where gtrans = groupBy (\(_, _, x) -> x) bg

suitable :: T.TKPMap TransitionId TransitionId (NodeId, String, Integer) (NodeId, Transition, NodeId)
  -> (NodeId, Transition, NodeId) -> (NodeId, Transition, NodeId) -> Bool
suitable idxTrans a@(oria, ta, desa) b@(orib, tb, desb) = (bg1 == bg2) && (desa == desb) && (ta /= tb) && unique
  where unique = any (\(sse, pars) -> all (`S.member` sse) pars) $ zip se $ zipWith (++) p1 p2
        tid1 = transitionId ta
        tid2 = transitionId tb
        f1 = funName ta
        f2 = funName tb
        p1 = params ta
        p2 = params tb
        se = computeSe ((oria, ta {params = zipWith (++) p1 p2}, desa):(bg1 \\ [a, b]))
        bg1 = getBg tid1 idxTrans
        bg2 = getBg tid2 idxTrans

nonDeterminisms :: TransitionId -> T.TKPMap ka TransitionId kc (NodeId, Transition, NodeId) -> [(TransitionId, TransitionId)]
nonDeterminisms tid idxTrans = concat [conflict t m | t@(a, tin, b) <- T.toList1 idxTrans]
  where m = mfromList li 
        li = [(bigGroup t2, t2) | t2@(_, tt2, _) <- T.toList1 idxTrans] -- this does not work: (S.toList $ T.lookup2 tid idxTrans)] why?

mfromList :: (Eq k, Hashable k) => [(k, v)] -> M.HashMap k [v]
mfromList li = mfromListA li M.empty

mfromListA :: (Eq k, Hashable k) => [(k, v)] -> M.HashMap k [v] -> M.HashMap k [v]
mfromListA [] ma = ma
mfromListA ((k,v):t) ma = mfromListA t (mfromListIns k v ma)

mfromListIns :: (Eq k, Hashable k) => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
mfromListIns k v ma = M.insert k (case M.lookup k ma of
                                    Just x -> v:x
                                    Nothing -> [v]) ma

conflict :: (NodeId, Transition, NodeId) -> M.HashMap (NodeId, String, Integer) [(NodeId, Transition, NodeId)]
    -> [(TransitionId, TransitionId)]
conflict t@(_, tra, _) m =
  case M.lookup (bigGroup t) m of
    Nothing -> [] 
    Just lis -> catMaybes [if checkParams (params tra) (params t2) &&
                                (transitionId tra /= transitionId t2)
                             then Just (transitionId tra, transitionId t2)
                             else Nothing
                           | gt@(_, t2, _) <- lis]

checkParams :: [[ParamSrc]] -> [[ParamSrc]] -> Bool
checkParams [] [] = True
checkParams (h:t) (h2:t2) = any (`elem` h2) h && checkParams t t2

justToTid :: Maybe (NodeId, Transition, NodeId) -> Maybe TransitionId
justToTid (Just (_, t, _)) = Just $ transitionId t
justToTid Nothing = Nothing

groupBy :: (Hashable a, Hashable b, Ord a, Ord b) => (a -> b) -> [a] -> [[a]]
groupBy f l = map S.toList res
 where (_,res) = unzip $ M.toList $ groupByAux l f M.empty

groupByAux :: (Hashable k, Hashable v, Ord k, Ord v) => [v] -> (v -> k) -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
groupByAux [] f m = m
groupByAux (h:t) f m = groupByAux t f $ minsert (f h) h m

minsert :: (Hashable k, Hashable v, Ord k, Ord v) => k -> v -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
minsert k v m = M.insert k (case M.lookup k m of
                              Nothing -> S.fromList [v]
                              Just l -> S.insert v l) m

-- Property

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
isMemberInNone el = all (notElem el)

getGroupChars :: (Hashable a, Eq a, Ord a) => [[a]] -> S.HashSet a
getGroupChars groups = getGroupCharsAux groups S.empty S.empty

getGroupCharsAux :: (Eq a, Hashable a) => [[a]] -> S.HashSet a -> S.HashSet a -> S.HashSet a
getGroupCharsAux [] onlyOnce severalTimes = onlyOnce
getGroupCharsAux (h:t) onlyOnce severalTimes = getGroupCharsAux t newOnlyOnce newSeveralTimes
  where (newOnlyOnce, newSeveralTimes) = getGroupCharsAux2 h S.empty onlyOnce severalTimes

getGroupCharsAux2 :: (Eq a, Hashable a) => [a]
     -> S.HashSet a -> S.HashSet a -> S.HashSet a -> (S.HashSet a, S.HashSet a)
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

activeFind :: (Eq v, Hashable v) => v -> S.HashSet v -> Maybe (S.HashSet v)
activeFind el set
  | S.member el set = Just $ S.delete el set
  | otherwise = Nothing

