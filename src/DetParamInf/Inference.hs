module DetParamInf.Inference (socketFun, inferFun, inferFunIO, classify, door, freqServerUTL, freqServerUniqueP, freqServer, freqServerP) where

import Control.Exception as E
import System.IO
import DetParamInf.ParamLang
import DetParamInf.AptaTree
import DetParamInf.DetParamInf
import DetParamInf.DFSMVisualise
import Control.Monad.Random
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.List
import Control.DeepSeq (rnf)
import Network.Socket hiding (send, sendTo, recv, recvFrom)
import Network.Socket.ByteString (send, recv)
import qualified Data.ByteString.Char8 as BS8

socketFun :: String -> Int -> ParamWord -> IO Bool
socketFun host port pw = withSocketsDo $ do
                         addrInfo <- getAddrInfo Nothing (Just host) (Just $ show port)
                         let serverAddr = head addrInfo
                         sock <- socket (addrFamily serverAddr) Stream defaultProtocol
                         connect sock (addrAddress serverAddr)
                         let msg = BS8.pack (show pw ++ "\n")
                         send sock msg
                         rMsg <- recv sock 10
                         let res = BS8.unpack rMsg
                         sClose sock
                         return (case res of
                                  "true\n" -> True
                                  "false\n" -> False)

inferFun :: [ParamWord] -> (ParamWord -> Bool) -> Integer -> Integer -> IO (DFSM, [ParamWord])
inferFun otraces f = inferFunIO otraces (return . f)

inferFunIO :: [ParamWord] -> (ParamWord -> IO Bool) -> Integer -> Integer -> IO (DFSM, [ParamWord])
inferFunIO otraces f n le =
  do traces <- mapM (shorten f) otraces
     evaluate (rnf traces)
     result <- inferFunIOAux traces f n le
     print result
     return result

inferFunIOAux :: [ParamWord] -> (ParamWord -> IO Bool) -> Integer -> Integer -> IO (DFSM, [ParamWord])
inferFunIOAux traces f n le =
  do classTraces <- classify f traces
     evaluate (rnf traces)
     let dfsm = detParamInf classTraces
     evaluate (rnf dfsm)
     result <- inferFunIOStep dfsm traces f n le
     case result of
       Just (cex, traces) -> inferFunIOAux (cex:traces) f n le
       Nothing -> return (dfsm, traces)

inferFunIOStep :: DFSM -> [ParamWord] -> (ParamWord -> IO Bool) -> Integer -> Integer -> IO (Maybe (ParamWord, [ParamWord]))
inferFunIOStep dfsm traces f n le =
  do
--   visualise dfsm
     putStrLn "Looking for a counter example..."
     hFlush stdout
     bigResult <- findCounterExample f dfsm n le
     result <- case bigResult of
                 Just a -> do { sa <- shorten f a ; return (Just sa) }
                 Nothing -> return Nothing
     evaluate (rnf result)
     print result
     hFlush stdout
     putStrLn "Updating model..."
     hFlush stdout
     case result of
       Just cex -> return $ Just (cex, traces)
       Nothing -> return Nothing

classify f traces = classifyAux f traces ParamSample { posTraces = []
                                                     , negTraces = [] }

classifyAux f [] ps = return ps
classifyAux f (h:t) ps@(ParamSample { posTraces = pt
                                    , negTraces = nt }) =
  do res <- f h;
     classifyAux f t (if res
                      then (ps { posTraces = h:pt })
                      else (ps { negTraces = h:nt }))

findCounterExample f dfsm n le
  | n == 0 = return Nothing
  | otherwise = do case mod n 100 of
                     0 -> do { putStr "."; hFlush stdout}
                     _ -> return ()
                   (clas, word) <- evalRandIO $ randomTrace dfsm le
                   actualClas <- f word
                   let Just testedEval = acceptsTrace word dfsm
                   if actualClas == testedEval
                     then findCounterExample f dfsm (n - 1) le
                     else do { res <- shorten f word; return $ Just res } 

shorten f word =
 do res <- f subword
    if res
      then return word
      else shorten f subword
 where subword = init word

data FreqSrvState = FreqSrvState { allocated :: S.HashSet Integer
                                 , deallocated :: S.HashSet Integer 
                                 , lastAllocated :: Integer
                                 , running :: Bool }

emptyFreqSrvState :: FreqSrvState
emptyFreqSrvState = FreqSrvState { allocated = S.empty
                                 , deallocated = S.empty
                                 , lastAllocated = 10
                                 , running = False }

-- Door example
-- Examples:
-- NICE: [[PCall "genPersoOutside" [], PCall "genPersoInside" [], PCall "openDoor" [], PCall "goOut" [1], PCall "goIn" [0], PCall "goIn" [1], PCall "closeDoor" []]]
-- LESS NICE: [[PCall "genPersoOutside" [], PCall "genPersoInside" [], PCall "openDoor" [], PCall "goOut" [1], PCall "goIn" [0], PCall "goIn" [1], PCall "goOut" [0], PCall "closeDoor" []]]
-- CLEAR PROBLEM: [[PCall "genPersoOutside" [], PCall "genPersoInside" [], PCall "openDoor" [], PCall "goOut" [1], PCall "goIn" [0], PCall "goIn" [1], PCall "goOut" [1], PCall "goOut" [0], PCall "closeDoor" []]]

data DoorSt = DoorSt { doorOpen :: Bool
                     , peopleInside :: S.HashSet Integer
                     , peopleOutside :: S.HashSet Integer
                     , lastPersoGen :: Integer }

emptyDoorSt = DoorSt { doorOpen = False
                     , peopleInside = S.empty
                     , peopleOutside = S.empty
                     , lastPersoGen = 0 }

door :: ParamWord -> Bool
door lis = systemSim fsDoor 0 lis emptyDoorSt M.empty

fsDoor fss (fun, pars)
  | (fun == "genPersoOutside") && (lpars == 0) = let (np, nfss) = touchPerso fss in (Just np, outside np nfss)
  | (fun == "genPersoInside") && (lpars == 0) = let (np, nfss) = touchPerso fss in (Just np, inside np nfss)
  | (fun == "goOut") && doorOpen fss && (lpars == 1) && S.member par (peopleInside fss) = (Just 0, outside par (notInside par fss))
  | (fun == "goIn") && doorOpen fss && (lpars == 1) && S.member par (peopleOutside fss) = (Just 0, inside par (notOutside par fss))
  | (fun == "closeDoor") && doorOpen fss && (lpars == 0) = (Just 0, fss { doorOpen = False })
  | (fun == "openDoor") && not (doorOpen fss) && (lpars == 0) = (Just 0, fss { doorOpen = True })
  | otherwise = (Nothing, fss)
  where lpars = length pars
        [par] = pars

touchPerso ds@(DoorSt { lastPersoGen = n }) = (n + 1, ds { lastPersoGen = n + 1 })
inside p ds@(DoorSt { peopleInside = pi }) = ds { peopleInside = S.insert p pi }
notInside p ds@(DoorSt { peopleInside = pi }) = ds { peopleInside = S.delete p pi }
outside p ds@(DoorSt { peopleOutside = po }) = ds { peopleOutside = S.insert p po }
notOutside p ds@(DoorSt { peopleOutside = po }) = ds { peopleOutside = S.delete p po }


-- Freq Server Unique Total Limited

freqServerUTL :: Integer -> ParamWord -> Bool
freqServerUTL maxFreqs lis = systemSim (fsExecuteUTL maxFreqs) 0 lis emptyFreqSrvState M.empty

fsExecuteUTL :: Integer -> FreqSrvState -> (String, [Integer]) -> (Maybe Integer, FreqSrvState)
fsExecuteUTL maxFreqs fss (fun, pars)
  | (fun == "start") && (lpars == 0) && not (running fss) = (Just 0, fss { running = True })
  | (fun == "stop") && (lpars == 0) && running fss = (Just 0, fss { running = False })
  | (fun == "allocate") && (lpars == 0) && running fss && (numFreqs < maxFreqs) = getNewUniqueFreq fss
  | (fun == "deallocate") && (lpars == 1) && isAllocated pars fss && running fss = (Just 0, deallocate pars fss)
  | otherwise = (Nothing, fss)
  where lpars = length pars
        numFreqs = fromIntegral $ S.size (allocated fss)

-- Freq Server Unique Total
-- INTERESTING: [[PCall "start" [], PCall "allocate" [], PCall "deallocate" [1], PCall "deallocate" [1], PCall "stop" []], [PCall "start" [], PCall "allocate" [],PCall "deallocate" [1],PCall "allocate" [],PCall "deallocate" [3], PCall "stop" []]] 

freqServerUnique :: ParamWord -> Bool
freqServerUnique lis = systemSim fsExecuteU 0 lis emptyFreqSrvState M.empty

fsExecuteU :: FreqSrvState -> (String, [Integer]) -> (Maybe Integer, FreqSrvState)
fsExecuteU fss (fun, pars)
  | (fun == "start") && (lpars == 0) && not (running fss) = (Just 0, fss { running = True })
  | (fun == "stop") && (lpars == 0) && running fss = (Just 0, fss { running = False })
  | (fun == "allocate") && (lpars == 0) && running fss = getNewUniqueFreq fss
  | (fun == "deallocate") && (lpars == 1) && isAllocated pars fss && running fss = (Just 0, deallocate pars fss)
  | otherwise = (Nothing, fss)
  where lpars = length pars


-- Freq Server Unique Partial

freqServerUniqueP :: ParamWord -> Bool
freqServerUniqueP lis = systemSim fsExecuteUP 0 lis emptyFreqSrvState M.empty

fsExecuteUP :: FreqSrvState -> (String, [Integer]) -> (Maybe Integer, FreqSrvState)
fsExecuteUP fss (fun, pars)
  | (fun == "allocate") && (lpars == 0) = getNewUniqueFreq fss
  | (fun == "deallocate") && (lpars == 1) && isAllocated pars fss = (Just 0, deallocate pars fss)
  | otherwise = (Nothing, fss)
  where lpars = length pars
--
-- Freq Server Total
-- INTERESTING: [[PCall "start" [], PCall "allocate" [], PCall "deallocate" [1], PCall "deallocate" [1], PCall "stop" []], [PCall "start" [], PCall "allocate" [],PCall "deallocate" [1],PCall "allocate" [],PCall "deallocate" [3], PCall "stop" []]] 

freqServer :: ParamWord -> Bool
freqServer lis = systemSim fsExecuteT 0 lis emptyFreqSrvState M.empty

fsExecuteT :: FreqSrvState -> (String, [Integer]) -> (Maybe Integer, FreqSrvState)
fsExecuteT fss (fun, pars)
  | (fun == "start") && (lpars == 0) && not (running fss) = (Just 0, fss { running = True })
  | (fun == "stop") && (lpars == 0) && running fss = (Just 0, fss { running = False })
  | (fun == "allocate") && (lpars == 0) && running fss = getNewFreq fss
  | (fun == "deallocate") && (lpars == 1) && isAllocated pars fss && running fss = (Just 0, deallocate pars fss)
  | otherwise = (Nothing, fss)
  where lpars = length pars

-- Freq Server Parial

freqServerP :: ParamWord -> Bool
freqServerP lis = systemSim fsExecuteP 0 lis emptyFreqSrvState M.empty

fsExecuteP :: FreqSrvState -> (String, [Integer]) -> (Maybe Integer, FreqSrvState)
fsExecuteP fss (fun, pars)
  | (fun == "allocate") && (lpars == 0) = getNewFreq fss
  | (fun == "deallocate") && (lpars == 1) && isAllocated pars fss = (Just 0, deallocate pars fss)
  | otherwise = (Nothing, fss)
  where lpars = length pars

-- Generic

systemSim :: (a -> (String, [b]) -> (Maybe b, a))
                 -> Integer -> [ParamCall] -> a -> M.HashMap Integer b -> Bool
systemSim _ _ [] _ _ = True
systemSim fsFunc n (PCall fun pars:t) st ma =
     case res of
       Just val -> systemSim fsFunc (n + 1) t newSt (M.insert n val ma)
       Nothing -> False
  where (res, newSt) = fsFunc st (fun, [let Just a = M.lookup p ma in a | p <- pars])

-- FreqServerGeneric

isAllocated :: [Integer] -> FreqSrvState -> Bool
isAllocated [par] fs = S.member par (allocated fs)

deallocate :: [Integer] -> FreqSrvState -> FreqSrvState
deallocate [par] fs@(FreqSrvState { deallocated = s
                                  , allocated = a }) = fs { allocated = S.delete par a
                                                          , deallocated = S.insert par s }

getNewFreq :: FreqSrvState -> (Maybe Integer, FreqSrvState)
getNewFreq fs@(FreqSrvState { deallocated = s
                            , allocated = a
                            , lastAllocated = n }) =
                  if S.null s
                    then (Just n, fs { lastAllocated = n + 1
                                     , allocated = S.insert n a }) 
                    else let (m, ns) = sDeleteFindOne s in (Just m, fs { deallocated = ns
                                                                       , allocated = S.insert m a })

sDeleteFindOne s = let (h:_) = S.toList s in (h, S.delete h s)

getNewUniqueFreq fss = (Just lastAll, fss { lastAllocated = lastAll + 1
                                          , allocated = S.insert lastAll alloc })
  where lastAll = lastAllocated fss
        alloc = allocated fss

