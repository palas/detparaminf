module DetParamInf.DFSMVisualise(visualise, visualiseNoNeg, renderToFile) where

import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph
import Data.GraphViz.Attributes.Colors (Color(..), toColorList)
import Data.GraphViz.Attributes.Complete(Attribute(..),Label(StrLabel), noMods, ArrowShape(..), ArrowType(..))
import Data.GraphViz
import Data.Text.Lazy (pack)
import Data.List
import DetParamInf.AptaTree


data DNode = DStartNode | DBadState | DOneOf Integer | DFun String Integer
  deriving (Eq, Show, Ord)
instance Labellable DNode where
  toLabelValue x = StrLabel (pack $ show x)
data DTran = DControlSta | DControl | DDep ParamPos Integer
  deriving (Eq, Show, Ord)
instance Labellable DTran where
  toLabelValue x = StrLabel (pack $ show x)

mybrown :: Color
mybrown = RGB {red = 153, green = 51, blue = 0}

myblue :: Color
myblue = RGB {red = 0, green = 0, blue = 153}

myyellow :: Color
myyellow = RGB {red = 204, green = 205, blue = 0}

myred :: Color
myred = RGB {red = 204, green = 0, blue = 0}

visualise :: DFSM -> IO ()
visualise dfsm = runGraphvizCanvas' (graphToDot ncp $ toGr dfsm) Xlib

renderToFile :: FilePath -> DFSM -> IO FilePath
renderToFile path dfsm = runGraphvizCommand Dot (graphToDot ncp $ toGr dfsm) DotOutput path

visualiseNoNeg :: DFSM -> IO ()
visualiseNoNeg dfsm = visualise (remNeg dfsm)

remNeg dfsm = dfsm { transitions = [ t | t@(_,_,b) <- transitions dfsm , b /= BadState ] }

ncp :: GraphvizParams Int DNode DTran () DNode
ncp = nonClusteredParams { fmtNode = \(_, n) -> decorateNode n
                         , fmtEdge = \(_, _, e) -> decorateEdge e }

decorateEdge :: DTran -> Attributes
decorateEdge (DControl) = [ Label $ StrLabel $ pack ""
                          , Color $ toColorList [mybrown] ]
decorateEdge (DControlSta) = [ Label $ StrLabel $ pack ""
                             , Color $ toColorList [mybrown]
                             , ArrowHead $ AType [(noMods, NoArrow)]]
decorateEdge (DDep ppos int) = [ Label $ StrLabel $ pack $ show ppos ++ "\nas\nparam: " ++ show int ]

decorateNode :: DNode -> Attributes
decorateNode (DOneOf int) = [ Label $ StrLabel $ pack (show int)
                            , Color $ toColorList [myblue]
                            , Shape DiamondShape]
decorateNode (DStartNode) = [ Label $ StrLabel $ pack "START"
                            , Color $ toColorList [myyellow]
                            , Shape Star]
decorateNode (DBadState) = [ Label $ StrLabel $ pack "ERROR!"
                           , Color $ toColorList [myred]
                           , Peripheries 2
                           , Shape Pentagon ]
decorateNode (DFun str int) = [ Label $ StrLabel $ pack $ str ++ " ( ... )"
                              , Color $ toColorList [mybrown] ]

toGr :: DFSM -> Gr DNode DTran
toGr dfsm = genGraph (transitions dfsm)

genGraph :: Graph gr => [(NodeId, Transition, NodeId)] -> gr DNode DTran
genGraph tran = mkGraph (nub (getStates tran)) (nub (getTransitions tran))

getStates :: [(NodeId, Transition, NodeId)] -> [(Int, DNode)]
getStates [] = []
getStates ((is, tran, es):t) = translateNode is:translateNode es:translateTran tran:getStates t

getTransitions :: [(NodeId, Transition, NodeId)] -> [(Int, Int, DTran)]
getTransitions [] = []
getTransitions ((is, tran, es):t) = controlsta tis ttran:control ttran tes:(dep tran ++ getTransitions t)
  where (tis, _) = translateNode is
        (ttran, _) = translateTran tran
        (tes, _) = translateNode es

translateNode :: NodeId -> (Int, DNode)
translateNode InitialState = (0, DStartNode)
translateNode BadState = (-1, DBadState)
translateNode (NId n) = (fromIntegral n, DOneOf n)

translateTran :: Transition -> (Int, DNode)
translateTran tr = ((-1) - fromIntegral (transitionId tr), DFun (funName tr) (genericLength (params tr)))

dep :: Transition -> [(Int, Int, DTran)]
dep tr = concat [[((-1) - fromIntegral (srcTransition psrc), (-1) - fromIntegral dtid, DDep (srcParamPos psrc) n) | psrc <- psrcs] | (n, psrcs) <- p]
  where dtid = transitionId tr
        p = zip [0..] (params tr)
controlsta st en = (st, en, DControlSta)
control st en = (st, en, DControl)

