{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main, runString) where

import SemanticFunctions
import Sdtl
import Data.Map
import qualified Control.Exception as E
import System.Environment
import Data.ByteString.Internal
import Debug.Trace
import qualified Control.Monad.State as S
import qualified Data.List as L

data AValue = Intval
            | Boolval
            | FunPointer Sid Int Eid
            | Object Int
            | Undecided
            deriving (Show, Eq, Ord)

instance Value AValue where
    conval (Boolean True) = Boolval
    conval (Boolean False) = Boolval
    conval (Number i) = Intval
    getSid (FunPointer n _ _) = n
    getSid Undecided = -1
    binop Plus (Intval) (Intval) = Intval
    binop Minus (Intval) (Intval) = Intval
    binop Mult (Intval) (Intval) = Intval
    binop Div (Intval) (Intval) = Intval
    binop GreaterThan (Intval) (Intval) = Boolval
    binop LessThan (Intval) (Intval) = Boolval
    binop Equal (Intval) (Intval) = Boolval
    binop _ Undecided _ = Undecided
    binop _ _ Undecided = Undecided
    
data AState = AState{
        env :: Map String AValue,
        returning :: Maybe AValue,
        exception :: Maybe AValue,
        functions :: Map Sid [String],
        objmem :: Map Eid (Map String AValue),
        this :: AValue,
        curried :: Map (Sid, Int, Eid) [AValue]
    } deriving (Show, Eq, Ord)

instance State (AState) where
    esc (AState {returning = v, exception = e}) = case v of
        Nothing -> case e of 
            Nothing -> False
            _ -> True
        _ -> True
    
    --fundecl :: String -> [String] -> Sid -> s -> [s]
    fundecl fnname fnparams n s = 
        [s {functions = insert n fnparams (functions s), 
            env = insert fnname (FunPointer n 0 0) (env s) }]

y x = x (y x)
mapToMonad m = M $ \f -> \s -> if member s m then (m ! s) else [(s, Just ())]

instance StateValue AState AValue where
    fix x = M $ \f -> \s ->
        let (fixedMap) = 
                (y $ \x0 -> \m0 -> 
                    let (M t1) = (x (mapToMonad m0))
                        newmap = traceShow m0 $ union m0 $ fromList [(s1,t1 f s1) | s1 <- (L.map fst (L.nub $ concat $ elems m0)) ++ [s] ]
                    in
                    if m0 == newmap then newmap else x0 newmap) (fromList [])
        in
            trace ("final " ++ (show fixedMap)) $
                L.nub $ concat $ elems fixedMap

    ret v s = trace (show s) $ [s {returning = Just v}]

    --cond :: (CValue v) => v -> (M s v a) -> (M s v a) -> (M s v a)
    cond (Boolval) (M t) (M u) = M $ \f -> \s0 ->
        let s1 = t f s0
            s2 = u f s0
        in L.nub $ s1 ++ s2
    --cond _ t u = u

    --asg :: (CValue v) => String -> v -> s -> [s]
    asg i v s = [s {env = (insert i v (env s))}]

    --dooutput :: (CValue v) => v -> s -> [s]
    dooutput _ s = [s]

    --getinput :: (CValue v) => s -> [(s,v)]
    getinput s =
        [(s,Intval)]

    --val :: (CValue v) => s -> String -> v
    val s i = (env s) ! i

    --enter :: (CValue v) => s -> Sid -> [v] -> s
    enter s n vs t = 
        let params = (functions s) ! n
        in s {env = fromList (zip params vs), this = t}

    --leave :: (CValue v) => s -> s -> (s, Maybe v)
    leave s0 s = trace (show s) $ 
        (AState {env = (env s0), returning = Nothing, exception = (exception s), 
                 functions = (functions s), 
                curried = (curried s),
                objmem = (objmem s),
                this = (this s0)}, (returning s))

    apply (FunPointer n c ce) p t e =
        M $ \f -> \s ->
            let cv=if c > 0 then ((curried s) ! (n, c, ce)) else [] in
                if length ((functions s) ! n) == c + (length p) 
                    then let (M tcall) = (call n (cv ++ p) t) in (tcall f s)
                    else 
                        [(s {curried = insert (n, (c + length p), e)  (cv ++ p) (curried s)}
                            , Just (FunPointer n (c+(length p)) e))]

    set (Object n) id1 v = \s -> 
        let oldo = (objmem s) ! n
        in [s {objmem = insert n (insert id1 v oldo) (objmem s)}]

    get (Object n) id1 = \s -> (objmem s) ! n ! id1
    
    getglobal = \s -> (Object 0)
    getthis = \s -> (this s)
    newobj eid = M $ \f -> \s -> 
        [(s {objmem = insert eid (fromList []) (objmem s)}, Just (Object eid))]

    --runthrow :: v -> s -> [s]
    runthrow v = \s -> [s {exception=Just v}]

    --runcatch :: String -> (M s v ()) -> (M s v ())
    runcatch id1 (M u) = M $ \f -> \s0 ->
        case (exception s0) of
            Nothing -> [(s0, Just ())]
            Just v -> (u f (s0 {env = insert id1 v (env s0), exception=Nothing}))
{-
getWorld :: IO RealWorld
getWorld = IO (\s -> (# s, fromState s #))

putWorld :: RealWorld -> IO ()
putWorld s' = IO (\_ -> (# toState s', () #))
-}


fun :: (Map Int AStmt) -> (Map (Int,AState) [(AState, Maybe ())]) -> Int -> (M AState AValue ())
fun sidMap fapprox sid = trace ("call sid " ++ (show sid)) $ 
    let Just fbody = Data.Map.lookup sid sidMap in 
    (M $ \f -> \s -> 
            if member (sid, s) fapprox then fapprox ! (sid, s)
                else  
                (y $ \localx -> \prevresult ->
                    let 
                        newapprox = (insert (sid, s) prevresult fapprox)
                        M t = (sstmt fbody)
                        result = t (fun sidMap newapprox) s
                    in
                        if result == prevresult then result
                        else localx result) [(s {returning = Just Undecided}, Just ())])

runAbstract :: SdtlProgram -> IO ()
runAbstract (SdtlProgram (AStmt _ mainSid) sdtlMap) = do
    --putStrLn $ show mainSid
    putStrLn $ show sdtlMap
    --w <- getWorld
    let endStates = 
            runMonad (fun sdtlMap (fromList []) mainSid) 
                     (fun sdtlMap (fromList []))
                     (AState {env = fromList [], 
                              returning = Nothing,
                              exception = Nothing,
                              functions = fromList [], 
                              curried = fromList [],
                              objmem = fromList [(0, fromList [])],
                              this = (Object 0)}) 
                     (Intval)
        in do
        --putWorld (io endState)
        putStrLn "Final States"
        putStrLn $ show endStates

runString :: String -> IO()
runString program = runAbstract (fst (S.runState (sdtl (lexer program)) (1, fromList [])))

main = do
    (sdtlfile:_) <- getArgs
    program <- readFile sdtlfile
    runString program
