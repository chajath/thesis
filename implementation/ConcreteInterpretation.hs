{-# LANGUAGE MagicHash, UnboxedTuples, GADTs, MultiParamTypeClasses #-}

module Main (main, runString) where

import SemanticFunctions
import Sdtl
import Data.Map
import qualified Control.Exception as E
import GHC.IO
import GHC.Exts
import System.Environment
import qualified Control.Monad.State as S
import System.IO.Unsafe
import Data.ByteString.Internal
import Debug.Trace
{-
fromState :: State# RealWorld -> RealWorld
fromState = unsafeCoerce#

toState :: RealWorld -> State# RealWorld
toState = unsafeCoerce#

execIO :: IO a -> RealWorld -> (RealWorld, a)
execIO (IO k) = \w -> case k (toState w) of (# s', x #) -> (fromState s', x)
-}

data CValue = Intval Int
            | Boolval Bool
            | FunPointer Sid [CValue]
            | Object Int
            deriving (Show, Eq)

instance Value CValue where
	conval (Boolean True) = Boolval True
	conval (Boolean False) = Boolval False
	conval (Number i) = Intval i
	getSid (FunPointer n []) = n
	binop Plus (Intval i1) (Intval i2) = Intval $ i1 + i2
	binop Minus (Intval i1) (Intval i2) = Intval $ i1 - i2
	binop Mult (Intval i1) (Intval i2) = Intval $ i1 * i2
	binop Div (Intval i1) (Intval i2) = Intval $ i1 `div` i2
	binop GreaterThan (Intval i1) (Intval i2) = Boolval $ i1 > i2
	binop LessThan (Intval i1) (Intval i2) = Boolval $ i1 < i2
	binop Equal (Intval i1) (Intval i2) = Boolval $ i1 == i2
	
data CState = CState{
		env :: Map String CValue,
		--io :: RealWorld,
		objmem :: Map Int (Map String CValue),
		returning :: Maybe CValue,
		exception :: Maybe CValue,
		this :: CValue,
		functions :: Map Sid [String]
	} deriving (Show)

instance Eq CState where
	(==) _ _ = False

instance State (CState) where
	esc (CState {returning = v, exception = e}) = case v of
		Nothing -> case e of 
			Nothing -> False
			_ -> True
		_ -> True
	
	--fundecl :: String -> [String] -> Sid -> s -> [s]
	fundecl fnname fnparams n s = 
		[s {functions = insert n fnparams (functions s), 
		    env = insert fnname (FunPointer n []) (env s) }]
instance StateValue CState CValue where
	ret v s = trace (show s) $ [s {returning = Just v}]

	--cond :: (CValue v) => v -> (M s v a) -> (M s v a) -> (M s v a)
	cond (Boolval True) t u = t
	cond _ t u = u

	--asg :: (CValue v) => String -> v -> s -> [s]
	asg i v s = [s {env = (insert i v (env s))}]

	--dooutput :: (CValue v) => v -> s -> [s]
	dooutput (Intval n) s =
		--let (io1, _) = (execIO $ putStrLn (show n)) (io s)
		--in [s {io = io1}]
		let v = ($!) inlinePerformIO $ putStrLn (show n) in
		if v == () then [s] else [s]
	
	--getinput :: (CValue v) => s -> [(s,v)]
	getinput s =
		--let (io1, v) = (execIO $ getLine) (io s)
		--in [(s {io = io1}, Intval (read v))]
		[(s,Intval (read (inlinePerformIO $ getLine)))]

	--val :: (CValue v) => s -> String -> v
	val s i = (env s) ! i

	--enter :: (CValue v) => s -> Sid -> [v] -> s
	enter s n vs t = 
		let params = (functions s) ! n
		in s {env = fromList (zip params vs), this = t}

	--leave :: (CValue v) => s -> s -> (s, Maybe v)
	leave s0 s = trace (show s) $ 
		(CState {env = (env s0), {-io = (io s), -} 
			     returning = Nothing,
			     exception = (exception s),
			     objmem = (objmem s),
			     this = (this s0),
			     functions = (functions s)}, (returning s))

	fix x = x (fix x)

	apply (FunPointer n c) p t _ =
		M $ \f -> \s -> 
			if length ((functions s) ! n) == (length (c ++ p)) 
				then let (M tcall) = call n (c ++ p) t in (tcall f s)
				else [(s, Just (FunPointer n (c++p)))]

	set (Object n) id1 v = \s -> 
		let oldo = (objmem s) ! n
		in [s {objmem = insert n (insert id1 v oldo) (objmem s)}]

	get (Object n) id1 = \s -> (objmem s) ! n ! id1
	
	getglobal = \s -> (Object 0)
	getthis = \s -> (this s)
	newobj _ = M $ \f -> \s -> 
		let newn = size (objmem s)
		in 
		traceShow (Object newn) $
		[(s {objmem = insert newn (fromList []) (objmem s)}, Just (Object newn))]

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


fun :: (StateValue s v) => (Map Int AStmt) -> Int -> (M s v ())
fun sidMap sid = trace ("call sid " ++ (show sid)) $ 
	let Just fbody = Data.Map.lookup sid sidMap in 
	sstmt fbody

runConcrete :: SdtlProgram -> IO ()
runConcrete (SdtlProgram (AStmt _ mainSid) sdtlMap) = do
	--putStrLn $ show mainSid
	putStrLn $ show sdtlMap
	--w <- getWorld
	let [endState] = 
		runMonad (fun sdtlMap mainSid) 
				 (fun sdtlMap)
		         (CState {env = fromList [], {-io = w, -} returning = Nothing, exception = Nothing,
		         		  functions = fromList [], objmem = fromList [(0, fromList [])], this = (Object 0)}) 
		         (Intval 0)
		in do
		--putWorld (io endState)
		putStrLn $ show (env endState)

runString :: String -> IO()
runString program = runConcrete (fst (S.runState (sdtl (lexer program)) (1, fromList [])))

main = do
	(sdtlfile:_) <- getArgs
	program <- readFile sdtlfile
	runString program