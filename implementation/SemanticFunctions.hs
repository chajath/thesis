{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
module SemanticFunctions where
import Data.Maybe as Maybe
import Sdtl
import Data.Map as Map
import Debug.Trace

class (Eq v) => Value v where
	conval :: Expr -> v
	getSid :: v -> Sid
	binop :: Op -> v -> v -> v
class (Eq s) => State s where
	fundecl :: String -> [String] -> Sid -> s -> [s]
	esc	:: s -> Bool
	
class (State s, Value v) => StateValue s v where
	ret :: v -> s -> [s]
	cond :: (Eq a) => v -> (M s v a) -> (M s v a) -> (M s v a)
	asg :: String -> v -> s -> [s]
	dooutput :: v -> s -> [s]
	getinput :: s -> [(s,v)]
	val :: s -> String -> v
	enter :: s -> Sid -> [v] -> v -> s
	leave :: s -> s -> (s, Maybe v)
	fix :: ((M s v ()) -> (M s v ())) -> M s v ()
	apply :: v -> [v] -> v -> Eid -> (M s v v)
	set :: v -> String -> v -> s -> [s]
	get :: v -> String -> s -> v
	getglobal :: s -> v
	getthis :: s -> v
	newobj :: Eid -> (M s v v)
	runthrow :: v -> s -> [s]
	runcatch :: String -> (M s v ()) -> (M s v ())
data M s v a where
	M :: (State s, Value v) => ((Sid -> (M s v ())) -> s -> [(s,Maybe a)]) -> M s v a

--data (State s) => M s a = M (F s -> s -> [(s,Maybe a)])

instance (StateValue s v) => Monad (M s v) where
	(M t) >>= u = 
		M $ (\f -> \s0 -> 
			let ss = t f s0
			in
			   concat [ if esc s1 then [(s1, Nothing)]
			   	            	  else let 
			   	            	      Just a' = a
			   	            	      (M us) = u a'
			   	            	      in us f s1
			   	      | (s1, a) <- ss ])
	return a = M $ \f -> \s0 -> [(s0, Just a)]

(>>>) :: (StateValue s v) => (M s v a) -> (M s v a) -> (M s v a)
(M t) >>> (M u) = M $ (\f -> \s0 -> 
	let ss = t f s0 in concat [ u f s1 | (s1, a) <- ss ])
					   

{- Takes a state transformer and transforms into a monad -}
liftS :: (StateValue s v) => (s -> [s]) -> M s v ()
liftS strans = M $ \f -> \s0 -> [(s1,Just ()) | s1 <- (strans s0)]

liftV :: (State s, Value v) => (s -> v) -> M s v v
liftV stov = M $ \f -> \s -> [(s, Just (stov s))]

getState :: (State s, Value v) => M s v s
getState = M $ \f -> \s0 -> [(s0,Just s0)]

sstmt :: (StateValue s v) => AStmt -> M s v ()
sstmt (AStmt Empty sid) = return ()
sstmt (AStmt (Stmts s1 s2) sid)  = do 
	traceShow s1 $ sstmt s1
	traceShow s2 $ sstmt s2
sstmt (AStmt (Expr e1) sid) = do
	sexpr e1
	return ()
sstmt (AStmt (Return e1) sid) = do
	v <- sexpr e1
	liftS $ ret v
sstmt (AStmt (If e1 s1) sid) = do
	v <- sexpr e1
	cond v (sstmt s1) (return ())
sstmt (AStmt (Ite e1 s1 s2) sid) = do
	v <- sexpr e1
	cond v (sstmt s1) (sstmt s2)
sstmt (AStmt (Asg (Id i1) e1) sid) = do
	v <- sexpr e1
	liftS $ asg i1 v
sstmt (AStmt (While e1 s1) sid) = fix $ \x -> do
	v <- sexpr e1
	cond v (sstmt s1 >> x) (return ())
sstmt (AStmt (Output e1) sid) = do
	v <- sexpr e1
	liftS $ dooutput v
sstmt (AStmt (Function id1 ids (AStmt _ s1)) sid) = liftS $ fundecl id1 ids s1
sstmt (AStmt (Asg (Ref e1 id1) e2) sid) = do
	r <- sexpr e1
	v <- sexpr e2
	liftS $ set r id1 v
sstmt (AStmt (TryCatch s1 id1 s2) sid) =
	(sstmt s1) >>> runcatch id1 (sstmt s2)
sstmt (AStmt (Throw e1) sid) = do
	v1 <- sexpr e1
	liftS $ runthrow v1

sexpr :: (StateValue s v) => AExpr -> M s v v
sexpr (AExpr (Number n) eid) = return $ conval (Number n)
sexpr (AExpr (Boolean b) eid) = return $ conval (Boolean b)
sexpr (AExpr (Lexpr l1) eid) = slexpr l1
sexpr (AExpr Input eid) = M $ \f -> \s0 -> [(s, Just v) | (s,v) <- getinput s0]
sexpr (AExpr (Call (Ref e1 id1) es) eid) = do
	t <- sexpr e1
	n <- liftV $ get t id1
	p <- evalParams es []
	apply n p t eid
sexpr (AExpr (Call l1 es) eid) = do
	n <- slexpr l1
	p <- evalParams es []
	t <- liftV $ getthis
	apply n p t eid
sexpr (AExpr (Binop op e1 e2) eid) = do
	v1 <- sexpr e1
	v2 <- sexpr e2
	return $ binop op v1 v2
sexpr (AExpr This eid) = liftV $ getthis
sexpr (AExpr Global eid) = liftV $ getglobal
sexpr (AExpr (New (AExpr (Call l1 es) eid1)) eid) = do
	n <- slexpr l1
	p <- evalParams es []
	m <- newobj eid
	apply n p m eid
	return m
evalParams :: (StateValue s v) => [AExpr] -> [v] -> M s v [v]
evalParams [] vs = return vs
evalParams (e:es) vs = do
	v <- sexpr e
	evalParams es (vs ++ [v])

slexpr :: (StateValue s v) => Lexpr -> M s v v
slexpr (Id id1) = do
	s0 <- getState 
	return $ val s0 id1
slexpr (Ref e1 id1) = do
	v <- sexpr e1
	liftV $ get v id1
putState :: (StateValue s v) => s -> (M s v ())
putState s = M $ \f -> \s0 -> [(s,Just ())]

getFunc :: (StateValue s v) => M s v (Sid -> (M s v ()))
getFunc = M $ \f -> \s -> [(s, Just f)]

call :: (StateValue s v) => Sid -> [v] -> v -> (M s v v)
call n p t = M $ \f -> \s0 -> [leave s0 s | (s,_) <- let M x = (f n) in x f (enter s0 n p t) ]

runMonad :: (StateValue s v) => (M s v a) -> (Sid -> (M s v ())) -> s -> v -> [s]
runMonad (M t) = \f -> \s0 -> \_ -> (Prelude.map) fst (t f s0)