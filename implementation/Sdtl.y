{
module Sdtl where
import Data.Char
import Control.Monad.State
import Data.Map

}

%name sdtl
%tokentype { Token }

%token
	if			{TokenIf}
	else		{TokenElse}
	while		{TokenWhile}
	input		{TokenInput}
	output		{TokenOutput}
	new			{TokenNew}
	this		{TokenThis}
	function	{TokenFunction}
	return		{TokenReturn}
	true		{TokenTrue}
	false		{TokenFalse}
	global		{TokenGlobal}
	try 		{TokenTry}
	catch 		{TokenCatch}
	throw  		{TokenThrow}
	id			{TokenId $$}
	'='			{TokenAsg}
	'+'			{TokenPlus}
	'-'			{TokenMinus}
	'*'			{TokenMult}
	'/'			{TokenDiv}
	gt			{TokenGreaterThan}
	lt			{TokenLessThan}
	eq			{TokenEqual}
	'('			{TokenLP}
	')'			{TokenRP}
	'{'			{TokenLC}
	'}'			{TokenRC}
	';'			{TokenScol}
	'.'			{TokenDot}
	','			{TokenComma}
	number		{TokenNumber $$}


%nonassoc gt lt eq
%left '+' '-'
%left '*' '/'

%monad {P}

%%


Program :: { SdtlProgram }
Program : Stmts {% state $ \(s0, m0) -> (SdtlProgram $1 m0, (s0,m0)) }

Stmts :: { AStmt }
Stmts : Stmts AStmt {% augStmt $ Stmts $1 $2}
	  | {% augStmt Empty}

AStmt :: { AStmt }
ASTmt : Stmt {% augStmt $1}      

Cblock :: { AStmt }
Cblock : '{' Stmts '}' { $2 }
	   | Stmt {% augStmt $1 }

Stmt :: {Stmt}
Stmt : AExpr ';' {Expr $1}
	 | Lexpr '=' AExpr ';' {Asg $1 $3}
	 | if '(' AExpr ')' Cblock else Cblock {Ite $3 $5 $7}
	 | if '(' AExpr ')' Cblock {If $3 $5}
	 | while '(' AExpr ')' Cblock {While $3 $5}
	 | output AExpr ';' {Output $2}
	 | return AExpr ';' {Return $2}
	 | function id '(' Idlist ')' Cblock {Function $2 $4 $6}
	 | try Cblock catch '(' id ')' Cblock {TryCatch $2 $5 $7}
	 | throw AExpr ';' {Throw $2}

Params :: {[AExpr]}
Params : {[]}
	   | AExpr {[$1]}
	   | AExpr ',' Params {$1:$3}

Idlist :: {[String]}
Idlist : {[]}
	   | id {[$1]}
	   | id ',' Idlist {$1:$3}

AExpr :: {AExpr}
AExpr : Expr {% augExpr $1}

Expr :: {Expr}
Expr : Lexpr {Lexpr $1}
	 | true {Boolean True}
	 | false {Boolean False}
	 | number {Number $1}
	 | AExpr '+' AExpr {Binop Plus $1 $3}
	 | AExpr '-' AExpr {Binop Minus $1 $3}
	 | AExpr '*' AExpr {Binop Mult $1 $3}
	 | AExpr '/' AExpr {Binop Div $1 $3}
	 | AExpr gt AExpr {Binop GreaterThan $1 $3}
	 | AExpr lt AExpr {Binop LessThan $1 $3}
	 | AExpr eq AExpr {Binop Equal $1 $3}
	 | input {Input}
	 | new AExpr {New $2}
	 | Lexpr '(' Params ')' {Call $1 $3}
	 | '(' Expr ')' {$2}
	 | this {This}
	 | global {Global}
Lexpr :: {Lexpr}
Lexpr : '(' Lexpr ')' {$2}
	  | AExpr '.' id {Ref $1 $3}
	  | id {Id $1}
{

type Sid = Int
type Eid = Int

data SdtlProgram = SdtlProgram AStmt (Map Int AStmt) deriving (Show)

data Lexpr = 
	Ref AExpr String
	| Id String
	deriving Show

data Op = Plus | Minus | Mult | Div | GreaterThan | LessThan | Equal
	deriving Show

data AExpr = AExpr Expr Eid deriving Show

data Expr =
	Lexpr Lexpr
	| Boolean Bool
	| Number Int
	| Binop Op AExpr AExpr
	| Input
	| New AExpr
	| Call Lexpr [AExpr]
	| This
	| Global
	deriving Show

data AStmt = 
	AStmt Stmt Sid 
	deriving Show

data Stmt =
	Asg Lexpr AExpr
	| Ite AExpr AStmt AStmt
	| If AExpr AStmt
	| While AExpr AStmt
	| Output AExpr
	| Expr AExpr
	| Return AExpr
	| Function String [String] AStmt
	| TryCatch AStmt String AStmt
	| Empty
	| Stmts AStmt AStmt
	| Throw AExpr
	deriving Show

data Token =
	TokenIf
	| TokenElse
	| TokenWhile
	| TokenInput
	| TokenOutput
	| TokenNew
	| TokenThis
	| TokenFunction
	| TokenReturn
	| TokenTrue
	| TokenFalse
	| TokenGlobal
	| TokenId String
	| TokenAsg
	| TokenPlus
	| TokenMinus
	| TokenMult
	| TokenDiv
	| TokenGreaterThan
	| TokenLessThan
	| TokenEqual
	| TokenLP
	| TokenRP
	| TokenLC
	| TokenRC
	| TokenScol
	| TokenDot
	| TokenComma
	| TokenNumber Int
	| TokenTry
	| TokenCatch
	| TokenThrow
	deriving Show

type P = State (Int, Map Int AStmt)

augStmt :: Stmt -> P AStmt
augStmt s = state $ \(s0, m0) -> let news = AStmt s s0 in (news, (s0+1, insert s0 news m0 ))

augExpr :: Expr -> P AExpr
augExpr e = state $ \(s0, m0) -> (AExpr e s0, (s0+1, m0))

lexer :: String -> [Token]
lexer s = lexer1 s

lexer1 :: String -> [Token]

lexer1 [] = []
lexer1 (c:cs)
	| isSpace c = lexer1 cs
	| c == '\t' = lexer1 cs
	| c == '\r' = lexer1 cs
	| c == '\n' = lexer1 cs
	| isAlpha c = lexVar (c:cs)
	| isDigit c = lexNum (c:cs)
	| c == '#' = lexer1 (dropWhile (/= '\n') cs)

lexer1 ('=':cs) = 
	case cs of
		('=':ss) -> TokenEqual : lexer1 ss
		_ -> TokenAsg : lexer1 cs

lexer1 ('+':cs) = TokenPlus : lexer1 cs
lexer1 ('-':cs) = TokenMinus : lexer1 cs
lexer1 ('*':cs) = TokenMult : lexer1 cs
lexer1 ('/':cs) = TokenDiv : lexer1 cs
lexer1 ('(':cs) = TokenLP : lexer1 cs
lexer1 (')':cs) = TokenRP : lexer1 cs
lexer1 ('{':cs) = TokenLC : lexer1 cs
lexer1 ('}':cs) = TokenRC : lexer1 cs
lexer1 ('.':cs) = TokenDot : lexer1 cs
lexer1 (';':cs) = TokenScol : lexer1 cs
lexer1 ('>':cs) = TokenGreaterThan : lexer1 cs
lexer1 ('<':cs) = TokenLessThan : lexer1 cs
lexer1 (',':cs) = TokenComma : lexer1 cs

lexNum cs = TokenNumber (read num) : lexer1 rest 
	where (num,rest) = span isDigit cs

lexVar cs =
	case span isAlphaNum cs of
		("if", rest) -> TokenIf : lexer1 rest 
		("else", rest) -> TokenElse : lexer1 rest
		("while", rest) -> TokenWhile : lexer1 rest
		("input", rest) -> TokenInput : lexer1 rest
		("output", rest) -> TokenOutput : lexer1 rest
		("new", rest) -> TokenNew : lexer1 rest
		("this", rest) -> TokenThis : lexer1 rest
		("function", rest) -> TokenFunction : lexer1 rest
		("return", rest) -> TokenReturn : lexer1 rest
		("true", rest) -> TokenTrue : lexer1 rest
		("false", rest) -> TokenFalse : lexer1 rest
		("global", rest) -> TokenGlobal : lexer1 rest
		("try", rest) -> TokenTry : lexer1 rest
		("catch", rest) -> TokenCatch : lexer1 rest
		("throw", rest) -> TokenThrow : lexer1 rest
		(var, rest) -> TokenId var : lexer1 rest

happyError :: [Token] -> a
happyError _ = error "Parse error"
}