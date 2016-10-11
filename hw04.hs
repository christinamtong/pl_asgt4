-- Homework 4.0: Parsing with Applicative
-- Due 2016-10-10

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Hw04 where

-- Charlie Watson, Christina Tong
-- Hw 4
-- Prof Greenberg

import Control.Applicative
import Data.Char

import qualified Data.Map as Map
import Data.Map (Map)

-- In this homework, you'll write some pretty-printers and parsers for
-- the While language of HW03.

type VarName = String

data AExp =
   Var VarName
   | Num Int
   | Plus AExp AExp
   | Times AExp AExp
   | Neg AExp
   | Div AExp AExp
 deriving Eq

data BExp =
   Bool Bool
   | Equal AExp AExp
   | Lt AExp AExp
   | Not BExp
   | Or BExp BExp
   | And BExp BExp
 deriving (Show, Eq)

data Stmt =
   Skip
   | Assign VarName AExp
   | Seq Stmt Stmt
   | If BExp Stmt Stmt
   | While BExp Stmt
 deriving (Show, Eq)


-- <h3>Problem 1: Pretty printing with `Show`</h3>

-- Write a `Show` instance for `AExp` that prints as few parentheses
-- as possible. That is, `show (Plus (Var "x") (Plus (Num 6) (Num 36)))`
-- should return `"x + 6 + 36"`, not `"x + (6 + 36)"`. Similarly, `show
-- (Plus (Num 5) (Times (Num 6) (Num 36)))` should return `5 + 6 * 36`,
-- because multiplication has a higher precedence than addition. But
-- `show (Times (Num 5) (Plus (Num 6) (Num 36)))` should return `"5 * (6
-- + 36)"`".

-- The trick is to have the pretty printer follow the structure of the
-- parser. There are two approaches: either take an extra integer
-- parameter and use it to determine what "level" you're at, or actually
-- write several functions (`showTerm`, `showFactor`, etc.).

instance Show AExp where
    show (Var a) = a
    show (Num a) = show a
    show (Plus a b) = showTerm (Plus a b)
    show (Div a b) = showFactor (Div a b)
    show (Times a b) = showFactor (Times a b)
    show (Neg a) = showNeg (Neg a)

showTerm (Plus a (Neg b)) = showFactor a ++ " - " ++ showTerm b
showTerm (Plus a b) = showFactor a ++ " + " ++ showTerm b
showTerm x = showFactor x

showFactor (Times a b) = showNeg a ++ " * " ++ showFactor b
showFactor (Div a b) = showNeg a ++ " / " ++ showFactor b
showFactor a = showNeg a

showNeg (Neg a) = "-" ++ showAtom a
showNeg a = showAtom a

showAtom (Num a) = show a
showAtom (Var a) = a
showAtom a = "(" ++ showTerm a ++ ")"

-- <h3>Problem 2: Parsing expressions</h3>

-- Problem 2 is long enough that I've marked the things you should do
-- with **HWHWHW**. I haven't done so for the other problems, which have
-- fewer parts.

-- A `Parser a` is a function that takes a `String` and may return an `a`
-- and a `String`. Intuitively, a Parser either (1) fails to parse, or
-- (2) parses part of the input (at type `a`) and has some remaining,
-- unparsed input.

newtype Parser a = Parser { parse :: String -> Maybe (a,String) }

-- We'll start out by defining a few necessary instances, but our goal
-- isn't to write `Parser (\s -> ...)` by hand: we'll construct a library
-- of *combinators* where we can build up parsers nicely.

-- But first, `Parser` is a functor: `fmap` applies to the parsed value.

instance Functor Parser where
    fmap f p = Parser $ \s -> (\(a,c) -> (f a, c)) <$> parse p s

-- `Parser` is also applicative: a pure `Parser` always succeeds, just
-- returning its input. The `(<*>)` (read: "ap") function takes an `f ::
-- Parser (a -> b)` and a `Parser a` and combines them: it first parses
-- `f` to get a function `g :: a -> b` and some remaining bit of string
-- to be parsed, `s'`. It then parses `s'` with `a :: Parser a`, making
-- sure to apply `g` to the result. (Note how we use `fmap` to concisely
-- say "apply `g` to the result of parsing with `a`.)

instance Applicative Parser where
    pure a = Parser $ \s -> Just (a,s)
    f <*> a = Parser $ \s ->
        case parse f s of
             Just (g,s') -> parse (fmap g a) s'
             Nothing -> Nothing

-- There's one last type class to define: `Alternative`, which is a
-- left-biased choice. In the `empty` case, we just return
-- `Nothing`. When considering two alternatives, we can take advantage of
-- the existing `Alternative` class for `Maybe`: try to parse the
-- left-hand side, and if that fails, try the right.

instance Alternative Parser where
   empty = Parser $ \s -> Nothing
   l <|> r = Parser $ \s -> parse l s <|> parse r s

-- Below we'll define a few "primitive" parsers, which explicitly write
-- parsing functions. Don't define any extra ones! All of your solutions
-- should use (a) these primitive parsers, (b)
-- Functor/Applicative/Alternative, and (c) other helpers/recursive
-- functions you define.

ensure :: (a -> Bool) -> Parser a -> Parser a
ensure p parser = Parser $ \s ->
    case parse parser s of
         Nothing -> Nothing
         Just (a,s') -> if p a then Just (a,s') else Nothing

lookahead :: Parser (Maybe Char)
lookahead = Parser f
    where f [] = Just (Nothing,[])
          f (c:s) = Just (Just c,c:s)

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser f
    where f [] = Nothing
          f (x:xs) = if p x then Just (x,xs) else Nothing

-- We can detect the end of the file manually...

eof :: Parser ()
eof = Parser $ \s -> if null s then Just ((),[]) else Nothing

-- ...but the other three primitive parsers are enough on their
-- own.

-- **HWHWHW** Write a function `eof'` which behaves like `eof` but is built up
-- from the other primitive parsers:

eof' :: Parser ()
eof' = (\s -> (())) <$> (ensure (\s -> s==Nothing) lookahead)

-- In general, we'll be careful to allow arbitrary whitespace at the
-- beginnings of what we parse.

ws :: Parser ()
ws = pure () <* many (satisfy isSpace)

char :: Char -> Parser Char
char c = ws *> satisfy (==c)

str :: String -> Parser String
str s = ws *> loop s
 where loop [] = pure []
       loop (c:cs) = (:) <$> satisfy (==c) <*> loop cs

-- We can define what it means to parse something in parentheses. Note
-- how we're careful to specify order of operations between `(*>)` and
-- `(<*)`---forgetting to do this can lead to some tricky bugs!

parens :: Parser a -> Parser a
parens p = (char '(' *> p) <* char ')'

-- Let's start our parser from the bottom up. We'll begin with a notion
-- of *keyword* a/k/a a *reserved word*. These are English words that
-- can't be used as variables because they'll be part of the concrete
-- syntax of our language.

keywords :: [String]
keywords = ["skip","if","then","else","while","true","false"]

isKeyword = (`elem` keywords)

-- To parse a keyword, we'll parse it as a string (using `str`) but make
-- sure that it it's a whole strong. For example, `parse (kw "repeat")
-- "repeat "` should return `Just ("repeat"," ")`, but `parse (kw
-- "repeat") "repeatable"` should return `Nothing`.

-- **HWHWHW** Write the that parses a keyword (you don't need to check
-- that the given string is in the list `keywords`).


kw :: String -> Parser String
kw s = ws *> ((str s) <* (ensure isNotAlphaNumeric lookahead))
   where isNotAlphaNumeric Nothing = True
         isNotAlphaNumeric (Just (c)) = not (isAlphaNum c)


-- **HWHWHW** Now let's parse variables. A variable is (1) a string
-- starting with an alphabetical character followed by zero or more
-- alphanumeric characters that (2) isn't a keyword.

var :: Parser String
var = ws *> (ensure (\s -> not (isKeyword s)) ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)))


-- A number is one or more digits. We can use `read :: Read a => String
-- -> a` to read out an Int, since a `Read Int` instance is defined in
-- the Prelude. Note that the type annotation here is critical, or
-- Haskell will complain---it doesn't know what you want to read!

num :: Parser Int
num = ws *> (read <$> some (satisfy isDigit))


-- **HWHWHW** Now define an `AExp` parser; call the top-level "terms"
-- `aexp`, but you can call the rest whatever you want. Feel free to
-- copy/paste most of it from lecture notes, but don't forget to add
-- division! Please also encode subtraction using addition and negation.

aexp, factor, neg, atom :: Parser AExp
aexp = Plus <$> factor <* plus <*> aexp
      <|> (\a b -> Plus a (Neg b)) <$> factor <* minus <*> aexp
      <|> factor
factor = Times <$> neg <* times <*> factor <|> neg
neg = Neg <$> (minus *> atom) <|> atom
atom = Num <$> num <|> (char '(' *> aexp <* char ')') <|> Var <$> var

plus, divide, minus, times :: Parser Char
plus = char '+'
divide = char '/'
minus = char '-'
times = char '*'


-- **HWHWHW** Now let's define a `BExp` parser; we'll have to use the
-- `aexp` parser. If you're unsure of which precedences to use here,
-- recall that in Boolean algebra, conjunction is multiplication and
-- disjunction is addition.

-- Your `bexp` parser should use the existing comparisons on `AExp`s to
-- encode all of the relevant comparisons. Here are some examples and
-- what they parse to; you don't have to parse *exactly* to what I do,
-- but you should parse to something equivalent. Use C-style syntax: and
-- is `&&`, or is `||`, and not is `!`. The constants can just use
-- lower-case names, like `true` and `false`.


bexp_encoding_test1 = "x == y" -- Equal (Var x) (Var y)
bexp_encoding_test2 = "x <= y" -- Or (Equal (Var x) (Var y)) (Lt (Var x) (Var y))
bexp_encoding_test3 = "x != y" -- Not (Equal (Var x)) (Var y)

bexp, factorB, notB, atomB :: Parser BExp
bexp = Or <$> factorB <* or' <*> bexp <|> factorB
factorB = And <$> notB <* and' <*> factorB <|> notB
notB = Not <$> (bang' *> atomB) <|> atomB
atomB = Bool <$> bool' <|> (char '(' *> bexp <* char ')')
      <|> Equal <$> aexp <* equal' <*> aexp
      <|> Not <$> (Equal <$> aexp <* nequal' <*> aexp)
      <|> Lt <$> aexp <* lt' <*> aexp
	    <|> (\x y -> (And (Not (Equal x y)) (Not (Lt x y)))) <$> aexp <* gt' <*> aexp
      <|> Not <$> (Lt <$> aexp <* geq' <*> aexp)
      <|> (\x y -> (Or (Equal x y) (Lt x y))) <$> aexp <* leq' <*> aexp

or', and', bang', equal', nequal', lt', gt', leq', geq' :: Parser String
or' = str "||"
and' = str "&&"
bang' = str "!"
equal' = str "=="
nequal' = str "!="
lt' = str "<"
gt' = str ">"
leq' = str "<="
geq' = str ">="

bool' :: Parser Bool
bool' = boolMap <$> (ws *> (str "true" <|> str "false"))
    where boolMap "true" = True
          boolMap _ = False

-- <h3>Problem 3: Parsing a la C</h3>

-- Now we can write a parser for statements. Let's use a C-like
-- syntax.

-- Your top-level parser should be called `cSyntax`. It's helpful to
-- think of a top-level program as being a sequence of one more
-- statements (in the concrete syntax, separated by `;`; in the abstract
-- syntax tree, joined by `Seq`).

-- Here are some example programs in the C syntax:

cProg1 = "x = 5; y = 6;"
cProg2 = "if (x == 0) { y = 10; } else { y = x; }"
cProg3 = "while (iffy > 10) { iffy = iffy - 1; };\n\nderp = 7;"
cProg4 = "while (true) {};"
cProg5 = "if (x==0) { y = 10;} else { }\ny = x + y;\n;x = 5;"

-- You'll *definitely* want to write more test programs. If you come up
-- with interesting corner cases, post them to Piazza! I want to
-- explicitly encourage collaboration on understanding the syntax (though
-- please write your own parsers within your pair).

-- what happens when you call two if's in a row? need a parser that is a sequence

cSyntax :: Parser Stmt
cSyntax = Seq <$> cSyntax <* semicolon' <*> cSyntax
    <|> If <$> (iff' *> lparen *> bexp <* rparen) <*> (lbrac *>
        (pure Skip <|> cSyntax) <* rbrac) <*> (else' *> lbrac *> (pure Skip <|> cSyntax) <* rbrac)
    <|> While <$> (while' *> lparen *> bexp <* rparen) <*> (lbrac *> (pure Skip <|> cSyntax) <* rbrac)
    <|> Assign <$> (var <* singleEqual') <*> (aexp <* semicolon')

semicolon', singleEqual', while', iff', else', lparen, rparen, lbrac, rbrac :: Parser String
lparen = str "("
rparen = str ")"
lbrac = str "{"
rbrac = str "}"
semicolon' = str ";"
singleEqual' = str "="
while' = str "while"
iff' = str "if"
else' = str "else"


-- Note: you will *not* be penalized for extra `Skip`s in your parsed
-- output. If inserting a `Skip` here or there makes your life easier, go
-- for it.

-- <h3>Problem 4: Parsing a la Python</h3>

-- Python's syntax is pleasantly spare, a nice example of
-- *whitespace-sensitive syntax*. (You may notice whitespace is
-- meaningful in Haskell's syntax, as well!) The idea is simple:
-- developers already use indentation to indicate, e.g., how nested you
-- are in loops. Why not make such indentation a requirement and reduce
-- the clutter from curly brackets?

-- Robust languages can infer the indentation level used on a per-program
-- or per-block basis, but let's fix the indentation level at two: every
-- time we open an if or while block, we'll indent the blocks by two more
-- spaces than we were.

-- Here's a sample program:

pyProg1 = "x = 5\ny = 6"

-- Oy---those newlines are going to get tiresome. There's a handy
-- function, `unlines`, which will let us write this a clearer way:

pyProg1' = unlines ["x = 5",
                   "y = 6"]

pyProg2 = unlines ["if x == 0:",
                  "  y = 10",
                  "else:",
                  "  y = x"]
pyProg3 = unlines ["while iffy > 10: ",
                  "  iffy = iffy - 1"]
pyProg4 = unlines ["while false:",
                  "  ",
                  "x = 0"]
pyProg5 = unlines ["while x > 0:",
                  "  while y < x:",
                  "    x = x - 1",
                  "    y = y + 1",
                  "  x = x - 1",
                  ""]

-- I've tried to cover the corner cases with these examples, but please
-- do discuss them. I'll try to settle any ambiguities that may arise.

-- Please write another parser for our language, but in the style of
-- Python. Your top-level parser of statements should be named
-- `pythonSyntax`:

pythonSyntax :: Parser Stmt
pythonSyntax = pythonParser 0

pythonParser :: Integer -> Parser Stmt
pythonParser lvl = Seq <$> ((pythonParser lvl) <* newline') <*> (pythonParser lvl)
    <|> If <$> (bexp <* colon' <* newline') <*> (pure Skip <|> pythonParser (lvl+1)) 
        <*> (else' *> colon' *> newline' *> (pythonParser (lvl+1)))
    <|> While <$> (bexp <* colon' <* newline') <*> (pure Skip <|> pythonParser (lvl+1))
    <|> Assign <$> ((ensureWS' lvl) *> var <* singleEqual') <*> (aexp <* newline')

-- data Stmt =
--    Skip
--  | Assign VarName AExp
--  | Seq Stmt Stmt
--  | If BExp Stmt Stmt
--  | While BExp Stmt
--  deriving (Show, Eq)


colon' :: Parser Char
colon' = char ':'

newline' :: Parser String
newline' = str "\n"

-- check that exactly correct amount of whitespace comes before the first character,
-- using helper function to accumulate requisite whitespace
ensureWS' :: Integer -> Parser String
ensureWS' level = ensure (\s -> s == (xWS level)) (many (satisfy isSpace)) <* (ensure isAlphaNumWrap lookahead)
    where xWS 0 = ""
          xWS l = "  " ++ xWS (l-1) 
          isAlphaNumWrap Nothing = False
          isAlphaNumWrap (Just c) = isAlphaNum c


-- when recurse, increment level by 2
-- before every statement make sure there is levels*2 space
-- catch 
-- skip is empty space?



-- You can largely follow the same idea as your C-style parser, but your
-- parsers for individual statements will need to keep track of the
-- current indentation level, e.g., by taking an integer
-- parameter. You'll need to be much more careful about whitespace in
-- general and newlines in particular. Writing a whitespace-sensitive
-- parser is hard. Let "testing" be your watchword!
