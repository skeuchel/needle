
module Coq.StdLib where

import Coq.Syntax

plus :: Term -> Term -> Term
plus a b = TermApp (TermQualId (Ident $ ID "plus")) [a,b]

eq :: Term -> Term -> Term
eq = TermEq

nat :: Term
nat = TermQualId (Ident $ ID "nat")

list :: Term -> Term
list t = TermApp (TermQualId (Ident $ ID "list")) [t]

cons :: Term -> Term -> Term
cons a b = TermApp (TermQualId (Ident $ ID "cons")) [a,b]

all :: Terms -> Term
all = TermAnd

prop :: Terms -> Term
prop = foldr TermFunction (TermSort Prop)

relation :: Terms -> Term -> Term
relation ts t = foldr TermFunction t ts

termZero :: Term
termZero = TermNum 0

termOne :: Term
termOne = TermNum 1

termIdent :: String -> Term
termIdent = TermQualId . Ident . ID

underscore :: Term
underscore = termIdent "_"

eqRefl :: Term
eqRefl = termIdent "eq_refl"

eqSym :: Term -> Term
eqSym p = TermApp (termIdent "eq_sym") [p]

eqTrans :: Term -> Term -> Term
eqTrans p q = TermApp (termIdent "eq_trans") [p,q]

eqFEqual :: Term -> Term -> Term
eqFEqual f p = TermApp (termIdent "f_equal") [f,p]

eqFEqual2 :: Term -> Term -> Term -> Term
eqFEqual2 f p q = TermApp (termIdent "f_equal2") [f,p,q]

eqFEqual3 :: Term -> Term -> Term -> Term -> Term
eqFEqual3 f p q r = TermApp (termIdent "f_equal3") [f,p,q,r]

eqFEqualn :: Term -> [Term] -> Term
eqFEqualn f as
  | n == 0     = eqRefl
  | n == 1     = TermApp (termIdent $ "f_equal") (f:as)
  | otherwise  = TermApp (termIdent $ "f_equal" ++ show n) (f:as)
  where n   = length as

sumbool :: Term -> Term -> Term
sumbool l r = TermApp (termIdent "sumbool") [l, r]

not :: Term -> Term
not tm = TermApp (termIdent "not") [tm]

false :: Term
false = termIdent "False"

true :: Term
true = termIdent "True"
