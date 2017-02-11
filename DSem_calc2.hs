-----------------------------------------------------------
--
-- Module      :  DSem_calc
-- APL Examples::
--   Calc -V3 
--     - with Store
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Expression Calculator:  (Watt, Ex. 3.2)	
--    From: ds_calc.ml	
-----------------------------------------------------------

module DSem_calc
( calcTests )
where

-- ---------- Abstract Syntax ---------- --
                        -- terminal nodes of the syntax --
type  Numeral = Int;

                        -- parsed phrases of the abstract syntax --
data Expression =
          Num    Numeral
        | Sumof  (Expression, Expression)
        | Subof  (Expression, Expression)
        | Prodof (Expression, Expression)
          deriving Show

data Command =
           Equal   Expression             -- "=" means evaluate!
         | Save    Expression Register
         | Seq     Command Command

-- ---------- Semantic Domains ---------- --
type  Integer = Int;

data Register =  X   |  Y
data Location = Loc1 | Loc2    -- named storage locations
                deriving Eq

data  Value   =
           IntValue    Int
         | Truthvalue  Bool
         | Null
           deriving Show

-- ---------- Semantic Functions ---------- --
valuation :: Int        -> Value
evaluate  :: Expression -> Store -> Value
execute   :: Command    -> Store -> Value

-- ---------- Auxiliary Semantic Functions ---------- --
add   :: (Int, Int) -> Int
diff  :: (Int, Int) -> Int
prod  :: (Int, Int) -> Int

add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

getInt :: Value -> Int
getInt (IntValue x) = x

-- -----------------------------
-- Storage: { X, Y }
type Store = Location -> Value

-- null = integer(0)
empty_store :: Store
empty_store   Loc1 = Null      -- fixed size store
empty_store   Loc2 = Null
-- empty_store    _   = Null       --  (* fail *)

update :: (Store, Location, Value) -> Store
update (sto, loc, v) =  \id -> if id==loc
                               then v else sto loc

fetch :: (Store, Location) -> Value
fetch  (sto, loc)  =  sto loc

-- ---------- Semantic Equations ---------- --

                               -- from integer to Value --
valuation ( n ) = IntValue(n)

evaluate ( Sumof (e1,e2) ) sto =
        let i1 = getInt (evaluate e1 sto)
            i2 = getInt (evaluate e2 sto)
        in  IntValue( add(i1,i2) )

evaluate ( Subof (e1,e2) ) sto =
        let i1 = getInt (evaluate e1 sto)
            i2 = getInt (evaluate e2 sto)
        in  IntValue( diff(i1,i2) )

evaluate ( Prodof(e1,e2) ) sto =
        let i1 = getInt (evaluate e1 sto)
            i2 = getInt (evaluate e2 sto)
        in  IntValue( prod(i1,i2) )

evaluate ( Num(n) ) sto = valuation(n)

execute ( Equal(e)) sto = evaluate e sto

-- ============================== --
-- ========== Test it! ========== --
-- print "----------  Test";
e1 = Num(2)
e2 = Sumof(Num(1),Num(2))

s1 = update (empty_store, Loc1, IntValue 1)
v1 = evaluate e1 s1
v2 = evaluate e2 s1

v3 = evaluate (Sumof(Num(1), Prodof(Num(2),Num(3)))) s1

c1 = Equal(e1)
c2 = Equal(e2)
v4 = execute c1 s1
v5 = execute c2 s1

calcTests = do print "------ APL: Calculator DSem"
               print [ v1, v2, v3, v4, v5 ]