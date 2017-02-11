
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
          -- deriving Show
        
data Command =
            Expreq  Expression  -- "=" means evaluate!
            |Productof (Expression,Expression)  -- = Product
-- ---------- Semantic Domains ---------- --
type  Integer = Int;

data  Value   =
            IntValue    Int
          | Truthvalue  Bool
          deriving Show

-- ---------- Semantic Functions ---------- --
valuation :: Int        -> Value
evaluate  :: Expression -> Value
execute   :: Command    -> Value

-- ---------- Auxiliary Semantic Functions ---------- --
add   :: (Int, Int) -> Int
diff  :: (Int, Int) -> Int
prod  :: (Int, Int) -> Int

add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

getInt :: Value -> Int
getInt (IntValue x) = x

-- ---------- Semantic Equations ---------- --

                -- from integer to Value --
valuation ( n ) = IntValue(n)

evaluate ( Sumof (e1,e2) ) =
        let i1 = getInt (evaluate e1)
            i2 = getInt (evaluate e2)
        in  IntValue( add(i1,i2) )

evaluate ( Subof (e1,e2) ) =
        let i1 = getInt (evaluate e1)
            i2 = getInt (evaluate e2)
        in  IntValue( diff(i1,i2) )

evaluate ( Prodof(e1,e2) ) =
        let i1 = getInt (evaluate e1)
            i2 = getInt (evaluate e2)
        in  IntValue( prod(i1,i2) )

evaluate ( Num(n) ) = valuation(n)

execute ( Expreq(e)  )  =
        evaluate e
        
execute (Productof(e1,e2)) = evaluate (Prodof(e1,e2))

-- ============================== --
-- ========== Test it! ========== --
-- print "----------  Test";
e1 = Num(2)
e2 = Sumof(Num(1),Num(2))
v1 = evaluate e1
v2 = evaluate e2

v3 = evaluate (Sumof(Num(1), Prodof(Num(2),Num(3))))

c1 = Expreq(e1)
c2 = Expreq(e2)
v4 = execute c1
v5 = execute c2
c6 = Productof(e1,e2)
v6 = execute c6
calcTests = do print "------ APL: Calculator DSem"
               print [ v1, v2, v3, v4, v5, v6 ]

